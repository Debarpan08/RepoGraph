from __future__ import annotations

import ast
import json
import os
import re
import sys
import threading
import urllib.error
import urllib.parse
import urllib.request
import zipfile
from collections import Counter, defaultdict
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from io import BytesIO
from math import log, sqrt
from pathlib import PurePosixPath
from typing import Any

from falkordb import FalkorDB

# Auto-load .env if present
env_path = os.path.join(os.path.dirname(__file__), ".env")
if os.path.exists(env_path):
    with open(env_path, "r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if line and not line.startswith("#") and "=" in line:
                k, v = line.split("=", 1)
                os.environ.setdefault(k.strip(), v.strip().strip("'\""))

GRAPH_NAME = os.getenv("FALKORDB_GRAPH", "repograph")
MAX_ARCHIVE_BYTES = 30 * 1024 * 1024
MAX_SOURCE_BYTES = 8 * 1024 * 1024
MAX_SOURCE_FILES = 800
SKIP_PARTS = {".git", "node_modules", "vendor", "dist", "build", ".venv", "venv", "__pycache__"}
RELATION_TYPES = {"CONTAINS", "DEFINES", "CALLS", "IMPORTS", "DEPENDS_ON", "USES"}
SOURCE_SUFFIXES = {
	".py", ".pyi", ".js", ".jsx", ".mjs", ".cjs", ".ts", ".tsx", ".java", ".go",
	".rs", ".rb", ".php", ".cs", ".kt", ".swift", ".scala", ".sql", ".yaml", ".yml",
	".toml", ".xml", ".json", ".md", ".html", ".css", ".sh",
}
DATABASE_PATTERNS = {
	"MongoDB": r"\b(mongodb|mongoose|pymongo|motor)\b",
	"PostgreSQL": r"\b(postgresql|postgres|psycopg|pgvector)\b",
	"MySQL": r"\b(mysql|pymysql|sequelize\.mysql)\b",
	"Redis": r"\b(redis|ioredis)\b",
	"SQLite": r"\b(sqlite|sqlite3)\b",
	"DynamoDB": r"\b(dynamodb|boto3\.resource\(['\"]dynamodb)\b",
	"FalkorDB": r"\b(falkordb|graph\.query)\b",
}


def _node(nodes: dict[str, dict[str, Any]], key: str, name: str, kind: str,
		  repository: str, **properties: Any) -> str:
	nodes[key] = {"key": key, "name": name, "kind": kind, "repository": repository, **properties}
	return key


def _package_name(name: str) -> str:
	return re.split(r"[<>=!~\[]", name.strip(), maxsplit=1)[0].strip().lower()


def parse_repository(owner: str, repo: str, files: dict[str, str]) -> tuple[list[dict[str, Any]], list[tuple[str, str, str]]]:
	"""Build a compact code and dependency graph from decoded repository files."""
	repository = f"{owner}/{repo}"
	nodes: dict[str, dict[str, Any]] = {}
	edges: set[tuple[str, str, str]] = set()
	repo_key = _node(nodes, f"repo:{repository}", repository, "repository", repository)
	file_keys: dict[str, str] = {}
	symbols: list[dict[str, str]] = []
	pending_calls: list[tuple[str, str]] = []
	pending_imports: list[tuple[str, str]] = []

	def add_symbol(path: str, name: str, kind: str) -> str:
		key = f"{repository}:{path}::{name}"
		symbols.append({"key": key, "name": name, "path": path, "kind": kind})
		return _node(nodes, key, name, kind, repository, path=path)

	for path, content in files.items():
		normalized = str(PurePosixPath(path))
		file_key = f"{repository}:{normalized}"
		file_keys[normalized] = _node(
			nodes, file_key, PurePosixPath(normalized).name, "file", repository,
			path=normalized, content=content[:12000],
		)
		edges.add((repo_key, "CONTAINS", file_key))

		if PurePosixPath(normalized).name.lower() in {"readme.md", "readme.rst", "readme.txt"}:
			readme_key = _node(nodes, f"{file_key}:readme", "README", "documentation", repository,
							   path=normalized, content=content[:12000])
			edges.add((file_key, "CONTAINS", readme_key))

		if normalized.endswith(".py"):
			try:
				tree = ast.parse(content)
			except SyntaxError:
				tree = None
			if tree is not None:
				class Visitor(ast.NodeVisitor):
					def __init__(self) -> None:
						self.scope: list[str] = []
						self.current: list[str] = []

					def _visit_scope(self, node: ast.FunctionDef | ast.AsyncFunctionDef | ast.ClassDef,
									 kind: str) -> None:
						qualified = ".".join([*self.scope, node.name])
						symbol_key = add_symbol(normalized, qualified, kind)
						edges.add((file_key, "DEFINES", symbol_key))
						self.scope.append(node.name)
						self.current.append(symbol_key)
						self.generic_visit(node)
						self.current.pop()
						self.scope.pop()

					def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
						self._visit_scope(node, "function")

					def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef) -> None:
						self._visit_scope(node, "function")

					def visit_ClassDef(self, node: ast.ClassDef) -> None:
						self._visit_scope(node, "class")

					def visit_Call(self, node: ast.Call) -> None:
						if self.current:
							called = node.func.id if isinstance(node.func, ast.Name) else (
								node.func.attr if isinstance(node.func, ast.Attribute) else ""
							)
							if called:
								pending_calls.append((self.current[-1], called))
						self.generic_visit(node)

					def visit_Import(self, node: ast.Import) -> None:
						for alias in node.names:
							pending_imports.append((file_key, alias.name.split(".")[0]))

					def visit_ImportFrom(self, node: ast.ImportFrom) -> None:
						if node.module:
							pending_imports.append((file_key, node.module.split(".")[0]))

				Visitor().visit(tree)

		elif PurePosixPath(normalized).suffix.lower() in {".js", ".jsx", ".mjs", ".cjs", ".ts", ".tsx"}:
			declarations = list(re.finditer(
				r"(?m)^\s*(?:export\s+)?(?:default\s+)?(?:async\s+)?"
				r"(?:function|class|const|let|var)\s+([A-Za-z_$][\w$]*)", content
			))
			for index, declaration in enumerate(declarations):
				name = declaration.group(1)
				kind = "component" if name[:1].isupper() and PurePosixPath(normalized).suffix.lower() in {".jsx", ".tsx"} else "function"
				symbol_key = add_symbol(normalized, name, kind)
				edges.add((file_key, "DEFINES", symbol_key))
				end = declarations[index + 1].start() if index + 1 < len(declarations) else len(content)
				body = content[declaration.start():end]
				for called in re.findall(r"\b([A-Za-z_$][\w$]*)\s*\(", body):
					if called != name:
						pending_calls.append((symbol_key, called))
			for imported in re.findall(r"(?:from\s*|import\s*\()['\"]([^'\"]+)['\"]", content):
				pending_imports.append((file_key, imported))

		for database, pattern in DATABASE_PATTERNS.items():
			if re.search(pattern, content, re.IGNORECASE):
				db_key = _node(nodes, f"database:{repository}:{database}", database, "database", repository)
				edges.add((file_key, "USES", db_key))

	symbol_by_name: dict[str, list[str]] = defaultdict(list)
	for symbol in symbols:
		symbol_by_name[symbol["name"].split(".")[-1]].append(symbol["key"])
	for source, called in pending_calls:
		targets = symbol_by_name.get(called, [])
		if targets:
			edges.add((source, "CALLS", targets[0]))

	basename_to_file = {PurePosixPath(path).stem: key for path, key in file_keys.items()}
	for source, imported in pending_imports:
		local_name = imported.removeprefix(".").split("/")[-1].split(".")[-1]
		candidates = [basename_to_file.get(local_name), basename_to_file.get(local_name.lower())]
		target = next((candidate for candidate in candidates if candidate), None)
		if target and source != target:
			edges.add((source, "IMPORTS", target))
		elif imported and not imported.startswith((".", "/")):
			package_name = imported.split("/")[0].split(".")[0]
			package_key = _node(nodes, f"package:{package_name}", package_name, "package", repository)
			edges.add((source, "DEPENDS_ON", package_key))

	for path, content in files.items():
		lower_path = PurePosixPath(path).name.lower()
		dependencies: dict[str, str] = {}
		if lower_path == "package.json":
			try:
				manifest = json.loads(content)
				for section in ("dependencies", "devDependencies", "peerDependencies"):
					dependencies.update(manifest.get(section, {}))
			except (ValueError, AttributeError):
				pass
		elif lower_path in {"requirements.txt", "requirements-dev.txt"}:
			for line in content.splitlines():
				line = line.split("#", 1)[0].strip()
				match = re.match(r"([A-Za-z0-9_.-]+)", line)
				if match:
					dependencies[match.group(1)] = ""
		elif lower_path == "pyproject.toml":
			for name in re.findall(r"(?m)^\s*[\"']?([A-Za-z0-9_.-]+)[\"']?\s*=\s*[\"']", content):
				if name.lower() not in {"name", "version", "description", "requires-python", "build-backend"}:
					dependencies[name] = ""
		elif lower_path == "go.mod":
			dependencies.update({name: "" for name in re.findall(r"(?m)^\s*([\w./-]+)\s+v[\w.+-]+", content)})

		manifest_key = file_keys.get(path)
		for dependency in dependencies:
			package = _package_name(dependency)
			if not package:
				continue
			package_key = _node(nodes, f"package:{repository}:{package}", package, "package", repository)
			if manifest_key:
				edges.add((manifest_key, "DEPENDS_ON", package_key))

	return list(nodes.values()), sorted(edges)


def _decode_repository_url(url: str) -> tuple[str, str]:
	parsed = urllib.parse.urlparse(url.strip())
	if parsed.scheme != "https" or parsed.hostname not in {"github.com", "www.github.com"}:
		raise ValueError("Enter a public GitHub repository URL using https://github.com/owner/repository.")
	parts = [part for part in parsed.path.strip("/").split("/") if part]
	if len(parts) < 2 or parts[0].startswith("-"):
		raise ValueError("The GitHub URL must include an owner and repository name.")
	return parts[0], re.sub(r"\.git$", "", parts[1])


def fetch_repository(owner: str, repo: str) -> dict[str, str]:
	url = f"https://api.github.com/repos/{urllib.parse.quote(owner)}/{urllib.parse.quote(repo)}/zipball"
	headers = {"User-Agent": "RepoGraph/1.0", "Accept": "application/vnd.github+json"}
	if token := os.getenv("GITHUB_TOKEN"):
		headers["Authorization"] = f"Bearer {token}"
	request = urllib.request.Request(url, headers=headers)
	try:
		with urllib.request.urlopen(request, timeout=30) as response:
			archive = response.read(MAX_ARCHIVE_BYTES + 1)
	except urllib.error.HTTPError as error:
		if error.code == 404:
			raise ValueError("GitHub could not find that repository, or it is private. Set GITHUB_TOKEN for private repositories.") from error
		raise ValueError(f"GitHub returned HTTP {error.code} while downloading the repository.") from error
	except (urllib.error.URLError, TimeoutError) as error:
		raise ValueError(f"Could not download the repository: {error.reason if hasattr(error, 'reason') else error}") from error
	if len(archive) > MAX_ARCHIVE_BYTES:
		raise ValueError("The repository archive exceeds the 30 MB download limit.")

	files: dict[str, str] = {}
	total_bytes = 0
	try:
		with zipfile.ZipFile(BytesIO(archive)) as bundle:
			for member in bundle.infolist():
				path = PurePosixPath(member.filename)
				if len(path.parts) < 2 or any(part in SKIP_PARTS for part in path.parts):
					continue
				relative = "/".join(path.parts[1:])
				if not relative or path.is_absolute() or ".." in path.parts:
					continue
				if path.suffix.lower() not in SOURCE_SUFFIXES and path.name.lower() not in {"dockerfile", "makefile"}:
					continue
				if member.is_dir() or member.file_size > 400_000:
					continue
				if len(files) >= MAX_SOURCE_FILES or total_bytes + member.file_size > MAX_SOURCE_BYTES:
					break
				try:
					content = bundle.read(member).decode("utf-8")
				except (UnicodeDecodeError, OSError, zipfile.BadZipFile):
					continue
				files[relative] = content
				total_bytes += member.file_size
	except zipfile.BadZipFile as error:
		raise ValueError("GitHub returned an invalid repository archive.") from error
	if not files:
		raise ValueError("No supported source or documentation files were found in the repository.")
	return files


def _get_graph():
	db = FalkorDB(
		host=os.getenv("FALKORDB_HOST", "localhost"),
		port=int(os.getenv("FALKORDB_PORT", "6379")),
		password=os.getenv("FALKORDB_PASSWORD") or None,
	)
	return db.select_graph(GRAPH_NAME)


def store_repository(graph: Any, repository: str, nodes: list[dict[str, Any]],
					 edges: list[tuple[str, str, str]]) -> None:
	graph.query(
		"MATCH (n:RepoGraphEntity {repository: $repository}) DETACH DELETE n",
		{"repository": repository},
	)
	for start in range(0, len(nodes), 100):
		graph.query(
			"UNWIND $rows AS row "
			"MERGE (n:RepoGraphEntity {key: row.key}) "
			"SET n.name = row.name, n.kind = row.kind, n.repository = row.repository, "
			"n.path = row.path, n.content = row.content",
			{"rows": nodes[start:start + 100]},
		)
	grouped: dict[str, list[dict[str, str]]] = defaultdict(list)
	for source, relation, target in edges:
		if relation in RELATION_TYPES:
			grouped[relation].append({"source": source, "target": target})
	for relation, rows in grouped.items():
		for start in range(0, len(rows), 200):
			graph.query(
				f"UNWIND $rows AS row "
				"MATCH (a:RepoGraphEntity {key: row.source}), (b:RepoGraphEntity {key: row.target}) "
				f"MERGE (a)-[:{relation}]->(b)",
				{"rows": rows[start:start + 200]},
			)


def _tokens(text: str) -> set[str]:
	split_camel = re.sub(r"([a-z])([A-Z])", r"\1 \2", text)
	return {word.lower() for word in re.findall(r"[A-Za-z][A-Za-z0-9_]{1,}", split_camel)}


def _question_context(graph: Any, repository: str, question: str) -> tuple[list[dict[str, Any]], list[str], str]:
	result = graph.query(
		"MATCH (n:RepoGraphEntity {repository: $repository}) "
		"RETURN n.key, n.name, n.kind, n.path, n.content",
		{"repository": repository},
	)
	entities = []
	for row in result.result_set:
		entities.append(dict(zip(("key", "name", "kind", "path", "content"), row)))
	query_terms = _tokens(question)
	document_terms = [
		Counter(_tokens(" ".join(str(entity.get(field) or "") for field in ("name", "path", "content"))))
		for entity in entities
	]
	document_frequency: Counter[str] = Counter()
	for terms in document_terms:
		document_frequency.update(terms.keys())
	inverse_frequency = {
		term: log((len(entities) + 1) / (frequency + 1)) + 1
		for term, frequency in document_frequency.items()
	}
	query_weights = {term: log((len(entities) + 1) / (1 + sum(
		term in terms for terms in document_terms
	))) + 1 for term in query_terms}
	query_norm = sqrt(sum(weight * weight for weight in query_weights.values())) or 1
	ranked: list[tuple[float, dict[str, Any]]] = []
	for entity, terms in zip(entities, document_terms):
		name_terms = _tokens(str(entity.get("name") or ""))
		path_terms = _tokens(str(entity.get("path") or ""))
		content_terms = _tokens(str(entity.get("content") or ""))
		overlap = query_terms & (name_terms | path_terms | content_terms)
		document_norm = sqrt(sum((frequency * inverse_frequency[term]) ** 2 for term, frequency in terms.items())) or 1
		vector_score = sum(
			terms[term] * inverse_frequency[term] * query_weights[term]
			for term in query_terms & terms.keys()
		) / (document_norm * query_norm)
		score = vector_score * 10 + len(overlap) + 3 * len(query_terms & name_terms) + 2 * len(query_terms & path_terms)
		if entity.get("kind") in {"function", "class", "component"}:
			score += 1
		if score:
			ranked.append((score, entity))
	ranked.sort(key=lambda item: (item[0], item[1].get("kind") == "file"), reverse=True)
	matches = [entity for _, entity in ranked[:12]]
	keys = [entity["key"] for entity in matches if entity.get("key")]

	relation_lines: list[str] = []
	if keys:
		related = graph.query(
			"MATCH (a:RepoGraphEntity)-[r]->(b:RepoGraphEntity) "
			"WHERE a.key IN $keys OR b.key IN $keys "
			"RETURN a.name, a.kind, type(r), b.name, b.kind, a.path, b.path LIMIT 80",
			{"keys": keys},
		)
		for row in related.result_set:
			left, _, relation, right, _, left_path, right_path = row
			relation_lines.append(f"{left} --{relation.lower()}--> {right} ({left_path or right_path or 'repository graph'})")

	impact = re.search(r"(?:remove|delete|break|impact|depend(?:s|ency|encies)? on)\s+(?:the\s+)?[`'\"]?([A-Za-z_$][\w$./\\-]*)", question, re.IGNORECASE)
	impact_lines: list[str] = []
	if impact:
		target_name = impact.group(1).replace("\\", "/").strip("/").lower()
		file_targets = [
			entity for entity in entities
			if entity.get("kind") == "file"
			and (
				str(entity.get("name", "")).lower() == target_name
				or str(entity.get("path", "")).replace("\\", "/").strip("/").lower() == target_name
			)
		]
		targets = file_targets or [
			entity for entity in entities
			if entity.get("kind") in {"function", "class", "component"}
			and str(entity.get("name", "")).lower() == target_name
		]
		for target in targets[:6]:
			impact_lines.append(f"Target: {target['name']} in {target.get('path') or 'unknown file'}")
			affected_keys = [target["key"]]
			if target.get("kind") == "file":
				defined = graph.query(
					"MATCH (file:RepoGraphEntity {key: $key})-[:DEFINES]->(symbol:RepoGraphEntity) "
					"RETURN symbol.key LIMIT 100",
					{"key": target["key"]},
				)
				affected_keys.extend(row[0] for row in defined.result_set)
			seen_dependents: set[tuple[str, str, str]] = set()
			for affected_key in affected_keys:
				dependents = graph.query(
					"MATCH (source:RepoGraphEntity)-[rels*1..5]->(target:RepoGraphEntity {key: $key}) "
					"RETURN source.name, source.kind, source.path, length(rels) LIMIT 30",
					{"key": affected_key},
				)
				for row in dependents.result_set:
					name, kind, path, hops = row
					if kind == "repository" or path == target.get("path"):
						continue
					identity = (str(name), str(kind), str(path or ""))
					if identity in seen_dependents:
						continue
					seen_dependents.add(identity)
					impact_lines.append(
						f"Dependent: {name} ({kind}) in {path or 'unknown file'}, {hops} relationship hop(s) away"
					)

	excerpts: list[str] = []
	for entity in matches:
		content = entity.get("content")
		if not content:
			continue
		lines = [line.strip() for line in str(content).splitlines() if line.strip()]
		relevant = [line for line in lines if query_terms & _tokens(line)]
		sample = relevant[:5] or lines[:3]
		if sample:
			excerpts.append(f"{entity.get('path') or entity.get('name')}:\n" + "\n".join(sample))
	evidence = "\n\n".join((impact_lines[:30] or relation_lines[:35]) + excerpts[:8])
	citations = list(dict.fromkeys(str(entity.get("path") or entity.get("name")) for entity in matches))
	return matches, citations, evidence


def answer_question(graph: Any, repository: str, question: str) -> dict[str, Any]:
	matches, citations, context = _question_context(graph, repository, question)
	if not matches:
		return {"answer": "I couldn't find a matching symbol or source file in the analyzed repository. Try a class, service, database, or feature name.", "sources": []}

	api_key = os.getenv("GEMINI_API_KEY")
	if api_key:
		base_url = os.getenv("GEMINI_BASE_URL", "https://generativelanguage.googleapis.com/v1beta").rstrip("/")
		model = urllib.parse.quote(os.getenv("GEMINI_MODEL", "gemini-3-flash-preview"), safe="")
		payload = json.dumps({
			"systemInstruction": {"parts": [{"text": "You are RepoGraph, a codebase analyst. Answer only from the supplied repository evidence. Distinguish graph-proven relationships from source-text clues, state uncertainty, and cite file paths inline."}]},
			"contents": [{"role": "user", "parts": [{
				"text": f"Repository: {repository}\nQuestion: {question}\n\nGraph and source evidence:\n{context[:18000]}"
			}]}],
			"generationConfig": {"temperature": 0.2},
		}).encode()
		request = urllib.request.Request(
			f"{base_url}/models/{model}:generateContent", data=payload,
			headers={"x-goog-api-key": api_key, "Content-Type": "application/json"}, method="POST",
		)
		try:
			with urllib.request.urlopen(request, timeout=45) as response:
				result = json.loads(response.read())
			parts = result.get("candidates", [])[0].get("content", {}).get("parts", [])
			answer = "\n".join(part["text"] for part in parts if part.get("text"))
			if not answer:
				raise ValueError("Gemini returned no text content.")
			return {"answer": answer, "sources": citations}
		except (urllib.error.URLError, urllib.error.HTTPError, KeyError, IndexError, TypeError, ValueError, TimeoutError):
			pass

	impact_match = re.search(r"(?:remove|delete|break|impact|depend(?:s|ency|encies)? on)\s+(?:the\s+)?[`'\"]?([A-Za-z_$][\w$.-]*)", question, re.IGNORECASE)
	if impact_match:
		impact_evidence = [line for line in context.splitlines() if line.startswith(("Target:", "Dependent:"))]
		answer = "Impact analysis from recorded graph paths:\n" + (
			"\n".join(impact_evidence) if impact_evidence else "No incoming dependency paths were found for that symbol."
		)
		if "Dependent:" not in answer:
			answer += "\nNo callers or dependents were found. This is limited to relationships the parser could resolve."
	else:
		answer = "Repository evidence matching your question:\n" + context[:5000]
		if not context:
			answer += "No source excerpts or direct relationships matched; try a more specific symbol or technology name."
		answer += "\n\n" + (
			"Gemini did not return an answer; showing repository evidence instead. Check GEMINI_API_KEY and GEMINI_MODEL."
			if api_key else "Set GEMINI_API_KEY to enable synthesized natural-language answers."
		)
	return {"answer": answer, "sources": citations}


def _graph_snapshot(graph: Any, repository: str) -> dict[str, Any]:
	result = graph.query(
		"MATCH (n:RepoGraphEntity {repository: $repository}) "
		"RETURN n.key, n.name, n.kind, n.path",
		{"repository": repository},
	)
	nodes = [dict(zip(("key", "name", "kind", "path"), row)) for row in result.result_set]
	counts = Counter(node["kind"] for node in nodes)
	if nodes:
		relationships = graph.query(
			"MATCH (a:RepoGraphEntity {repository: $repository})-[r]->(b:RepoGraphEntity {repository: $repository}) "
			"RETURN a.key, b.key, type(r) LIMIT 600",
			{"repository": repository},
		)
		edges = [{"source": row[0], "target": row[1], "kind": row[2]} for row in relationships.result_set]
	else:
		edges = []
	return {"repository": repository, "nodes": nodes[:100], "edges": edges, "counts": dict(counts)}


class RepoGraphHandler(BaseHTTPRequestHandler):
	def log_message(self, format: str, *args: Any) -> None:
		print(f"{self.log_date_time_string()} {format % args}")

	def _json(self, status: int, body: dict[str, Any]) -> None:
		raw = json.dumps(body).encode("utf-8")
		self.send_response(status)
		self.send_header("Content-Type", "application/json; charset=utf-8")
		self.send_header("Content-Length", str(len(raw)))
		self.send_header("Access-Control-Allow-Origin", "*")
		self.end_headers()
		self.wfile.write(raw)

	def do_GET(self) -> None:
		path = urllib.parse.urlparse(self.path).path
		if path == "/":
			try:
				with open(os.path.join(os.path.dirname(__file__), "index.html"), "rb") as page:
					body = page.read()
				self.send_response(200)
				self.send_header("Content-Type", "text/html; charset=utf-8")
				self.send_header("Content-Length", str(len(body)))
				self.end_headers()
				self.wfile.write(body)
			except OSError:
				self._json(500, {"error": "index.html is missing"})
		elif path == "/api/health":
			try:
				_get_graph().query("RETURN 1")
				self._json(200, {"database": "connected", "llm": bool(os.getenv("GEMINI_API_KEY"))})
			except Exception as error:
				self._json(503, {"database": "disconnected", "error": str(error)})
		elif path == "/api/repository":
			repository = urllib.parse.parse_qs(urllib.parse.urlparse(self.path).query).get("name", [""])[0]
			try:
				self._json(200, _graph_snapshot(_get_graph(), repository))
			except Exception as error:
				self._json(500, {"error": str(error)})
		else:
			self._json(404, {"error": "Not found"})

	def do_POST(self) -> None:
		try:
			length = int(self.headers.get("Content-Length", "0"))
			if length <= 0 or length > 16_000:
				raise ValueError("Request body is missing or too large.")
			payload = json.loads(self.rfile.read(length))
			if self.path == "/api/analyze":
				owner, repo = _decode_repository_url(str(payload.get("url", "")))
				files = fetch_repository(owner, repo)
				repository = f"{owner}/{repo}"
				nodes, edges = parse_repository(owner, repo, files)
				store_repository(_get_graph(), repository, nodes, edges)
				snapshot = _graph_snapshot(_get_graph(), repository)
				self._json(200, {**snapshot, "fileCount": len(files), "indexedAt": __import__("datetime").datetime.now().isoformat(timespec="minutes")})
			elif self.path == "/api/ask":
				repository = str(payload.get("repository", ""))
				question = str(payload.get("question", "")).strip()
				if not repository or not question or len(question) > 1000:
					raise ValueError("Choose an analyzed repository and enter a question under 1,000 characters.")
				self._json(200, answer_question(_get_graph(), repository, question))
			else:
				self._json(404, {"error": "Not found"})
		except (ValueError, json.JSONDecodeError) as error:
			self._json(400, {"error": str(error)})
		except Exception as error:
			self._json(502, {"error": str(error)})


def _self_test() -> None:
	files = {
		"README.md": "RepoGraph demo",
		"package.json": '{"dependencies":{"mongoose":"^8.0.0"}}',
		"user_service.py": "from user_repository import UserRepository\nclass UserService:\n    def create(self):\n        return UserRepository()\n",
		"user_repository.py": "class UserRepository:\n    pass\n",
	}
	nodes, edges = parse_repository("sample", "app", files)
	names = {node["name"] for node in nodes}
	assert {"UserService", "UserRepository", "mongoose", "README"} <= names
	assert any(kind == "CALLS" for _, kind, _ in edges)
	assert any(kind == "IMPORTS" for _, kind, _ in edges)
	assert any(kind == "DEPENDS_ON" for _, kind, _ in edges)
	print(f"Parser self-test passed: {len(nodes)} nodes, {len(edges)} edges.")


def main() -> None:
	if "--self-test" in sys.argv:
		_self_test()
		return
	host = os.getenv("REPOGRAPH_HOST", "127.0.0.1")
	port = int(os.getenv("REPOGRAPH_PORT", "8000"))
	server = ThreadingHTTPServer((host, port), RepoGraphHandler)
	print(f"RepoGraph running at http://{host}:{port}")
	print(f"FalkorDB graph: {GRAPH_NAME}")
	try:
		server.serve_forever()
	except KeyboardInterrupt:
		print("\nStopping RepoGraph.")
	finally:
		server.server_close()


if __name__ == "__main__":
	main()