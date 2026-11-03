# Use lightweight official Python image
FROM python:3.11-slim

# Prevent Python from writing .pyc files and buffer stdout/stderr
ENV PYTHONDONTWRITEBYTECODE=1 \
    PYTHONUNBUFFERED=1 \
    REPOGRAPH_HOST=0.0.0.0 \
    REPOGRAPH_PORT=8000

WORKDIR /app

# Install dependencies first (for layer caching)
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

# Copy application files
COPY main.py index.html ./

# Expose app port
EXPOSE 8000

# Run RepoGraph
CMD ["python", "main.py"]
