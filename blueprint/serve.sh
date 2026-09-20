#!/usr/bin/env bash
set -euo pipefail
project_dir="$(cd "$(dirname "$0")/.." && pwd)"
cd "$project_dir"
exec blueprint/.venv/bin/python -m http.server "${1:-8041}" --bind 127.0.0.1 --directory blueprint/web
