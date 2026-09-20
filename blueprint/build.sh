#!/usr/bin/env bash
set -euo pipefail
project_dir="$(cd "$(dirname "$0")/.." && pwd)"
cd "$project_dir"
if [[ ! -x blueprint/.venv/bin/leanblueprint ]]; then
  echo 'Missing blueprint environment. See blueprint/README.md for setup.' >&2
  exit 1
fi
export PATH="$project_dir/blueprint/.venv/bin:$PATH"
lake build
leanblueprint pdf > blueprint/pdf-build.log 2>&1
leanblueprint web > blueprint/web-build.log 2>&1
leanblueprint checkdecls > blueprint/checkdecls.log 2>&1
python blueprint/scripts/source_links.py
python blueprint/scripts/enhance_site.py
python blueprint/scripts/verify_site.py
echo 'Blueprint ready: blueprint/web/index.html and blueprint/print/print.pdf'
