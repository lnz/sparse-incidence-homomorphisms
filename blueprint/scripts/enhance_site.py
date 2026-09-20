#!/usr/bin/env python3
"""Add the small local interaction layer to generated blueprint pages."""
from pathlib import Path
import shutil
import re

root = Path(__file__).resolve().parents[1]
web = root / "web"
script = '<script src="js/blueprint-ui.js" defer></script>'

shutil.copyfile(root / "src/blueprint-ui.js", web / "js/blueprint-ui.js")
for page in web.glob("*.html"):
    html = page.read_text()
    if page.name == "index.html":
        html = re.sub(r'<nav class=(?:"local_toc"|local_toc)>.*?</nav>',
                      '', html, count=1, flags=re.DOTALL)
    if script not in html:
        html = html.replace("</body>", f"{script}\n</body>")
        page.write_text(html)
