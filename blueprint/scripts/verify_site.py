#!/usr/bin/env python3
"""Check local generated assets, links, declaration anchors, and dependency labels."""
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import urlsplit, unquote
import json, re
ROOT=Path(__file__).resolve().parents[2]
WEB=ROOT/'blueprint/web'
class Page(HTMLParser):
    def __init__(self,text):
        super().__init__(); self.ids=set();self.links=[];self.feed(text)
    def handle_starttag(self,tag,attrs):
        a=dict(attrs)
        if 'id' in a:self.ids.add(a['id'])
        if tag=='a' and 'name' in a:self.ids.add(a['name'])
        for attribute in (['href'] if tag in ('a','link') else ['src'] if tag in ('img','script') else []):
            if attribute in a:self.links.append(a[attribute])
pages={p.resolve():Page(p.read_text()) for p in WEB.rglob('*.html')}
errors=[]
for p,page in pages.items():
    for href in page.links:
        url=urlsplit(href)
        if url.scheme or url.netloc or not href:continue
        target=(p.parent/unquote(url.path)).resolve() if url.path else p
        if target.is_dir():target=target/'index.html'
        if not target.exists():errors.append(f'{p.name}: missing {href}');continue
        fragment=unquote(url.fragment)
        if fragment and not fragment.startswith('doc/') and target in pages and fragment not in pages[target].ids:
            errors.append(f'{p.name}: missing anchor {href}')
content=(ROOT/'blueprint/src/content.tex').read_text()
labels=set(re.findall(r'\\label\{([^}]+)\}',content))
for group in re.findall(r'\\uses\{([^}]+)\}',content):
    for label in map(str.strip,group.split(',')):
        if label not in labels:errors.append('Unknown dependency label: '+label)
for module in {entry['module'] for entry in json.loads((ROOT/'blueprint/source-links.json').read_text()).values()}:
    source=(ROOT/f'Paper/{module}.lean').read_bytes()
    assert source==(WEB/f'lean/Paper/{module}.lean').read_bytes(), f'{module} source browser is stale'
refs=set((ROOT/'blueprint/lean_decls').read_text().splitlines())
anchors=json.loads((ROOT/'blueprint/source-links.json').read_text())
assert refs==set(anchors), 'Declaration links are stale'
for name, entry in anchors.items():
    target=(WEB/f"lean/Paper/{entry['module']}.html").resolve()
    assert name in pages[target].ids, f'Missing declaration anchor for {name}'
    assert f"L{entry['line']}" in pages[target].ids, f'Missing source line for {name}'
external=content.split('\\label{thm:external-rounding}',1)[1].split('\\end{theorem}',1)[0]
assert 'external_rounding' in external
if errors:raise SystemExit('\n'.join(errors))
print(f'Validated {len(pages)} HTML pages, all local links/assets, {len(labels)} labels, and {len(refs)} declaration links.')
