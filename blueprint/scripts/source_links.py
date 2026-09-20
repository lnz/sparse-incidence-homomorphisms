#!/usr/bin/env python3
"""Build a small local Lean source browser for blueprint declaration links."""
from pathlib import Path
import html, json, re
from pygments import highlight
from pygments.lexers import get_lexer_by_name
from pygments.formatters import HtmlFormatter

root = Path(__file__).resolve().parents[2]
web = root/'blueprint/web'
sources = {path.stem: path.read_text() for path in sorted((root/'Paper').glob('*.lean'))
           if path.stem != 'Audit'}
declarations = {}
for module, source in sources.items():
    namespace = []
    for lineno, line in enumerate(source.splitlines(), 1):
        if line.startswith('namespace '):
            namespace.append(line.split()[1])
        elif re.match(r'^end(?:\s|$)', line):
            if namespace:
                namespace.pop()
        else:
            match = re.match(r'^(?:noncomputable\s+)?(?:def|theorem|lemma|structure|axiom|abbrev)\s+(\S+)', line)
            if match:
                name = '.'.join(namespace + [match.group(1)])
                declarations[name] = {'module': module, 'line': lineno}
referenced={s.strip() for s in (root/'blueprint/lean_decls').read_text().splitlines() if s.strip()}
missing=referenced-declarations.keys()
if missing:
    raise SystemExit('Missing source anchors: '+', '.join(sorted(missing)))
module_dir=web/'lean/Paper'
module_dir.mkdir(parents=True,exist_ok=True)
for module, source in sources.items():
    formatter=HtmlFormatter(nowrap=True)
    lines=highlight(source,get_lexer_by_name('lean4'),formatter).splitlines()
    by_line={entry['line']:name for name,entry in declarations.items() if entry['module']==module}
    rows=[]
    for number,code in enumerate(lines,1):
        anchor=f'<a id="{html.escape(by_line[number])}" class="declaration-anchor"></a>' if number in by_line else ''
        rows.append(f'{anchor}<span class="source-line" id="L{number}"><a class="line-number" href="#L{number}">{number}</a>{code}</span>')
    page='''<!doctype html><html lang="en"><head><meta charset="utf-8">
    <meta name="viewport" content="width=device-width, initial-scale=1">
    <title>Paper/__MODULE__.lean — source</title><style>
    body{margin:0;background:#fbfcfc;color:#18282b;font:15px system-ui,sans-serif}
    header{position:sticky;top:0;padding:16px 24px;background:#eaf1f1;border-bottom:1px solid #cbd8d8;z-index:2}
    header a{color:#21565e;margin-right:24px} h1{font-size:17px;display:inline;margin-right:28px}
    pre{margin:0;padding:16px 24px;font:13px/1.65 ui-monospace,SFMono-Regular,monospace;overflow:auto}
    .source-line{display:block;min-height:1.65em}.line-number{display:inline-block;width:4em;margin-right:1em;text-align:right;color:#6d8185;text-decoration:none;user-select:none}
    .declaration-anchor{display:block;scroll-margin-top:74px}.declaration-anchor:target + .source-line,.source-line:target{background:#fff2b8}
    .source-line{scroll-margin-top:74px}
    '''+formatter.get_style_defs('.code')+'''</style></head><body>
    <header><h1>Paper/__MODULE__.lean</h1><a href="../../index.html">Blueprint</a><a href="../../dep_graph_document.html">Dependency graph</a><a href="__MODULE__.lean">Raw source</a></header>
    <pre class="code">'''+ ''.join(rows)+ '</pre></body></html>'
    (module_dir/f'{module}.html').write_text(page.replace('__MODULE__', module))
    (module_dir/f'{module}.lean').write_text(source)
finder=web/'lean/find'
finder.mkdir(parents=True,exist_ok=True)
(finder/'index.html').write_text('''<!doctype html><html lang="en"><meta charset="utf-8"><title>Lean declaration</title>
<p id="status">Opening Lean source…</p><script>
const names = '''+json.dumps({name: entry['module'] for name, entry in declarations.items()})+''';
const name = decodeURIComponent(location.hash.startsWith('#doc/') ? location.hash.slice(5) : location.hash.slice(1));
if (Object.hasOwn(names, name)) location.replace('../Paper/' + names[name] + '.html#' + encodeURIComponent(name));
else document.getElementById('status').textContent = 'Unknown Lean declaration: ' + name;
</script></html>''')
(root/'blueprint/source-links.json').write_text(json.dumps({name:declarations[name] for name in sorted(referenced)},indent=2)+'\n')
print(f'Created source links for all {len(referenced)} blueprint declarations; no doc-gen4 or duplicate Mathlib build required.')
