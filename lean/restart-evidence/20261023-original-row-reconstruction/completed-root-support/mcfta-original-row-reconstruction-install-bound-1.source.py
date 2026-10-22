import ast
import hashlib
import json
import re
import runpy
import sys
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
here = root / 'lean/restart-evidence/20261023-original-row-reconstruction'
package = Path('/tmp/mcfta-original-row-reconstruction-bound-actual')
audit = Path('/tmp/mcfta-original-row-reconstruction-bound-audit')
digest = lambda data: hashlib.sha256(data).hexdigest()
load = lambda path: json.loads(path.read_bytes())
for folder in [package, audit]:
    assert (folder / 'FROZEN.json').is_file()
    pins = load(folder / 'pins.json')
    rows = pins if isinstance(pins, list) else [dict(path=path, **item) for path, item in pins.items()]
    for item in rows:
        data = (folder / item['path']).read_bytes()
        assert len(data) == item['bytes'] and digest(data) == item['sha256']
assert load(audit / 'review.json')['status'] == 'CLEAR'
scripts = load(package / 'selected-scripts.json')
values = load(package / 'binding-values.json')
assert len(scripts) == 9 and len(values) == 33
lines = assertions = 0
seen = set()
for name, item in scripts.items():
    before = (package / 'predecessors' / name).read_bytes()
    selected = (package / name).read_bytes()
    assert digest(before) == item['predecessor_sha256']
    assert digest(selected) == item['sha256']
    reconstructed = before.decode()
    for replacement in item['replacements']:
        token = replacement['token']
        assert reconstructed.count(token) == replacement['occurrences']
        seen.add(token)
        if replacement['mode'] == 'whole_quoted_JSON_literal':
            encoded = repr(json.dumps(values[token], ensure_ascii=False))
            reconstructed, count = re.subn(r"(['\"])" + re.escape(token) + r'\1', lambda _: encoded, reconstructed)
            assert count == replacement['occurrences']
        else:
            assert replacement['mode'] == 'literal_token'
            reconstructed = reconstructed.replace(token, str(values[token]))
    assert reconstructed.encode() == selected, name
    assert not re.search(r'__H23_[A-Z0-9_]+__', reconstructed)
    parsed = ast.parse(reconstructed)
    count = sum(isinstance(node, ast.Assert) for node in ast.walk(parsed))
    assert count == item['assertions'] and len(selected.splitlines()) == item['lines']
    lines += item['lines']
    assertions += count
assert seen == set(values) and lines == 828 and assertions == 280
history = load(package / 'source-history-gate.proposed.json')
assert history == values['__H23_SOURCE_HISTORY_JSON__'] and history['status'] == 'ROOT_ACCEPTED'
assert len(history['variants']) == 3 and len(history['artifacts']) == 93 and len(history['patches']) == 2
for item in history['variants'] + history['artifacts']:
    path = Path(item['path'])
    assert not path.is_absolute() and '..' not in path.parts
    data = (here / path).read_bytes()
    assert digest(data) == item['sha256']
    assert len(data.splitlines()) == item['lines'] if 'lines' in item else len(data) == item['bytes']
assert not (here / 'source-history-gate.json').exists()
for folder, name in [(package, 'bound-actual'), (audit, 'bound-audit')]:
    sys.argv = ['archive-extra.py', str(folder), name]
    runpy.run_path(str(here / 'archive-extra.py'), run_name='__main__')
for name in scripts:
    assert not (here / name).exists(), name
    (here / name).write_bytes((package / name).read_bytes())
(here / 'source-history-gate.json').write_text(json.dumps(history, indent=2) + '\n')
record = dict(status='ROOT_BOUND_TOOL_REVIEW_CLEAR', operational_scripts=9, operational_lines=lines,
    operational_assertions=assertions, composite_tools=12, composite_lines=1037, composite_assertions=332,
    bound_tokens=33, source_variants=3, source_artifacts=93, retained_source_patches=2,
    source_hard_stop=350, actual_jobs=4, failed_jobs=1,
    root_read_scope='All828programlines read. Source-history JSON data reviewed as3variants/2patches/93artifactmanifest; allbytes/hashes checked programmatically. All33bindingvalues and exact substitutions checked. Independent whole9review CLEAR.',
    selected_scripts=scripts, independent_review_sha256=digest((audit / 'review.json').read_bytes()),
    prepared_scripts_executed=False, new_lean_lake_jobs=0)
(here / 'root-bound-tools-review.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps({key: value for key, value in record.items() if key != 'selected_scripts'}))
