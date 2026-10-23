import ast
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = ROOT / 'lean/restart-evidence/20261023-pair-stable-model-transport'
PACKAGE = Path('/tmp/mcfta-pair-stable-model-transport-bound-tools')
AUDIT = Path('/tmp/mcfta-pair-stable-model-transport-bound-audit')
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
def load(path):
    return json.loads(path.read_bytes())

assert sha(PACKAGE / 'pins.json') == 'b28fe2badbc92f8f02ab2905f31fb4cf71256bab5caf544d6093411e5e7dfef8'
assert sha(PACKAGE / 'FROZEN.json') == '4c4dd61ccdd0cbf507d0d5618ea035bf735cacc188822b3c9532d9d42ed22fa3'
assert sha(AUDIT / 'review.json') == sys.argv[1]
assert load(AUDIT / 'review.json')['status'] == 'SOURCE_CLEAR'
assert load(AUDIT / 'review.json')['no_blocker_found'] is True
for folder in [PACKAGE, AUDIT]:
    assert (folder / 'FROZEN.json').exists()
    pins = load(folder / 'pins.json')
    if isinstance(pins, dict):
        pins = [dict(path=name, **pin) for name, pin in pins.items()]
    for pin in pins:
        path = folder / pin['path']
        assert path.stat().st_size == pin['bytes'] and sha(path) == pin['sha256'], path
scripts = load(PACKAGE / 'selected-scripts.json')
values = load(PACKAGE / 'binding-values.json')
assert len(scripts) == 9 and len(values) == 31
lines = assertions = 0
seen = set()
for name, pin in scripts.items():
    before = (PACKAGE / 'predecessors' / name).read_bytes()
    selected = (PACKAGE / name).read_bytes()
    assert sha(PACKAGE / 'predecessors' / name) == pin['predecessor_sha256']
    assert before == (HERE / 'checkpoint-preparation' / name).read_bytes()
    assert sha(PACKAGE / name) == pin['sha256']
    reconstructed = before.decode()
    for replacement in pin['substitutions']:
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
    assert reconstructed.encode() == selected and not re.search(r'__H24_[A-Z0-9_]+__', reconstructed)
    count = sum(isinstance(node, ast.Assert) for node in ast.walk(ast.parse(reconstructed)))
    assert count == pin['assertions'] and len(selected.splitlines()) == pin['lines']
    lines += pin['lines']
    assertions += count
assert seen == set(values) and lines == 795 and assertions == 274
history = load(PACKAGE / 'source-history-gate.proposed.json')
assert history == values['__H24_SOURCE_HISTORY_JSON__'] and history['status'] == 'ROOT_ACCEPTED'
assert len(history['variants']) == 1 and len(history['artifacts']) == 84 and not history['patches']
for item in history['variants'] + history['artifacts']:
    relative = Path(item['path'])
    assert not relative.is_absolute() and '..' not in relative.parts
    path = HERE / relative
    data = path.read_bytes()
    assert sha(path) == item['sha256']
    assert len(data.splitlines()) == item['lines'] if 'lines' in item else len(data) == item['bytes']
proposals = load(PACKAGE / 'root-installation-proposals.json')['copy_after_root_review']
assert list(proposals.values()) == ['selected-sources.json', 'selected-source-gate.json', 'frozen-modules.json',
    'source-history-gate.json', 'selected-sources/SourceCurrentSameSymbolEdgeModelTransport.lean']
for folder, name in [(PACKAGE, 'bound-actual'), (AUDIT, 'bound-audit')]:
    subprocess.run(['/usr/bin/python3', str(HERE / 'archive-extra.py'), str(folder), name], check=True)
for name in scripts:
    assert not (HERE / name).exists()
    (HERE / name).write_bytes((PACKAGE / name).read_bytes())
for source, target in proposals.items():
    path = HERE / target
    assert not path.exists()
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes((PACKAGE / source).read_bytes())
report = dict(status='ROOT_BOUND_TOOL_REVIEW_CLEAR', operational_scripts=9, operational_lines=lines,
    operational_assertions=assertions, composite_tools=12, composite_lines=1005, composite_assertions=327,
    bound_tokens=31, source_variants=1, source_artifacts=84, retained_source_patches=0,
    source_hard_stop=120, actual_jobs=3, failed_jobs=0,
    root_read_scope='All1005 template program lines, all31 structured binding values and exact substitutions reviewed. Bound795-line code reconstructs exactly. The84 history artifact bytes and hashes are checked programmatically. Independent whole9 review CLEAR.',
    selected_scripts=scripts, independent_review_sha256=sha(AUDIT / 'review.json'),
    prepared_scripts_executed=False, new_lean_lake_jobs=0)
(HERE / 'root-bound-tools-review.json').write_text(json.dumps(report, indent=2) + '\n')
target = HERE / 'NEXT-TARGET.md'
note = target.read_text()
old = 'Two root metadata commands failed: the initial SSH fetch and the first manifest archive.\nThe HTTPS fetch and corrected list-manifest archive passed. All attempts remain.\n'
new = 'Three root metadata commands failed: the initial SSH fetch, first manifest archive,\nand first bound installation status check. The check expected CLEAR instead of the\nactual SOURCE_CLEAR status. It failed before mutation. The corrected checks and retries pass.\nThe HTTPS fetch and corrected list-manifest archive passed. All attempts remain.\n'
assert note.count(old) == 1
target.write_text(note.replace(old, new))
print(json.dumps({key: value for key, value in report.items() if key != 'selected_scripts'}))
