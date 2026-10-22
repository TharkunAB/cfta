import ast
import difflib
import hashlib
import json
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
OLD = ROOT / 'lean/restart-evidence/20261022-direct-edge-word-ranges'
HERE = ROOT / 'lean/restart-evidence/20261022-same-symbol-edge-original-rows'
TARGET = Path('/tmp/mcfta-same-symbol-edge-original-rows-full-preparation')
assert not TARGET.exists()
TARGET.mkdir()
(TARGET / 'predecessors').mkdir()
replacements = {
    'check-full-public.py': [
        ('H12', 'H13'),
        ('SourceCurrentAllocatedDirectEdgeWordRanges', 'SourceCurrentSameSymbolEdgeOriginalRows'),
        ('direct-edge-word-ranges', 'same-symbol-edge-original-rows'),
        ('edge_body', 'both_miss_complete'),
    ],
    'prepare-selected-full.py': [
        ('SourceCurrentAllocatedDirectEdgeWordRanges', 'SourceCurrentSameSymbolEdgeOriginalRows'),
        ('== int(expected_lines) == 44', '== int(expected_lines) and 1 <= int(expected_lines) <= 250'),
        ('== 11 and len(header.splitlines()) == 15', '== 19 and len(header.splitlines()) == 54'),
        ('.edge_body', '.both_miss_complete'),
        ("'context_lines': 11, 'actual_header_lines': 15", "'context_lines': 19, 'actual_header_lines': 54"),
    ],
}
for name, edits in replacements.items():
    source = OLD / ('full-preparation/' if name == 'check-full-public.py' else '') / name
    before = source.read_bytes()
    after = before.decode()
    for old, new in edits:
        assert old in after, (name, old)
        after = after.replace(old, new)
    ast.parse(after)
    (TARGET / 'predecessors' / (name + '.txt')).write_bytes(before)
    (TARGET / name).write_text(after)
    (TARGET / (name + '.patch')).write_text(''.join(difflib.unified_diff(
        before.decode().splitlines(keepends=True), after.splitlines(keepends=True),
        fromfile='H12/' + name, tofile='H13/' + name)))
for name in ['context.lean.txt', 'proposed-signature.lean.txt']:
    (TARGET / name).write_bytes((HERE / 'original-rows-plan' / name).read_bytes())
options = ['maxRecDepth 30000', 'maxHeartbeats 0', 'linter.all true', 'pp.explicit true',
    'pp.fullNames true', 'pp.proofs true', 'pp.proofs.threshold 254', 'pp.universes true',
    'pp.deepTerms true', 'pp.maxSteps 10000000']
head = 'MicroCFTA.SourceCurrentSameSymbolEdgeOriginalRows.both_miss_complete'
tail = '\n' + ''.join('set_option ' + option + '\n' for option in options)
tail += ''.join(directive + head + '\n' for directive in ['#check @', '#print ', '#print axioms '])
assert len(tail.splitlines()) == 14
(TARGET / 'diagnostic-tail.lean.txt').write_text(tail)
(TARGET / 'pins.json').write_text(json.dumps({
    str(p.relative_to(TARGET)): hashlib.sha256(p.read_bytes()).hexdigest()
    for p in sorted(TARGET.rglob('*')) if p.is_file()
}, indent=2) + '\n')
(TARGET / 'status.json').write_text(json.dumps({'status': 'FROZEN_SOURCE_ONLY',
    'prepared_scripts_executed': 0, 'new_proof_jobs': 0,
    'exact_context_lines': 19, 'exact_header_lines': 54,
    'diagnostic_limits_after_module_only': True}, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'prepared': str(TARGET), 'new_proof_jobs': 0}))
