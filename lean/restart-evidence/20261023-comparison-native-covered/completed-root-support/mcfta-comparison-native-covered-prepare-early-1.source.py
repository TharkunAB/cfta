import ast
import difflib
import hashlib
import json
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
OLD = ROOT / 'lean/restart-evidence/20261023-completed-hit-readback'
TARGET = Path('/tmp/mcfta-comparison-native-covered-early-tools')
assert not TARGET.exists()
TARGET.mkdir()
(TARGET / 'basis').mkdir()
(TARGET / 'selected').mkdir()
expected = {
    'root-run-check.py': '37784c72c779cac7e5cbd2bfdbfaf10bf90a1cda37c117debe04495b74d604ff',
    'check-full-public.py': '3f3e363c0ca864a250d3b6466f55c0eab3ed3a1cc8c0fdbacf713215fa48bcb8',
    'prepare-selected-full.py': 'b068ee9f2d645dd2a6ba5f8473fde4810b3f395967ed12c9567002d1e9cc4763',
}
replacements = {
    'SourceCurrentSameSymbolEdgeHitReadback': 'SourceCurrentSameSymbolEdgeComparisonCovered',
    'completed_hit_checked': 'original_rows_complete',
    'completed-hit-readback': 'comparison-native-covered',
    'H27': 'H28',
    'int("180")': 'int("230")',
    "json.loads('[\"yielded_done\", \"ret_checked\"]')": "json.loads('[]')",
}
metrics = {}
for name, expected_sha in expected.items():
    raw = (OLD / name).read_bytes()
    assert hashlib.sha256(raw).hexdigest() == expected_sha, name
    (TARGET / 'basis' / name).write_bytes(raw)
    old = raw.decode()
    new = old
    used = {}
    for before, after in replacements.items():
        count = new.count(before)
        if count:
            used[before] = dict(replacement=after, occurrences=count)
            new = new.replace(before, after)
    ast.parse(new)
    (TARGET / 'selected' / name).write_text(new)
    (TARGET / (name + '.patch')).write_text(''.join(difflib.unified_diff(
        old.splitlines(keepends=True), new.splitlines(keepends=True), fromfile='basis/' + name, tofile='selected/' + name)))
    metrics[name] = dict(lines=len(new.splitlines()),
        assertions=sum(isinstance(node, ast.Assert) for node in ast.walk(ast.parse(new))),
        sha256=hashlib.sha256(new.encode()).hexdigest(), replacements=used)
tail_options = ['maxRecDepth 30000', 'maxHeartbeats 0', 'linter.all true', 'pp.explicit true',
    'pp.fullNames true', 'pp.proofs true', 'pp.proofs.threshold 254', 'pp.universes true',
    'pp.deepTerms true', 'pp.maxSteps 10000000']
tail = '\n' + ''.join('set_option ' + option + '\n' for option in tail_options)
tail += ''.join(command + 'MicroCFTA.SourceCurrentSameSymbolEdgeComparisonCovered.original_rows_complete\n'
    for command in ['#check @', '#print ', '#print axioms '])
(TARGET / 'diagnostic-tail.lean.txt').write_text(tail)
(TARGET / 'review-boundary.md').write_text('''# Early tool source boundary

These three tools retain the accepted H27 algorithms. Literal changes select
the H28 module, public head, artifact names, proposed cap230 and no private helper.
The proposed cap needs the exact declaration gate before any body or compiler.
Only diagnostic printing changes limits, after the complete module.
Strict source compilation keeps default limits and all linters.
The complete public TYPE must be read by root and an independent reviewer.
BODY evidence remains programmatic only. No prepared tool has been executed.
''')
(TARGET / 'metrics.json').write_text(json.dumps(metrics, indent=2) + '\n')
pins = []
for path in sorted(TARGET.rglob('*')):
    if path.is_file():
        data = path.read_bytes()
        pins.append(dict(path=str(path.relative_to(TARGET)), bytes=len(data), sha256=hashlib.sha256(data).hexdigest()))
(TARGET / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
freeze = dict(status='SOURCE_ONLY_PENDING_ROOT_AND_INDEPENDENT_REVIEW',
    pins_sha256=hashlib.sha256((TARGET / 'pins.json').read_bytes()).hexdigest(),
    prepared_execution=False, proposed_source_cap=230, declaration_gate_required=True)
(TARGET / 'FROZEN.json').write_text(json.dumps(freeze, indent=2) + '\n')
print(json.dumps(dict(status='PASS', directory=str(TARGET), metrics=metrics,
    pins_sha256=freeze['pins_sha256'], frozen_sha256=hashlib.sha256((TARGET / 'FROZEN.json').read_bytes()).hexdigest())))
