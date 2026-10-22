import datetime
import hashlib
import json
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
here = root / 'lean/restart-evidence/20261022-prepend-grouping'
old = root / 'lean/restart-evidence/20261022-original-row-cluster-language'
start = 'd0cf685f461430a7c608ceb3b76da0fe568e4d84'
assert (here / 'starting-head.txt').read_text().strip() == start
base = json.loads((here / 'starting-files.json').read_text())
assert len(base) == 93582
counts = dict(baseline_files=len(base),
    older_lean=sum(p.startswith('lean/MicroCFTA/') and p.endswith('.lean') and p != 'lean/MicroCFTA/Audit.lean' for p in base),
    haskell=sum(p.endswith('.hs') for p in base),
    package=sum(p.split('/')[0] in {'cfta', 'cfta-generator', 'cfta-ghc', 'decision-model'} for p in base))
assert counts == dict(baseline_files=93582, older_lean=3636, haskell=298, package=207)
publication = json.loads(Path('/tmp/mcfta-original-row-cluster-language-local-publication.json').read_text())
assert publication['status'] == 'LOCAL_PASS' and publication['checkpoint'] == start
assert publication['filesystem_index_head_equal'] and publication['clean']
assert publication['selected_proof']['archived_components'] == 21
assert publication['selected_proof']['actual_jobs'] == 4
previous = Path('/tmp/mcfta-prepend-grouping-previous-local-checkpoint')
assert not previous.exists()
previous.mkdir()
prefix = 'mcfta-original-row-cluster-language-'
names = []
for stem in ['support-1', 'seal-1', 'local-publication-1', 'prepare-board-1']:
    names.extend(prefix + stem + suffix for suffix in ['.json', '.log', '.limits.json', '.peaks.txt', '.source.py', '.usage.json'])
names.extend(prefix + name for name in ['local-publication.json', 'board-request.json', 'board-reply.json', 'board-readback.json', 'board-verified.json'])
pins = {}
for name in names:
    raw = (Path('/tmp') / name).read_bytes()
    (previous / name).write_bytes(raw)
    pins[name] = hashlib.sha256(raw).hexdigest()
(previous / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
assert not (here / 'archived-components.json').exists()
(here / 'archived-components.json').write_text('{}\n')
(here / 'baseline-counts.json').write_text(json.dumps(counts, indent=2) + '\n')
(here / 'original-sources').mkdir()
audit = (root / 'lean/MicroCFTA/Audit.lean').read_bytes()
(here / 'original-sources/Audit.original.lean.txt').write_bytes(audit)
(here / 'original-source-index.json').write_text(json.dumps(dict(sources=[dict(path='lean/MicroCFTA/Audit.lean',
    snapshot='original-sources/Audit.original.lean.txt', lines=len(audit.splitlines()),
    sha256=hashlib.sha256(audit).hexdigest())]), indent=2) + '\n')
for name in ['NEXT-TARGET.md', 'next-grouping-root-inventory.json']:
    (here / ('previous-' + name)).write_bytes((old / name).read_bytes())
timestamp = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
(here / 'current-progress.md').write_text(f'''# Prepend grouping and bucket reversal

Updated: {timestamp}. Start: {start}.

H20 is sealed and locally verified. Its original symbol-group scan preserves physical union language.
All four proof commands exit zero. The first strict command has one retained warning.
The selected strict2 and sole FULL1 are clean. Audit passes at3637 jobs/75482 dependencies.
Final saved checks and preservation pass at21 components. The H20 handoff is posted and read back.
The older12 approved commits were pushed through562120d456. Newer8 remain outside that approval.
A fresh exact-payload approval question covers2cc495ab5e through{start}.
No approval for that newer payload has arrived at this cut.

Fresh upstream refresh and93582-file baseline pass. The backup branch retains the exact start.
This slice models singleton-prepend insertion, optional-bucket reversal and finite iterator transport.
It reuses SourceCurrentMergeGrouping without edits. The generic key later uses symbol alone.
Preserve absence, stored empty buckets, repeated occurrences and within-bucket input order.
Only exact declaration contracts and a total line budget are under preparation.
No mathematical body, new Lean module or compiler command is authorized yet.
Read the primary APIs and independently review all declarations before implementation.
The target is120–200 ordinary lines, with a proposed hard240-line limit.

Actual HashMap refinement, group traversal, generated parents, reconstruction and Mu/full pass remain open.
Practical width, solver composition, Haskell refinement and convergence remain open.
No Haskell change or new repair is added. FINDINGS keeps its repair index first.
H6 remains the strongest combined trace theorem. The whole goal stays active.
''')
print(json.dumps(dict(status='PASS', **counts, previous_support_files=len(names), proof_jobs=0)))
