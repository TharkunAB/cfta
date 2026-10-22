import datetime
import hashlib
import json
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
here = root / 'lean/restart-evidence/20261022-original-row-group-chain'
old = root / 'lean/restart-evidence/20261022-prepend-grouping'
start = '70787b95484cb69897bc4075858e07c7f9c22433'
assert (here / 'starting-head.txt').read_text().strip() == start
base = json.loads((here / 'starting-files.json').read_text())
counts = dict(baseline_files=len(base),older_lean=sum(p.startswith('lean/MicroCFTA/') and p.endswith('.lean') and p != 'lean/MicroCFTA/Audit.lean' for p in base),haskell=sum(p.endswith('.hs') for p in base),package=sum(p.split('/')[0] in {'cfta','cfta-generator','cfta-ghc','decision-model'} for p in base))
assert counts == dict(baseline_files=96320,older_lean=3637,haskell=298,package=207)
publication = json.loads(Path('/tmp/mcfta-prepend-grouping-local-publication.json').read_text())
assert publication['status'] == 'LOCAL_PASS' and publication['checkpoint'] == start
assert publication['filesystem_index_head_equal'] and publication['clean']
assert publication['selected_proof']['archived_components'] == 33 and publication['selected_proof']['actual_jobs'] == 5
previous = Path('/tmp/mcfta-original-row-group-chain-previous-local-checkpoint')
assert not previous.exists()
previous.mkdir()
prefix = 'mcfta-prepend-grouping-'
names = [prefix + stem + suffix for stem in ['support-1','seal-1','local-publication-1','prepare-board-1'] for suffix in ['.json','.log','.limits.json','.peaks.txt','.source.py','.usage.json']]
names.extend(prefix + name for name in ['local-publication.json','board-request.json','board-reply.json','board-readback.json','board-verified.json'])
pins = {}
for name in names:
    raw = (Path('/tmp') / name).read_bytes()
    (previous / name).write_bytes(raw)
    pins[name] = hashlib.sha256(raw).hexdigest()
(previous / 'pins.json').write_text(json.dumps(pins,indent=2) + '\n')
assert not (here / 'archived-components.json').exists()
(here / 'archived-components.json').write_text('{}\n')
(here / 'baseline-counts.json').write_text(json.dumps(counts,indent=2) + '\n')
(here / 'original-sources').mkdir()
audit = (root / 'lean/MicroCFTA/Audit.lean').read_bytes()
assert len(audit.splitlines()) == 3127 and hashlib.sha256(audit).hexdigest() == '4c54e8f578cc9e12084e7306671e6c6410150811a3868fc128b90805ae5452e1'
(here / 'original-sources/Audit.original.lean.txt').write_bytes(audit)
(here / 'original-source-index.json').write_text(json.dumps(dict(sources=[dict(path='lean/MicroCFTA/Audit.lean',snapshot='original-sources/Audit.original.lean.txt',lines=len(audit.splitlines()),sha256=hashlib.sha256(audit).hexdigest())]),indent=2) + '\n')
for name in ['NEXT-TARGET.md','root-next-traversal-review.json']:
    (here / ('previous-' + name)).write_bytes((old / name).read_bytes())
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
(here / 'current-progress.md').write_text(f'''# Original-parent symbol-group execution chain

Updated: {now}. Start: {start}.

Previous goal turn: PROGRESS. H21 adds a checked grouping bridge and a sealed checkpoint.
H21 strict3, sole FULL1 and Audit1 pass. Audit has3638 jobs/75494 dependencies.
Five actual proof jobs include two failed stricts. One metadata reader failed.
The original reader, exact whitespace repair and stale-verifier-path repair remain retained.
Final normal/live checks,33 archived components, seal2735/2746 and local publication pass.
All96320 tracked blobs/modes are verified. The start was clean.
The prior handoff was posted and read back. Those receipts remain historical evidence.
NEXT-PROMPT explicitly prohibits further messages or board posts. Follow that project rule.

Fresh upstream pull passes. HEAD remains70787b95484cb69897bc4075858e07c7f9c22433.
origin/formalize remains562120d456; origin/main remains794903b3fbad3becb8b28736fc33463760731fc7.
The backup branch and fresh96320-file baseline retain all proofs, drafts, counterexamples
and the optimized interned core. All298 Haskell and207 package files remain.
The older12-commit approved push is complete. The earlier exact8 question excludes H21.
No fresh push approval has arrived. This phase runs no network publication command.

Next work derives actual H16 runs for every finite symbol group from H20.
H21 supplies exact reversed-bucket readback. Preserve supplied iterator order and duplicates.
Keep one evolving full Wrapper, fixed source/model/ranks/width/initialDomains and global Trace.
Derive every step from the genuine initial packet and the same initial Room tuple.
Do not assume future completion or capacity. Return cumulative effects and physical union iff.
The literal modeled row view does not prove Haskell Mu/union unfolding.
Generated-parent admission, executable outer traversal and public full-pass correctness remain open.

Only exact declaration context, public/private/local statements and a total budget are pending.
Root and independent declaration review must precede any body or compiler command.
No next mathematical body, official module, check or success is claimed at this cut.
H6 remains strongest combined. The whole formalization goal stays active.
No Haskell change or new repair is added. Keep the FINDINGS repair index FIRST.
''')
print(json.dumps(dict(status='PASS',**counts,previous_support_files=len(names),proof_jobs=0,previous_goal_turn='PROGRESS')))
