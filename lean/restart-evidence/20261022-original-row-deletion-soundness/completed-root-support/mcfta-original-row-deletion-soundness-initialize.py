import datetime
import hashlib
import json
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
here = root / 'lean/restart-evidence/20261022-original-row-deletion-soundness'
old = root / 'lean/restart-evidence/20261022-original-row-physical-meaning'
start = 'a8223aafa4ef99da5570f2013aadc14af99076b3'
assert (here / 'starting-head.txt').read_text().strip() == start
base = json.loads((here / 'starting-files.json').read_text())
assert len(base) == 90717
assert sum(p.startswith('lean/MicroCFTA/') and p.endswith('.lean') and p != 'lean/MicroCFTA/Audit.lean' for p in base) == 3634
assert sum(p.endswith('.hs') for p in base) == 298
assert sum(p.split('/')[0] in {'cfta', 'cfta-generator', 'cfta-ghc', 'decision-model'} for p in base) == 207
publication = json.loads(Path('/tmp/mcfta-original-row-physical-meaning-local-publication.json').read_text())
assert publication['status'] == 'LOCAL_PASS' and publication['checkpoint'] == start
assert publication['clean'] and publication['filesystem_index_head_equal'] and publication['network_commands_executed'] == 0
assert publication['publication'] == 'PENDING_USER_APPROVAL'
preserved = publication['preservation']
assert len(preserved['frozen_manifests']) == 302
assert sum(p['checked'] for p in preserved['frozen_manifests'].values()) == 1396
assert len(preserved['frozen_entry_archives']) == 5
previous = Path('/tmp/mcfta-original-row-deletion-soundness-previous-local-checkpoint')
assert not previous.exists()
previous.mkdir()
prefix = 'mcfta-original-row-physical-meaning-'
names = []
for stem in ['support-1', 'seal-1', 'local-publication-1']:
    names.extend(prefix + stem + suffix for suffix in ['.json', '.log', '.limits.json', '.peaks.txt', '.source.py', '.usage.json'])
names.extend(prefix + name for name in ['local-publication.json', 'board-request.json', 'board-reply.json', 'board-readback.json'])
pins = {}
for name in names:
    raw = (Path('/tmp') / name).read_bytes()
    (previous / name).write_bytes(raw)
    pins[name] = hashlib.sha256(raw).hexdigest()
note = '''# Previous local checkpoint
H18 is sealed at a8223aafa4ef99da5570f2013aadc14af99076b3.
Its proof is a9c5cd9ffb2369e354362617c07db9fc288957fe.
Strict1, sole FULL1 and Audit1 pass. One Python metadata precheck repair is separate.
The local publisher checked clean filesystem/index/HEAD equality and ran no network command.
Automatic approval review rejected an earlier push and requires fresh destination and payload approval.
The pending exact 12-commit payload ends at 562120d456. No approval has arrived.
Do not retry the rejected push without that direct approval. Local proof work can continue.
'''
(previous / 'publication-blocker.md').write_text(note)
pins['publication-blocker.md'] = hashlib.sha256(note.encode()).hexdigest()
(previous / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
assert not (here / 'archived-components.json').exists()
(here / 'archived-components.json').write_text('{}\n')
audit = (root / 'lean/MicroCFTA/Audit.lean').read_bytes()
assert hashlib.sha256(audit).hexdigest() == '3dcbcdcec1ff02d14f17784dda3eba709811d291e1c82619d5eb1b4fac4ecd4e'
assert len(audit.splitlines()) == 3124
(here / 'original-sources').mkdir()
(here / 'original-sources/Audit.original.lean.txt').write_bytes(audit)
(here / 'original-source-index.json').write_text(json.dumps(dict(sources=[dict(path='lean/MicroCFTA/Audit.lean',
    snapshot='original-sources/Audit.original.lean.txt', lines=3124, sha256=hashlib.sha256(audit).hexdigest())]), indent=2) + '\n')
for name in ['NEXT-TARGET.md', 'next-deletion-root-review.json']:
    (here / ('previous-' + name)).write_bytes((old / name).read_bytes())
timestamp = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
(here / 'current-progress.md').write_text(f'''# Original-row identity deletion

Updated: {timestamp}.

The previous goal turn made progress: H18 row physical meaning passed all checks and was sealed.
The fresh upstream refresh and 90717-file baseline pass. H18 stays unchanged.
The target is both identity-deletion inclusions for one actual completed comparison result.
Keep fixed source Facts, arbitrary holds, admitted inputModel and ranked input.
Keep the original closed available parent, its two literal rows and the final coherent heap.
Use actual result residency, source-to-final growth and the canonical empty-domain EdgeLaw.
These are completed-past H15 postconditions. They do not derive a new comparison execution.
Use only EdgeLaw.sound. Derive complete row equality from each tested identity equality.
The later cluster theorem must retain its genuine H17 width and global Room.
Only exact context/public/optional private statements are authorized now.
Target 90 to 140 ordinary total lines. Hard stop: 180. Keep default limits and all linters.
No new Lean proof job has run. No Haskell change or repair is added.
Scan union preservation, grouping/generated parents/Mu and the full public pass remain open.
H6 remains the strongest combined semantic theorem. The whole goal stays active.
Remote push still needs the pending fresh direct user approval.
''')
print(json.dumps(dict(status='PASS', baseline_files=90717, older_lean=3634, haskell=298, package=207,
    expected_older_registries=303, expected_older_entries=1397, previous_files=len(names), proof_jobs=0)))
