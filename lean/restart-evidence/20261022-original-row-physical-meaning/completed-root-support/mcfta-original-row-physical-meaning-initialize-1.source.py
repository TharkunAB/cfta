import datetime
import hashlib
import json
import shutil
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
here = root / 'lean/restart-evidence/20261022-original-row-physical-meaning'
old = root / 'lean/restart-evidence/20261022-original-row-cluster-completion'
start = '4fffdcea9e49afb54ff4c3218347a830df4cc39d'
assert (here / 'starting-head.txt').read_text().strip() == start
base = json.loads((here / 'starting-files.json').read_text())
assert len(base) == 89667
assert sum(p.startswith('lean/MicroCFTA/') and p.endswith('.lean') and p != 'lean/MicroCFTA/Audit.lean' for p in base) == 3633
assert sum(p.endswith('.hs') for p in base) == 298
assert sum(p.split('/')[0] in {'cfta', 'cfta-generator', 'cfta-ghc', 'decision-model'} for p in base) == 207
publication = json.loads(Path('/tmp/mcfta-original-row-cluster-completion-local-publication.json').read_text())
assert publication['status'] == 'LOCAL_PASS' and publication['checkpoint'] == start
assert publication['clean'] and publication['filesystem_index_head_equal'] and publication['network_commands_executed'] == 0
assert publication['publication'] == 'PENDING_USER_APPROVAL'
preserved = publication['preservation']
assert len(preserved['frozen_manifests']) == 301
assert sum(p['checked'] for p in preserved['frozen_manifests'].values()) == 1395
assert len(preserved['frozen_entry_archives']) == 5
previous = Path('/tmp/mcfta-original-row-physical-meaning-previous-local-checkpoint')
assert not previous.exists()
previous.mkdir()
prefix = 'mcfta-original-row-cluster-completion-'
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
H17 is sealed at 4fffdcea9e49afb54ff4c3218347a830df4cc39d.
Its proof is 2cc495ab5e39ae603880acd56f17122595242699.
The local publisher verified clean filesystem/index/HEAD equality and ran no network command.
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
assert hashlib.sha256(audit).hexdigest() == '47087565238f473ef8269f9328bfe087f8902cd4976c18ce0aa5e6da39542308'
assert len(audit.splitlines()) == 3123
(here / 'original-sources').mkdir()
(here / 'original-sources/Audit.original.lean.txt').write_bytes(audit)
(here / 'original-source-index.json').write_text(json.dumps(dict(sources=[dict(path='lean/MicroCFTA/Audit.lean',
    snapshot='original-sources/Audit.original.lean.txt', lines=3123, sha256=hashlib.sha256(audit).hexdigest())]), indent=2) + '\n')
for name in ['NEXT-TARGET.md', 'next-row-meaning-root-review.json']:
    (here / ('previous-' + name)).write_bytes((old / name).read_bytes())
timestamp = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
(here / 'current-progress.md').write_text(f'''# Original-row physical meaning

Updated: {timestamp}.

The previous goal turn made progress: H17 cluster completion passed all proof checks and was sealed.
The current upstream refresh and 89667-file baseline pass. H17 remains unchanged.
The target is exact physical row meaning and original/admitted children for one literal original row.
Keep the same source Facts, arbitrary holds and admitted InputMeaning. Do not replace a populated model.
Only the exact context, one public header and optional codec-helper statement are authorized now.
Use the literal row membership to derive the ordinary-node codec before payload_readback.
Target 90 to 150 ordinary source lines. Hard stop: 180 total lines. Keep default limits and all linters.
No new Lean proof job has run. No Haskell change or repair is added.
Physical scan preservation, generated parents, grouping, Mu and the public pass remain open.
H6 remains the strongest combined semantic theorem. The whole goal stays active.
Remote publication still needs the pending fresh direct user approval.
''')
print(json.dumps(dict(status='PASS', baseline_files=89667, older_lean=3633, haskell=298, package=207,
    expected_older_registries=302, expected_older_entries=1396, previous_files=len(names), proof_jobs=0)))
