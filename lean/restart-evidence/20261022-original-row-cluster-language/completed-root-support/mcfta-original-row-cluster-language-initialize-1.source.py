import datetime
import hashlib
import json
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
here = root / 'lean/restart-evidence/20261022-original-row-cluster-language'
old = root / 'lean/restart-evidence/20261022-original-row-deletion-soundness'
start = '21dbf7da7ec880f6d9673213934f764e6fda7999'
assert (here / 'starting-head.txt').read_text().strip() == start
base = json.loads((here / 'starting-files.json').read_text())
assert len(base) == 91951
assert sum(p.startswith('lean/MicroCFTA/') and p.endswith('.lean') and p != 'lean/MicroCFTA/Audit.lean' for p in base) == 3635
assert sum(p.endswith('.hs') for p in base) == 298
assert sum(p.split('/')[0] in {'cfta', 'cfta-generator', 'cfta-ghc', 'decision-model'} for p in base) == 207
publication = json.loads(Path('/tmp/mcfta-original-row-deletion-soundness-local-publication.json').read_text())
assert publication['status'] == 'LOCAL_PASS' and publication['checkpoint'] == start
assert publication['clean'] and publication['filesystem_index_head_equal'] and publication['network_commands_executed'] == 0
preserved = publication['preservation']
assert len(preserved['frozen_manifests']) == 303
assert sum(p['checked'] for p in preserved['frozen_manifests'].values()) == 1397
assert len(preserved['frozen_entry_archives']) == 5
approved_path = Path('/tmp/mcfta-original-row-deletion-soundness-approved-push-20261022-2115.json')
approved = json.loads(approved_path.read_text())
assert approved['status'] == 'PUSHED_AND_REMOTE_VERIFIED' and approved['approved_commit_count'] == 12
assert approved['verified_remote_tip'] == '562120d456ea5836dc0f3cc718dafd25323521c3'
assert approved['approval_for_later_commits'] is False
assert subprocess.check_output(['git','rev-parse','origin/formalize'],cwd=root,text=True).strip() == approved['verified_remote_tip']
assert subprocess.check_output(['git','rev-list','--count',approved['verified_remote_tip']+'..HEAD'],cwd=root,text=True).strip() == '6'
previous = Path('/tmp/mcfta-original-row-cluster-language-previous-local-checkpoint')
assert not previous.exists()
previous.mkdir()
prefix = 'mcfta-original-row-deletion-soundness-'
names = []
for stem in ['support-1', 'seal-1', 'local-publication-1', 'prepare-board-1']:
    names.extend(prefix + stem + suffix for suffix in ['.json', '.log', '.limits.json', '.peaks.txt', '.source.py', '.usage.json'])
names.extend(prefix + name for name in ['local-publication.json', 'board-request.json', 'board-reply.json', 'board-readback.json', 'board-verified.json', 'approved-push-20261022-2115.json'])
pins = {}
for name in names:
    raw = (Path('/tmp') / name).read_bytes()
    (previous / name).write_bytes(raw)
    pins[name] = hashlib.sha256(raw).hexdigest()
note = '''# Previous checkpoint and current publication status

H19 is sealed at21dbf7da7ec880f6d9673213934f764e6fda7999.
Its proof is95b83f2e14a716579aa5dade638a2a4bd9a26530.
Strict1, sole FULL1 and Audit1 pass. No root capped metadata command failed.
The local publisher checked clean filesystem/index/HEAD equality and ran no network command.
After direct user approval, all12 commits47c597a8e3..562120d456 were pushed.
Remote formalize was verified at562120d456ea5836dc0f3cc718dafd25323521c3.
The approved-push receipt records this completed publication.
Older pending12-commit statements remain historical evidence. They are superseded.
The six later local commits through21dbf7da7e are outside that approval.
No approval for a later payload has arrived. Continue local proof work.
'''
(previous / 'publication-status.md').write_text(note)
pins['publication-status.md'] = hashlib.sha256(note.encode()).hexdigest()
(previous / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
assert not (here / 'archived-components.json').exists()
(here / 'archived-components.json').write_text('{}\n')
audit = (root / 'lean/MicroCFTA/Audit.lean').read_bytes()
assert hashlib.sha256(audit).hexdigest() == '7e754f81ab43baeace185b866adaf0a38c61ab347b402752cf83bba73882de5e'
assert len(audit.splitlines()) == 3125
(here / 'original-sources').mkdir()
(here / 'original-sources/Audit.original.lean.txt').write_bytes(audit)
(here / 'original-source-index.json').write_text(json.dumps(dict(sources=[dict(path='lean/MicroCFTA/Audit.lean',
    snapshot='original-sources/Audit.original.lean.txt', lines=3125, sha256=hashlib.sha256(audit).hexdigest())]), indent=2) + '\n')
for name in ['NEXT-TARGET.md', 'next-scan-root-review.json']:
    (here / ('previous-' + name)).write_bytes((old / name).read_bytes())
(here / 'current-publication-status.json').write_text(json.dumps(dict(
    published_approved_tip=approved['verified_remote_tip'], published_approved_commits=12,
    six_newer_commits_outside_approval=True, network_publication_for_next_checkpoint='PENDING_NEW_PAYLOAD_APPROVAL'),indent=2)+'\n')
timestamp = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
(here / 'current-progress.md').write_text(f'''# Original-row cluster language preservation

Updated: {timestamp}.

The previous goal turn made progress: the12 approved commits were pushed and remote-verified.
H19 remains sealed. Its105-line deletion theorem and all three proof jobs pass.
The fresh upstream refresh and91951-file baseline pass. All old proof sources stay unchanged.
The next target is one actual original-row symbol-group execution with physical union-language iff.
Keep H17's complete execution and state packet, same source/model/ranks and parent admission.
Keep actual H15 witnesses, final coherence/growth, global width/Room and final domain Trace.
Use H19 for each actual candidate-first identity-deletion decision. Keep promotion/reversal order.
Do not add a future-completion or resource oracle, new comparison, replacement model or state reset.
Only exact context/public/private and local induction statements are authorized now.
The proposed410–480 ordinary total lines and hard500 need the next exact statement gate.
Keep default declaration limits and all linters. No new Lean/Lake proof command has run.
Grouping, reconstruction, generated parents, Mu/full pass, practical width,
external solver composition, Haskell refinement and convergence remain open.
No Haskell change or repair is added. FINDINGS will retain its repair index FIRST.
H6 remains the strongest combined semantic theorem. The whole goal stays active.
The approved12-commit publication is complete. Later commits need a new payload approval.
''')
print(json.dumps(dict(status='PASS', baseline_files=91951, older_lean=3635, haskell=298, package=207,
    expected_older_registries=304, expected_older_entries=1398, previous_files=len(names), proof_jobs=0)))
