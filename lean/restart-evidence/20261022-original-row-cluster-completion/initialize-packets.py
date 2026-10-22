import datetime
import difflib
import hashlib
import json
import shutil
from pathlib import Path

HERE = Path(__file__).resolve().parent
START = '562120d456ea5836dc0f3cc718dafd25323521c3'
assert (HERE / 'starting-head.txt').read_text().strip() == START
baseline = json.loads((HERE / 'starting-files.json').read_text())
assert len(baseline) == 88001
assert sum(p.startswith('lean/MicroCFTA/') and p.endswith('.lean') and
           p != 'lean/MicroCFTA/Audit.lean' for p in baseline) == 3632
assert sum(p.endswith('.hs') for p in baseline) == 298
assert sum(p.split('/')[0] in {'cfta', 'cfta-generator', 'cfta-ghc', 'decision-model'}
           for p in baseline) == 207
old = HERE.parent / '20261022-original-row-cluster-control/initialize-packets.py'
(HERE / 'initialize-packets.H16-original.txt').write_bytes(old.read_bytes())
(HERE / 'initialize-packets.patch').write_text(''.join(difflib.unified_diff(
    old.read_text().splitlines(True), Path(__file__).read_text().splitlines(True),
    fromfile='H16/initialize-packets.py', tofile='H17/initialize-packets.py')))
report = json.loads(Path('/tmp/mcfta-original-row-cluster-control-local-publication.json').read_text())
assert report['status'] == 'LOCAL_PASS' and report['clean'] and report['filesystem_index_head_equal']
assert report['checkpoint'] == START and report['publication'] == 'PENDING_USER_APPROVAL'
assert report['network_commands_executed'] == 0
preserved = report['preservation']
assert len(preserved['frozen_manifests']) == 300
assert sum(p['checked'] for p in preserved['frozen_manifests'].values()) == 1394
assert len(preserved['frozen_entry_archives']) == 5
previous = Path('/tmp/mcfta-original-row-cluster-completion-previous-local-checkpoint')
assert not previous.exists()
previous.mkdir()
prefix = 'mcfta-original-row-cluster-control-'
names = []
for stem in ['support-1', 'seal-1', 'local-publication-1']:
    names += [prefix + stem + suffix for suffix in
              ['.json', '.log', '.limits.json', '.peaks.txt', '.source.py', '.usage.json']]
names += [prefix + tail for tail in
          ['local-publication.json', 'board-request.json', 'board-reply.json', 'board-readback.json']]
pins = {}
for name in names:
    source = Path('/tmp') / name
    assert source.is_file(), name
    shutil.copyfile(source, previous / name)
    pins[name] = hashlib.sha256(source.read_bytes()).hexdigest()
note = '''# Previous checkpoint publication status

H16 is committed locally at562120d456ea5836dc0f3cc718dafd25323521c3.
Its proof is272cb31f5ff5d60c9396a931931aea1297759cad.
Its local publisher ran no network command. FS=index=HEAD and the tree was clean.
Its board post and exact readback state that publication remains pending.
Automatic approval review rejected the earlier H11 push before execution twice.
That review requires fresh direct approval of the destination and payload.
The configured destination is git@github.com:TharkunAB/cfta.git formalize.
Fresh approval was requested for the12 commits through562120d456.
No approval has arrived. Automatic goal continuation supplies no approval.
Do not retry the rejected push without direct user approval.
Local formalization can continue while publication remains pending.
'''
(previous / 'publication-blocker.md').write_text(note)
pins['publication-blocker.md'] = hashlib.sha256(note.encode()).hexdigest()
(previous / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
assert not (HERE / 'archived-components.json').exists()
(HERE / 'archived-components.json').write_text('{}\n')
timestamp = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
(HERE / 'current-progress.md').write_text(f'''# Genuine original-row cluster completion

Updated: {timestamp}.

The pull reports Already up to date. All88001 starting blobs and modes agree.
H16 remains sealed and unchanged at{START}.
The target is actual H16 runner completion for one exact original-parent symbol group.
It must retain original membership, a length bound, all current invariants and global Trace.
The SAME fixed source/models, populated state, initial domain cache and reservation remain.
Use H15 to derive each comparison. Do not assume future success or use a callback.
Only the exact context, public header and two helper statements are authorized now.
Bodies and compiler commands need separate complete source review.
Target270 to350 ordinary source lines. HARD STOP350 before further source or a check.
No new Lean command has run. No Haskell source or repair changes.
Physical pruning, grouping, generated parents, Mu and the full public pass remain open.
H6 constructed_node_calls remains the strongest combined semantic theorem.
The overall goal stays active. Remote publication still needs fresh approval.
''')
print(json.dumps({'status': 'PASS', 'previous_local_files': len(names), 'proof_jobs': 0,
    'baseline_files': len(baseline), 'older_non_audit_lean': 3632, 'haskell': 298,
    'package': 207, 'expected_frozen_registries': 301, 'expected_frozen_entries': 1395,
    'publication': 'PENDING_USER_APPROVAL'}))
