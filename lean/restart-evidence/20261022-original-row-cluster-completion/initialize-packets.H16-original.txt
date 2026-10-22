import datetime
import difflib
import hashlib
import json
import shutil
from pathlib import Path

HERE = Path(__file__).resolve().parent
START = '4f7a7e064f17a66367618dc2bc360f0755503b1a'
assert (HERE / 'starting-head.txt').read_text().strip() == START
baseline = json.loads((HERE / 'starting-files.json').read_text())
assert len(baseline) == 86577
assert sum(p.startswith('lean/MicroCFTA/') and p.endswith('.lean') and
           p != 'lean/MicroCFTA/Audit.lean' for p in baseline) == 3631
assert sum(p.endswith('.hs') for p in baseline) == 298
assert sum(p.split('/')[0] in {'cfta', 'cfta-generator', 'cfta-ghc', 'decision-model'}
           for p in baseline) == 207
old = HERE.parent / '20261022-same-symbol-edge-comparison-domains/initialize-packets.py'
(HERE / 'initialize-packets.H15-original.txt').write_bytes(old.read_bytes())
(HERE / 'initialize-packets.patch').write_text(''.join(difflib.unified_diff(
    old.read_text().splitlines(True), Path(__file__).read_text().splitlines(True),
    fromfile='H15/initialize-packets.py', tofile='H16/initialize-packets.py')))
report = json.loads(Path('/tmp/mcfta-same-symbol-edge-comparison-domains-local-publication.json').read_text())
assert report['status'] == 'LOCAL_PASS' and report['clean'] and report['filesystem_index_head_equal']
assert report['checkpoint'] == START and report['publication'] == 'PENDING_USER_APPROVAL'
assert report['network_commands_executed'] == 0
preserved = report['preservation']
assert len(preserved['frozen_manifests']) == 299
assert sum(p['checked'] for p in preserved['frozen_manifests'].values()) == 1393
assert len(preserved['frozen_entry_archives']) == 5
previous = Path('/tmp/mcfta-original-row-cluster-control-previous-local-checkpoint')
assert not previous.exists()
previous.mkdir()
prefix = 'mcfta-same-symbol-edge-comparison-domains-'
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

H15 is committed locally at 4f7a7e064f17a66367618dc2bc360f0755503b1a.
Its proof commit is 1dfbb4feec0ee33cb964df772ca8f878b279c1a3.
Its local publisher ran no network command. FS=index=HEAD and the tree was clean.
Its exact board post and readback state that publication remains pending.
Automatic approval review rejected the earlier H11 push before execution twice.
That review requires fresh direct approval of the destination and payload.
The configured destination was git@github.com:TharkunAB/cfta.git formalize.
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
(HERE / 'current-progress.md').write_text(f'''# Original-row cluster operational control

Updated: {timestamp}.

The current pull reports Already up to date. All 86577 starting blobs and modes agree.
H15 remains sealed and unchanged at {START}.
The next slice prepares cluster, scan and comparison controls over the SAME H7 State.
The exact source context, declaration schema and public comparison_lift header are pending.
Only that proposal is authorized. Definition/theorem bodies and compiler runs are not authorized yet.
The later public result must use a positive consumed prefix bounded by the supplied H7 fuel.
It must yield the exact ordered resume control and SAME returned state.
The source target is 120 to 180 lines. Stop at 220 before further source or a check.
No new Lean proof command has run. No Haskell source or repair changes.
Actual cluster completion, physical pruning semantics, grouping, Mu/generated parents and the full pass remain open.
H6 constructed_node_calls remains the strongest combined semantic theorem.
The full formalization goal remains active. Remote publication still needs fresh approval.
''')
print(json.dumps({'status': 'PASS', 'previous_local_files': len(names), 'proof_jobs': 0,
    'baseline_files': len(baseline), 'older_non_audit_lean': 3631, 'haskell': 298,
    'package': 207, 'expected_frozen_registries': 300, 'expected_frozen_entries': 1394,
    'publication': 'PENDING_USER_APPROVAL'}))
