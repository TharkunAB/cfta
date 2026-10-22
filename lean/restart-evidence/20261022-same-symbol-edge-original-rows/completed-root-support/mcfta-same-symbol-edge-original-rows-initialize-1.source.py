import datetime
import hashlib
import json
import shutil
from pathlib import Path

HERE = Path(__file__).resolve().parent
START = 'c49dd66acf3beecbead06219f10f125a43b3925d'
assert (HERE / 'starting-head.txt').read_text().strip() == START
assert len(json.loads((HERE / 'starting-files.json').read_text())) == 83325
report = json.loads(Path('/tmp/mcfta-direct-edge-word-ranges-local-publication.json').read_text())
assert report['status'] == 'LOCAL_PASS' and report['clean'] and report['filesystem_index_head_equal']
assert report['checkpoint'] == START and report['publication'] == 'PENDING_USER_APPROVAL'
assert report['network_commands_executed'] == 0
previous = Path('/tmp/mcfta-same-symbol-edge-original-rows-previous-local-checkpoint')
assert not previous.exists()
previous.mkdir()
names = []
for stem in ['support-1', 'seal-1', 'local-publication-1']:
    names += ['mcfta-direct-edge-word-ranges-' + stem + suffix
              for suffix in ['.json', '.log', '.limits.json', '.peaks.txt', '.source.py', '.usage.json']]
names += ['mcfta-direct-edge-word-ranges-' + tail for tail in [
    'local-publication.json', 'board-request.json', 'board-reply.json', 'board-readback.json']]
pins = {}
for name in names:
    source = Path('/tmp') / name
    assert source.is_file(), name
    shutil.copyfile(source, previous / name)
    pins[name] = hashlib.sha256(source.read_bytes()).hexdigest()
note = '''# Previous checkpoint publication status

H12 is committed locally at c49dd66acf3beecbead06219f10f125a43b3925d.
Its proof commit is 3ad63b6b3971479814f1ff480f6bc7f39747af28.
Its local publisher performed no network command. FS=index=HEAD and the tree was clean.
The exact board post and readback state that publication remains pending.
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
(HERE / 'current-progress.md').write_text(f'''# Original-row native comparison composition

Updated: {timestamp}.

H12 made progress and is committed locally at {START}.
The current pull reports Already up to date. All83325 starting tracked blobs and modes agree.
The reviewed future contract combines H11 semantic completion and H12 word ranges with H8/H9.
The proposed result includes actual comparison completion, final pair Stable and native Idle.
No new body has been checked at this cut. Current source/model/cache and Room assumptions remain.
Future success, a supplied Receipt, final Stable and post-call Room are not premises.
H6 constructed_node_calls remains the strongest combined semantic theorem.
The public pass, convergence, practical host bounds and Haskell correspondence remain open.
No Haskell source or repair changes. The whole formalization goal remains active.
Remote publication remains pending fresh user approval after automatic review rejected the push.
''')
print(json.dumps({'status': 'PASS', 'previous_local_files': len(names), 'proof_jobs': 0,
                  'publication': 'PENDING_USER_APPROVAL'}))
