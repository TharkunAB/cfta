import datetime
import hashlib
import json
import shutil
from pathlib import Path

HERE = Path(__file__).resolve().parent
assert (HERE / 'starting-head.txt').read_text().strip() == '108bc09e803b90b5e2e790c796d7ffd3c1d2f39f'
assert len(json.loads((HERE / 'starting-files.json').read_text())) == 82469
report = json.loads(Path('/tmp/mcfta-original-row-edge-completion-local-publication.json').read_text())
assert report['status'] == 'LOCAL_PASS' and report['clean'] and report['filesystem_index_head_equal']
assert report['checkpoint'] == '108bc09e803b90b5e2e790c796d7ffd3c1d2f39f'
assert report['publication'] == 'PENDING_FRESH_USER_APPROVAL_AFTER_AUTOMATIC_REVIEW_REJECTION'
previous = Path('/tmp/mcfta-direct-edge-word-ranges-previous-local-checkpoint')
assert not previous.exists()
previous.mkdir()
names = []
for stem in ['support-1', 'seal-1', 'local-finalize-1']:
    names += ['mcfta-original-row-edge-completion-' + stem + suffix
              for suffix in ['.json', '.log', '.limits.json', '.peaks.txt', '.source.py', '.usage.json']]
names += ['mcfta-original-row-edge-completion-' + tail for tail in [
    'local-publication.json', 'publication-risk-verification.json', 'finalize-local.py',
    'board-request.json', 'board-reply.json', 'board-readback.json']]
pins = {}
for name in names:
    source = Path('/tmp') / name
    assert source.is_file(), name
    shutil.copyfile(source, previous / name)
    pins[name] = hashlib.sha256(source.read_bytes()).hexdigest()
(previous / 'publication-blocker.md').write_text('''# Previous checkpoint publication status

H11 is committed locally at 108bc09e803b90b5e2e790c796d7ffd3c1d2f39f.
Its proof commit is 26a01918be8b5a4b2232dbabe3d1ccb8b51a14da.
Automatic approval review rejected the publisher before execution twice.
The stated reasons concerned remote ownership and authorization to export
this exact payload to git@github.com:TharkunAB/cfta.git formalize.
Read-only remote checks matched the previous formalize and main records.
The local finalizer then committed the complete sealed checkpoint.
It ran no network command. The tree was clean and FS=index=HEAD.
The board post and exact readback correctly state publication pending.
The user has been asked for fresh approval. No approval has arrived.
An automatic goal continuation does not supply this approval.
Do not retry the rejected push without direct user approval.
Local formalization can continue while publication remains pending.
''')
pins['publication-blocker.md'] = hashlib.sha256((previous / 'publication-blocker.md').read_bytes()).hexdigest()
(previous / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
assert not (HERE / 'archived-components.json').exists()
(HERE / 'archived-components.json').write_text('{}\n')
timestamp = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
(HERE / 'current-progress.md').write_text(f'''# Direct edge-body word ranges

Updated: {timestamp}.

Previous H11 checkpoint made progress and is committed locally at
108bc09e803b90b5e2e790c796d7ffd3c1d2f39f. Publication remains pending
fresh user approval after two automatic review rejections.
The current pull reports Already up to date.
All 82469 baseline tracked blobs and modes match the starting commit.
The root draft retains the reviewed exact contract and has no proof check yet.
It aims to derive every raw prefix WordRanges at the same current state.
It assumes no future success, instruction fuel or semantic completion.
The source/current capacity and readiness premises remain explicit.
H6 constructed_node_calls remains the strongest combined semantic theorem.
The full public pass, convergence and Haskell correspondence remain open.
No Haskell source or repair changes. The whole formalization goal stays active.
''')
print(json.dumps({'status': 'PASS', 'previous_local_files': len(names), 'proof_jobs': 0,
                  'publication': 'PENDING_USER_APPROVAL'}))
