import hashlib
import json
import shutil
from pathlib import Path

HERE = Path(__file__).resolve().parent
assert (HERE / 'starting-head.txt').read_text().strip() == '47c597a8e39cb82aa158a9fca104ed41b24849ef'
assert len(json.loads((HERE / 'starting-files.json').read_text())) == 81460
report = json.loads(Path('/tmp/mcfta-same-symbol-edge-ready-publication.json').read_text())
assert report['status'] == 'PASS' and report['clean'] and report['filesystem_index_head_equal']
assert report['checkpoint'] == '47c597a8e39cb82aa158a9fca104ed41b24849ef'
previous = Path('/tmp/mcfta-original-row-edge-completion-previous-publication')
previous.mkdir()
names = []
for stem in ['support-1', 'seal-1', 'publish-1']:
    names += ['mcfta-same-symbol-edge-ready-' + stem + suffix
              for suffix in ['.json', '.log', '.limits.json', '.peaks.txt', '.source.py', '.usage.json']]
names += ['mcfta-same-symbol-edge-ready-' + tail for tail in [
    'publication.json', 'final-push.log', 'final-remote.txt',
    'board-request.json', 'board-reply.json', 'board-readback.json']]
pins = {}
for name in names:
    source = Path('/tmp') / name
    assert source.is_file(), name
    shutil.copyfile(source, previous / name)
    pins[name] = hashlib.sha256(source.read_bytes()).hexdigest()
(previous / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
erratum = Path('/tmp/mcfta-original-row-edge-completion-plan-audit-timestamp-erratum.json').read_bytes()
assert hashlib.sha256(erratum).hexdigest() == 'cb393559f0313211655ec6d86b761af5cf382cbdd3019e49ef76b3bd23fdff7e'
(HERE / 'plan-audit-timestamp-erratum.json').write_bytes(erratum)
assert not (HERE / 'archived-components.json').exists()
(HERE / 'archived-components.json').write_text('{}\n')
print(json.dumps({'status': 'PASS', 'previous_publication_files': len(names), 'proof_jobs': 0}))
