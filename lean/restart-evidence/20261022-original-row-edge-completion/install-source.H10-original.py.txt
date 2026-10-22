import difflib
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
name = 'SourceCurrentSameSymbolEdgeReady'
source = (HERE / (name + '.lean')).read_bytes()
sha = hashlib.sha256(source).hexdigest()
assert sha == '68d9ca87569a4bb4ad3d2df6e928c441a4e218bf54154c1da9f4d14de6b2c8aa'
assert len(source.splitlines()) == 192
assert source == (HERE / 'same-symbol-edge-ready-strict-2.source.lean').read_bytes()
assert (HERE / 'same-symbol-edge-ready-strict-2.log').read_bytes() == b''
assert json.loads((HERE / 'same-symbol-edge-ready-public-1.json').read_text())['exit_code'] == 0
review = json.loads((HERE / 'root-full-review.json').read_text())
assert review['source_sha256'] == sha
assert review['complete_public_type_root_review'] == 'CLEAR'
assert review['independent_complete_public_type_review'] == 'CLEAR'
assert review['official_install_authorized'] is True
target = ROOT / ('lean/MicroCFTA/' + name + '.lean')
assert not target.exists()
audit = ROOT / 'lean/MicroCFTA/Audit.lean'
original = audit.read_bytes()
assert hashlib.sha256(original).hexdigest() == 'a36b1f2aefc14b99db041f7b8c40c6c3acc79db4f563b87532fda88b24d392fc'
assert len(original.splitlines()) == 3115
old = (HERE.parent / '20261022-same-symbol-edge-stable-memo/install-source.py').read_bytes()
(HERE / 'install-source.H9-original.py.txt').write_bytes(old)
(HERE / 'install-source.patch').write_text(''.join(difflib.unified_diff(old.decode().splitlines(keepends=True), Path(__file__).read_text().splitlines(keepends=True), fromfile='H9-install', tofile='H10-install')))
archive = HERE / 'original-sources'
archive.mkdir()
(archive / 'Audit.original.lean.txt').write_bytes(original)
addition = b'import MicroCFTA.SourceCurrentSameSymbolEdgeReady\n'
assert addition not in original
target.write_bytes(source)
audit.write_bytes(original.replace(b'/-!', addition + b'/-!', 1))
path = 'lean/MicroCFTA/' + name + '.lean'
selected = {path: dict(sha256=sha, lines=192, strict='same-symbol-edge-ready-strict-2', full='same-symbol-edge-ready-public-1')}
(HERE / 'selected-sources.json').write_text(json.dumps(selected, indent=2) + '\n')
(HERE / 'frozen-modules.json').write_text(json.dumps({name: sha}, indent=2) + '\n')
snapshots = HERE / 'selected-sources'
snapshots.mkdir()
(snapshots / (name + '.lean')).write_bytes(source)
(HERE / 'selected-source-gate.json').write_text(json.dumps(dict(status='ROOT_ACCEPTED', path=path,
    sha256=sha, lines=192, snapshot='selected-sources/' + name + '.lean'), indent=2) + '\n')
(HERE / 'original-source-index.json').write_text(json.dumps({'sources': [dict(path='lean/MicroCFTA/Audit.lean',
    snapshot='original-sources/Audit.original.lean.txt', lines=3115,
    sha256=hashlib.sha256(original).hexdigest())]}, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'installed_module': path, 'audit_only_new_import': True}))
