import difflib
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
name = 'SourceCurrentSameSymbolEdgeOriginalRows'
source = (HERE / (name + '.lean')).read_bytes()
sha = hashlib.sha256(source).hexdigest()
assert sha == '9d8af23bc2bbdd97f462a34b4d786d772a55bebf243dd585187b25630ac6440b'
assert len(source.splitlines()) == 174
assert source == (HERE / 'same-symbol-edge-original-rows-strict-1.source.lean').read_bytes()
assert (HERE / 'same-symbol-edge-original-rows-strict-1.log').read_bytes() == b''
assert json.loads((HERE / 'same-symbol-edge-original-rows-public-1.json').read_text())['exit_code'] == 0
review = json.loads((HERE / 'root-full-review.json').read_text())
assert review['source_sha256'] == sha
assert review['complete_public_type_root_review'] == 'CLEAR'
assert review['independent_complete_public_type_review'] == 'CLEAR'
assert review['official_install_authorized'] is True
target = ROOT / ('lean/MicroCFTA/' + name + '.lean')
assert not target.exists()
audit = ROOT / 'lean/MicroCFTA/Audit.lean'
original = audit.read_bytes()
assert hashlib.sha256(original).hexdigest() == '7a723653274a2fcbd82a74d4c83e6104bbbda1da660b7cc6e6393ce9c3ce34b2'
assert len(original.splitlines()) == 3118
old = (HERE.parent / '20261022-direct-edge-word-ranges/install-source.py').read_bytes()
(HERE / 'install-source.H12-original.py.txt').write_bytes(old)
(HERE / 'install-source.patch').write_text(''.join(difflib.unified_diff(old.decode().splitlines(keepends=True), Path(__file__).read_text().splitlines(keepends=True), fromfile='H12-install', tofile='H13-install')))
archive = HERE / 'original-sources'
archive.mkdir()
(archive / 'Audit.original.lean.txt').write_bytes(original)
addition = b'import MicroCFTA.SourceCurrentSameSymbolEdgeOriginalRows\n'
assert addition not in original
target.write_bytes(source)
audit.write_bytes(original.replace(b'/-!', addition + b'/-!', 1))
path = 'lean/MicroCFTA/' + name + '.lean'
selected = {path: dict(sha256=sha, lines=174, strict='same-symbol-edge-original-rows-strict-1', full='same-symbol-edge-original-rows-public-1')}
(HERE / 'selected-sources.json').write_text(json.dumps(selected, indent=2) + '\n')
(HERE / 'frozen-modules.json').write_text(json.dumps({name: sha}, indent=2) + '\n')
snapshots = HERE / 'selected-sources'
snapshots.mkdir()
(snapshots / (name + '.lean')).write_bytes(source)
(HERE / 'selected-source-gate.json').write_text(json.dumps(dict(status='ROOT_ACCEPTED', path=path,
    sha256=sha, lines=174, snapshot='selected-sources/' + name + '.lean'), indent=2) + '\n')
(HERE / 'original-source-index.json').write_text(json.dumps({'sources': [dict(path='lean/MicroCFTA/Audit.lean',
    snapshot='original-sources/Audit.original.lean.txt', lines=3118,
    sha256=hashlib.sha256(original).hexdigest())]}, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'installed_module': path, 'audit_only_new_import': True}))
