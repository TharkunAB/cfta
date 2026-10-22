import difflib
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
name = 'SourceCurrentOriginalRowClusterScan'
source = (HERE / (name + '.lean')).read_bytes()
sha = hashlib.sha256(source).hexdigest()
assert sha == '37bcce3d4b04310f6e3c1e394e27a875baf98547f4078d1b3be7252c47d0a5f7'
assert len(source.splitlines()) == 129
assert source == (HERE / 'original-row-cluster-control-strict-2.source.lean').read_bytes()
assert (HERE / 'original-row-cluster-control-strict-2.log').read_bytes() == b''
assert json.loads((HERE / 'original-row-cluster-control-public-1.json').read_text())['exit_code'] == 0
review = json.loads((HERE / 'root-full-review.json').read_text())
assert review['source_sha256'] == sha
assert review['complete_public_type_root_review'] == 'CLEAR'
assert review['independent_complete_public_type_review'] == 'CLEAR'
assert review['official_install_authorized'] is True
target = ROOT / ('lean/MicroCFTA/' + name + '.lean')
assert not target.exists()
audit = ROOT / 'lean/MicroCFTA/Audit.lean'
original = audit.read_bytes()
assert hashlib.sha256(original).hexdigest() == '8587e6d6e10773d7e626ad5a51d3ba5f5739d731673616129765104b2a2af1f6'
assert len(original.splitlines()) == 3121
old = (HERE.parent / '20261022-same-symbol-edge-comparison-domains/install-source.py').read_bytes()
(HERE / 'install-source.H15-original.py.txt').write_bytes(old)
(HERE / 'install-source.patch').write_text(''.join(difflib.unified_diff(
    old.decode().splitlines(keepends=True), Path(__file__).read_text().splitlines(keepends=True),
    fromfile='H15-install', tofile='H16-install')))
archive = HERE / 'original-sources'
archive.mkdir()
(archive / 'Audit.original.lean.txt').write_bytes(original)
addition = b'import MicroCFTA.SourceCurrentOriginalRowClusterScan\n'
assert addition not in original
target.write_bytes(source)
audit.write_bytes(original.replace(b'/-!', addition + b'/-!', 1))
path = 'lean/MicroCFTA/' + name + '.lean'
selected = {path: dict(sha256=sha, lines=129,
    strict='original-row-cluster-control-strict-2', full='original-row-cluster-control-public-1')}
(HERE / 'selected-sources.json').write_text(json.dumps(selected, indent=2) + '\n')
(HERE / 'frozen-modules.json').write_text(json.dumps({name: sha}, indent=2) + '\n')
snapshots = HERE / 'selected-sources'
snapshots.mkdir()
(snapshots / (name + '.lean')).write_bytes(source)
assert not (HERE / 'selected-source-gate.json').exists()
(HERE / 'selected-source-gate.json').write_text(json.dumps(dict(status='ROOT_ACCEPTED', path=path,
    sha256=sha, lines=129, snapshot='selected-sources/' + name + '.lean'), indent=2) + '\n')
(HERE / 'original-source-index.json').write_text(json.dumps({'sources': [dict(path='lean/MicroCFTA/Audit.lean',
    snapshot='original-sources/Audit.original.lean.txt', lines=3121,
    sha256=hashlib.sha256(original).hexdigest())]}, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'installed_module': path, 'audit_only_new_import': True}))
