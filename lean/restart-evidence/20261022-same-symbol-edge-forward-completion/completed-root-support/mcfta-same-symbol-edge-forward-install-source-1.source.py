import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
name = 'SourceCurrentSameSymbolEdgeForwardCompletion'
source = (HERE / (name + '.lean')).read_bytes()
sha = hashlib.sha256(source).hexdigest()
assert sha == 'c1b7480244632c2cc0454051f0dc7f63649d9ed4cf3c2548edf615ff8647aafd'
assert len(source.splitlines()) == 216
assert source == (HERE / 'same-symbol-edge-forward-strict-3.source.lean').read_bytes()
assert (HERE / 'same-symbol-edge-forward-strict-3.log').read_bytes() == b''
assert json.loads((HERE / 'same-symbol-edge-forward-public-1.json').read_text())['exit_code'] == 0
review = json.loads((HERE / 'root-full-review.json').read_text())
assert review['source_sha256'] == sha
assert review['complete_public_type_root_review'] == 'CLEAR'
assert review['independent_complete_public_type_review'] == 'CLEAR'
assert review['official_install_authorized'] is True
target = ROOT / ('lean/MicroCFTA/' + name + '.lean')
assert not target.exists()
audit = ROOT / 'lean/MicroCFTA/Audit.lean'
original = audit.read_bytes()
assert hashlib.sha256(original).hexdigest() == '8f02e3994f8b7559692a36eab8e4d1ca0afb31f38485d59d0b5e802f376fa75f'
assert len(original.splitlines()) == 3113
archive = HERE / 'original-sources'
archive.mkdir()
(archive / 'Audit.original.lean.txt').write_bytes(original)
addition = b'import MicroCFTA.SourceCurrentSameSymbolEdgeForwardCompletion\n'
assert addition not in original
target.write_bytes(source)
audit.write_bytes(original.replace(b'/-!', addition + b'/-!', 1))
path = 'lean/MicroCFTA/' + name + '.lean'
selected = {path: dict(sha256=sha, lines=216, strict='same-symbol-edge-forward-strict-3', full='same-symbol-edge-forward-public-1')}
(HERE / 'selected-sources.json').write_text(json.dumps(selected, indent=2) + '\n')
(HERE / 'frozen-modules.json').write_text(json.dumps({name: sha}, indent=2) + '\n')
snapshots = HERE / 'selected-sources'
snapshots.mkdir()
(snapshots / (name + '.lean')).write_bytes(source)
(HERE / 'selected-source-gate.json').write_text(json.dumps(dict(status='ROOT_ACCEPTED', path=path,
    sha256=sha, lines=216, snapshot='selected-sources/' + name + '.lean'), indent=2) + '\n')
(HERE / 'original-source-index.json').write_text(json.dumps({'sources': [dict(path='lean/MicroCFTA/Audit.lean',
    snapshot='original-sources/Audit.original.lean.txt', lines=3113,
    sha256=hashlib.sha256(original).hexdigest())]}, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'installed_module': path, 'audit_only_new_import': True}))
