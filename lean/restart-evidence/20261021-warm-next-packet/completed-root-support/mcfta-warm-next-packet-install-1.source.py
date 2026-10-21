import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
name = 'SourceCurrentWarmNextPacket'
source = (HERE / (name + '.lean')).read_bytes()
sha = hashlib.sha256(source).hexdigest()
assert sha == '13e8373cff925aca8832a47e12514767dd94dbe3fdb8d68bd73b2cdf19246be8'
assert len(source.splitlines()) == 117
assert source == (HERE / 'warm-packet-strict-1.source.lean').read_bytes()
assert (HERE / 'warm-packet-strict-1.log').read_bytes() == b''
assert json.loads((HERE / 'warm-packet-public-1.json').read_text())['exit_code'] == 0
review = json.loads((HERE / 'root-full-review.json').read_text())
assert review['source_sha256'] == sha
assert review['complete_public_type_root_review'] == 'CLEAR'
assert review['independent_complete_public_type_review'] == 'CLEAR'
assert review['official_install_authorized'] is True
target = ROOT / ('lean/MicroCFTA/' + name + '.lean')
assert not target.exists()
audit = ROOT / 'lean/MicroCFTA/Audit.lean'
original = audit.read_bytes()
assert hashlib.sha256(original).hexdigest() == 'dde44b93bbc658d4aa7decec70afff57c6680b0878df6af7c510325006067a0a'
assert len(original.splitlines()) == 3109
archive = HERE / 'original-sources'
archive.mkdir()
(archive / 'Audit.original.lean.txt').write_bytes(original)
addition = b'import MicroCFTA.SourceCurrentWarmNextPacket\n'
assert addition not in original
target.write_bytes(source)
audit.write_bytes(original.replace(b'/-!', addition + b'/-!', 1))
path = 'lean/MicroCFTA/' + name + '.lean'
selected = {path: dict(sha256=sha, lines=117, strict='warm-packet-strict-1', full='warm-packet-public-1')}
(HERE / 'selected-sources.json').write_text(json.dumps(selected, indent=2) + '\n')
(HERE / 'frozen-modules.json').write_text(json.dumps({name: sha}, indent=2) + '\n')
(HERE / 'original-source-index.json').write_text(json.dumps({'sources': [dict(path='lean/MicroCFTA/Audit.lean',
    snapshot='original-sources/Audit.original.lean.txt', lines=3109,
    sha256=hashlib.sha256(original).hexdigest())]}, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'installed_module': path, 'audit_only_new_import': True}))
