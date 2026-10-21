import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
name = 'SourceCurrentColdFiniteWarmCalls'
source = (HERE / (name + '.lean')).read_bytes()
sha = hashlib.sha256(source).hexdigest()
assert sha == 'e4665b0bb522ec88f1925fe6bc360b76e9e4bdfbe6192210ac708a3097a20cc5'
assert len(source.splitlines()) == 157
assert source == (HERE / 'cold-finite-calls-strict-2.source.lean').read_bytes()
assert (HERE / 'cold-finite-calls-strict-2.log').read_bytes() == b''
assert json.loads((HERE / 'cold-finite-calls-public-2.json').read_text())['exit_code'] == 0
review = json.loads((HERE / 'root-full-review.json').read_text())
assert review['source_sha256'] == sha
assert review['complete_public_type_root_review'] == 'CLEAR'
assert review['independent_complete_public_type_review'] == 'CLEAR'
assert review['official_install_authorized'] is True
target = ROOT / ('lean/MicroCFTA/' + name + '.lean')
assert not target.exists()
audit = ROOT / 'lean/MicroCFTA/Audit.lean'
original = audit.read_bytes()
assert hashlib.sha256(original).hexdigest() == 'd11e901227fa107e2b36ebd5a76f96f1f89f7f8f697e39be2907011648cf9487'
assert len(original.splitlines()) == 3111
archive = HERE / 'original-sources'
archive.mkdir()
(archive / 'Audit.original.lean.txt').write_bytes(original)
addition = b'import MicroCFTA.SourceCurrentColdFiniteWarmCalls\n'
assert addition not in original
target.write_bytes(source)
audit.write_bytes(original.replace(b'/-!', addition + b'/-!', 1))
path = 'lean/MicroCFTA/' + name + '.lean'
selected = {path: dict(sha256=sha, lines=157, strict='cold-finite-calls-strict-2', full='cold-finite-calls-public-2')}
(HERE / 'selected-sources.json').write_text(json.dumps(selected, indent=2) + '\n')
(HERE / 'frozen-modules.json').write_text(json.dumps({name: sha}, indent=2) + '\n')
(HERE / 'original-source-index.json').write_text(json.dumps({'sources': [dict(path='lean/MicroCFTA/Audit.lean',
    snapshot='original-sources/Audit.original.lean.txt', lines=3111,
    sha256=hashlib.sha256(original).hexdigest())]}, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'installed_module': path, 'audit_only_new_import': True}))
