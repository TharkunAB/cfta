import hashlib
import json
import shutil
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
here = root / 'lean/restart-evidence/20261020-native-generated-row-capture-backedge'
components = [
    ('/tmp/mcfta-native-generated-row-capture-backedge', 'backedge-module',
     'generated-row-backedge-manifest.json',
     '19a8d4fa8ae47ae5ad157d7f5662546a2f4c762183737d1051c4124c46410bbb'),
    ('/tmp/mcfta-native-generated-row-backedge-core', 'backedge-core',
     'generated-backedge-manifest.json',
     '64a861d37a94b7caf61084f96fd42763370a16f868067cf7d70bd9bffdceb6cc'),
    ('/tmp/mcfta-native-generated-row-capture-backedge-math-review', 'source-review',
     'math-review-manifest.json',
     '2df6ff33ea91c48ec7a0858d1b8b96471b1ac6f746e4e42d1ce2e4e1a58b7a9e'),
]
report = []
for source, destination, manifest, digest in components:
    source = Path(source)
    assert hashlib.sha256((source / manifest).read_bytes()).hexdigest() == digest
    destination = here / destination
    assert not destination.exists()
    shutil.copytree(source, destination)
    assert hashlib.sha256((destination / manifest).read_bytes()).hexdigest() == digest
    report.append({'path': str(destination.relative_to(here)), 'manifest': manifest,
                   'manifest_sha256': digest})
for extension in ['json', 'log', 'limits.json', 'peaks.txt', 'source.py', 'usage.json']:
    shutil.copyfile('/tmp/mcfta-backedge-archive-previous-1.' + extension,
                    here / ('archive-previous-run.' + extension))
proof = '57fe78e0e5f0d127f8ee350a6a485b8e2636e594'
(here / 'proof-commit.txt').write_text(proof + '\n')
(here / 'archived-components.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'components': report, 'proof_commit': proof}))
