import hashlib
import json
import shutil
from pathlib import Path

HERE = Path(__file__).resolve().parent
components = [
    ('mcfta-cold-return-warm-entry-assessment', 'warm-entry-assessment'),
    ('mcfta-warm-return-node-closure-audit', 'closure-plan-review'),
    ('mcfta-warm-return-origins-plan', 'origins-plan'),
    ('mcfta-warm-return-origins-audit', 'origins-plan-review'),
    ('mcfta-warm-return-closure-proof', 'closure-owner'),
    ('mcfta-warm-return-origins-proof', 'origins-owner'),
    ('mcfta-warm-return-closure-candidate-audit', 'closure-source-review'),
    ('mcfta-warm-return-origins-candidate-audit', 'origins-source-review'),
    ('mcfta-warm-return-closure-accepted-audit', 'closure-accepted-review'),
    ('mcfta-warm-return-origins-accepted-audit', 'origins-accepted-review'),
    ('mcfta-finite-warm-count-mass-assessment', 'next-count-assessment'),
    ('mcfta-finite-warm-count-mass-audit', 'next-count-review'),
]
manifest = {}
for source, name in components:
    original, target = Path('/tmp') / source, HERE / name
    assert original.is_dir() and not target.exists()
    shutil.copytree(original, target)
    files = {}
    for path in sorted(target.rglob('*')):
        if path.is_file():
            relative = path.relative_to(target)
            assert path.read_bytes() == (original / relative).read_bytes()
            files[str(relative)] = hashlib.sha256(path.read_bytes()).hexdigest()
    manifest[name] = files
(HERE / 'archived-components.json').write_text(json.dumps(manifest, indent=2) + '\n')
previous = HERE / 'previous-publication-support'
previous.mkdir()
for pattern in ['mcfta-cold-rank-capacity-publication.json',
                'mcfta-cold-rank-capacity-final-publication*',
                'mcfta-cold-rank-capacity-final-push.log',
                'mcfta-cold-rank-capacity-final-remote.txt',
                'mcfta-cold-rank-capacity-board-*.json']:
    found = [path for path in Path('/tmp').glob(pattern) if path.is_file()]
    assert found, pattern
    for source in found:
        shutil.copyfile(source, previous / source.name)
print(json.dumps({'status': 'PASS', 'components': len(manifest),
                  'archived_files': sum(map(len, manifest.values()))}))
