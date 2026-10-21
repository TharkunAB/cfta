import hashlib
import json
import shutil
from pathlib import Path

HERE = Path(__file__).resolve().parent
components = [
    ('mcfta-count-mass-bound-plan', 'count-plan'),
    ('mcfta-count-mass-bound-plan-audit', 'count-plan-review'),
    ('mcfta-count-mass-bound-proof', 'count-initial-source'),
    ('mcfta-count-mass-bound-candidate-audit', 'count-initial-source-review'),
    ('mcfta-count-mass-bound-repair-1', 'count-repair-1'),
    ('mcfta-count-mass-bound-repair-1-audit', 'count-repair-1-review'),
    ('mcfta-count-mass-bound-repair-2', 'count-repair-2'),
    ('mcfta-finite-round-forecast-plan', 'finite-plan'),
    ('mcfta-finite-round-forecast-plan-audit', 'finite-plan-review'),
    ('mcfta-finite-round-forecast-proof', 'finite-initial-source'),
    ('mcfta-finite-round-forecast-repair-1', 'finite-repair-1'),
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
for pattern in ['mcfta-warm-return-publication.json',
                'mcfta-warm-return-final-publication*',
                'mcfta-warm-return-final-push.log',
                'mcfta-warm-return-final-remote.txt',
                'mcfta-warm-return-seal-1.*',
                'mcfta-warm-return-support-1.*',
                'mcfta-warm-return-board-*.json']:
    found = [path for path in Path('/tmp').glob(pattern) if path.is_file()]
    assert found, pattern
    for source in found:
        shutil.copyfile(source, previous / source.name)
print(json.dumps({'status': 'PASS', 'components': len(manifest),
                  'archived_files': sum(map(len, manifest.values()))}))
