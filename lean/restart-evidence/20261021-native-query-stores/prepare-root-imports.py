import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
official = ROOT / 'lean/.lake/build/lib/lean'
overlay = Path('/tmp/mcfta-native-query-stores-root-imports')
assert not overlay.exists()
overlay.mkdir()
relative = Path('MicroCFTA/SourceCurrentNativeRequestPositivePositions.olean')
artifact = HERE / 'stores/import-tree' / relative
digest = hashlib.sha256(artifact.read_bytes()).hexdigest()
assert digest == 'f0f776df28be85619fe0a6c91d8a5110e2de9da044666b9ae6f7a3760398a945'
count = 0
for source in official.rglob('*'):
    if source.is_dir():
        continue
    name = source.relative_to(official)
    target = overlay / name
    target.parent.mkdir(parents=True, exist_ok=True)
    target.symlink_to(artifact if name == relative else source)
    count += 1
assert (overlay / relative).resolve() == artifact.resolve()
layout = {'overlay': str(overlay), 'official_library': str(official),
          'official_entries': count, 'replacement': str(relative),
          'replacement_artifact': str(artifact), 'replacement_sha256': digest,
          'replacement_source_sha256': 'e9fe573b314f7e8e4bf65025bb29078165a61a5fa92168f3da65b852b47d4d52',
          'archive_external_tree': False,
          'reason': 'Lean resolves a package from the first directory that contains its root. A merged directory retains all other official imports.'}
(HERE / 'root-import-layout.json').write_text(json.dumps(layout, indent=2) + '\n')
print(json.dumps({'status': 'PASS', **layout}))
