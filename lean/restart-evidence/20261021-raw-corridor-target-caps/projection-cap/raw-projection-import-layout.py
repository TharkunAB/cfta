import hashlib
import json
from pathlib import Path
import shutil

HERE = Path(__file__).resolve().parent
ROOT = Path('/home/tritlo/Code/mcfta')
LIBRARY = Path('/tmp/mcfta-raw-corridor-projection-imports')
RAW = Path('/tmp/mcfta-required-raw-corridor-proof/import-tree/MicroCFTA/SourceCurrentRequiredRawCorridor.olean')
RAW_SNAPSHOT = HERE / 'inputs/raw-dependency/SourceCurrentRequiredRawCorridor.olean'
RAW_SNAPSHOT.parent.mkdir(parents=True, exist_ok=True)
shutil.copyfile(RAW, RAW_SNAPSHOT)
modules = LIBRARY / 'MicroCFTA'
modules.mkdir(parents=True, exist_ok=True)
official = ROOT / 'lean/.lake/build/lib/lean/MicroCFTA'
links = {file.name: file for file in official.glob('*.olean')}
links[RAW.name] = RAW_SNAPSHOT
links['SourceCurrentRawCorridorProjectionCap.olean'] = HERE / 'import-tree/MicroCFTA/SourceCurrentRawCorridorProjectionCap.olean'
for name, target in links.items():
    link = modules / name
    if link.is_symlink():
        assert link.readlink() == target
    else:
        assert not link.exists()
        link.symlink_to(target)
report = {
    'library': str(LIBRARY),
    'official_root': 'lean/.lake/build/lib/lean/MicroCFTA',
    'official_link_count': len(list(official.glob('*.olean'))),
    'raw_snapshot': str(RAW_SNAPSHOT.relative_to(HERE)),
    'raw_sha256': hashlib.sha256(RAW_SNAPSHOT.read_bytes()).hexdigest(),
    'consumer_output': 'import-tree/MicroCFTA/SourceCurrentRawCorridorProjectionCap.olean',
    'external_tree_not_archived': True,
    'failed_first_lean_path': '/tmp/mcfta-required-raw-corridor-proof/import-tree:/home/tritlo/Code/mcfta/lean/.lake/build/lib/lean',
}
(HERE / 'raw-projection-import-layout.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
