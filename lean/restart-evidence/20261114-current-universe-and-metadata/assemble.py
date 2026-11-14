from pathlib import Path
import gzip
import hashlib
import json
import os

ROOT = Path('/home/tritlo/Code/mcfta')
PACKET = ROOT / 'lean/restart-evidence/20261114-current-universe-and-metadata'
RUNS = [
    'mcfta-current-universe-prefix-check-20261114-0657',
    'mcfta-current-universe-prefix-publication-20261114-0701',
    'mcfta-current-labeled-universe-shape-review-20261114-070201',
    'mcfta-current-labeled-universe-body-draft-20261114-071508',
    'mcfta-current-labeled-universe-body-check-20261114-0727',
    'mcfta-current-labeled-universe-body-publication-20261114-0738',
    'mcfta-identity-child-cps-proof-repairs-20261114-0651',
    'mcfta-identity-captured-hook-proof-repair-20261114-0702',
    'mcfta-identity-worker-metadata-erasure-20261114-0739',
    'mcfta-identity-worker-proof-repairs-20261114-0806',
    'mcfta-identity-worker-prepared-option-repair-20261114-0828',
    'mcfta-identity-worker-metadata-erasure-check-20261114-0758',
    'mcfta-identity-worker-publication-20261114-0834',
    'mcfta-current-universe-ownership-draft-20261114-075226',
    'mcfta-current-universe-ownership-repair-20261114-082949',
    'mcfta-current-universe-ownership-check-20261114-0826',
    'mcfta-current-universe-ownership-publication-20261114-0840',
    'mcfta-current-first-universe-publication-draft-20261114-074526',
    'mcfta-proper-type-cycle-probe-20261114-0805',
]
CPS = Path('/tmp/mcfta-identity-child-cps-erasure-check-20261114-0639')
EXTRA = [CPS / name for name in ['check3', 'check4', 'check5']]
EXTRA += [Path('/tmp/mcfta-finite-completion-source-review-20261114-0754.md')]
SKIP_DIRS = {'objects', 'raw-ghc', 'default-ghc', '.git', '__pycache__'}
SKIP_SUFFIXES = {'.olean', '.ilean', '.o', '.hi', '.a', '.so', '.dylib'}
records = []


def save(source: Path, relative: Path) -> None:
    if source.is_symlink() or not source.is_file() or source.suffix in SKIP_SUFFIXES:
        return
    data = source.read_bytes()
    assert not data.startswith(b'\x7fELF'), source
    compressed = len(data) > 16384 or source.suffix == '.patch' or data.endswith(b'\n\n')
    target = PACKET / 'runs' / relative
    if compressed:
        target = target.with_name(target.name + '.gz')
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(gzip.compress(data, mtime=0) if compressed else data)
    records.append({'original': str(source), 'archived': str(target.relative_to(PACKET)),
                    'gzip': compressed, 'source_bytes': len(data),
                    'source_sha256': hashlib.sha256(data).hexdigest()})


assert not PACKET.exists()
PACKET.mkdir(parents=True)
for source in [Path('/tmp') / name for name in RUNS] + EXTRA:
    assert source.exists(), source
    if source.is_file():
        save(source, Path(source.name))
        continue
    prefix = Path(source.parent.name) / source.name if source in EXTRA else Path(source.name)
    for directory, dirs, files in os.walk(source, followlinks=False):
        dirs[:] = [name for name in dirs if name not in SKIP_DIRS
                   and not (Path(directory) / name).is_symlink()]
        for name in files:
            file = Path(directory) / name
            save(file, prefix / file.relative_to(source))

(PACKET / 'archived-inputs.json').write_text(json.dumps(records, indent=2) + '\n')
print(json.dumps({'packet': str(PACKET), 'archived_inputs': len(records),
                  'bytes': sum(p.stat().st_size for p in PACKET.rglob('*') if p.is_file())}))
