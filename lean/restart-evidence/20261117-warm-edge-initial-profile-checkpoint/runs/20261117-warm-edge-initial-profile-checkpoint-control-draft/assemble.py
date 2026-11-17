from pathlib import Path
import gzip
import hashlib
import json
import os

ROOT = Path('/home/tritlo/Code/mcfta')
PACKET = ROOT / 'lean/restart-evidence/20261117-warm-edge-initial-profile-checkpoint'
RUNS = json.loads((Path(__file__).parent / 'archive-roots.json').read_text())
EXTRA = []
SKIP_DIRS = {'objects', 'raw-ghc', 'default-ghc', '.git', '__pycache__'}
SKIP_SUFFIXES = {'.olean', '.ilean', '.o', '.hi', '.a', '.so', '.dylib'}
records = []


def save(source: Path, relative: Path) -> None:
    if source.is_symlink() or not source.is_file() or source.suffix in SKIP_SUFFIXES:
        return
    for attempt in range(10):
        before = source.stat()
        data = source.read_bytes()
        after = source.stat()
        if (before.st_ino, before.st_size, before.st_mtime_ns) == (after.st_ino, after.st_size, after.st_mtime_ns) and len(data) == after.st_size:
            break
        import time
        time.sleep(0.05)
    else:
        raise RuntimeError(f'Input changed during snapshot: {source}')
    assert not data.startswith(b'\x7fELF'), source
    compressed = len(data) > 16384 or source.suffix == '.patch' or data.endswith(b'\n\n') or any(line.rstrip(b'\r\n').endswith((b' ', b'\t')) for line in data.splitlines(keepends=True))
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
for source in [ROOT / name for name in RUNS] + EXTRA:
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
