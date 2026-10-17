"""Restore ignored raw logs from their exact committed compressed archives."""

import gzip
import hashlib
import json
from pathlib import Path
import shutil

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def digest(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


for item in json.loads((HERE / "compressed-evidence.json").read_text()):
    archive = ROOT / item["archive"]
    original = ROOT / item["original"]
    assert archive.stat().st_size == item["archive_bytes"]
    assert digest(archive) == item["archive_sha256"]
    if not original.exists():
        temporary = original.with_suffix(original.suffix + ".restore.tmp")
        try:
            with gzip.open(archive, "rb") as source, temporary.open("wb") as target:
                shutil.copyfileobj(source, target)
            assert temporary.stat().st_size == item["original_bytes"]
            assert digest(temporary) == item["original_sha256"]
            temporary.replace(original)
        finally:
            temporary.unlink(missing_ok=True)
    assert original.stat().st_size == item["original_bytes"]
    assert digest(original) == item["original_sha256"]

print("PASS: compressed archives and exact original raw logs verified")
