from pathlib import Path
import hashlib, json
root = Path(__file__).resolve().parent
manifest = json.loads((root / "MANIFEST.json").read_text())
for item in manifest["payloads"]:
    data = (root / item["name"]).read_bytes()
    assert len(data) == item["bytes"], item["name"]
    assert hashlib.sha256(data).hexdigest() == item["sha256"], item["name"]
assert json.loads((root / "HEADER-CHECKS.json").read_text())["full_initializer_conclusion_prefix_byte_identical"]
print(f"PASS: {len(manifest['payloads'])} retained payloads")
