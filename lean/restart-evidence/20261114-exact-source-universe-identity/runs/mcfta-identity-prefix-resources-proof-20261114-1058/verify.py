from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parent
manifest=json.loads((root/"MANIFEST.json").read_text())
for item in manifest["payloads"]:
 data=(root/item["name"]).read_bytes()
 assert len(data)==item["bytes"],item["name"]
 assert hashlib.sha256(data).hexdigest()==item["sha256"],item["name"]
check=json.loads((root/"HEADER-CHECK.json").read_text())
source=(root/check["final_candidate"]).read_text()
start=source.index("theorem prefix_identity_complete_resources\n")
end=source.index(" := by",start)
assert source[start:end]==(root/"APPROVED-HEADER.txt").read_text().rstrip()
assert hashlib.sha256(source.encode()).hexdigest()==check["final_sha256"]
print(f"PASS: {len(manifest['payloads'])} payloads and exact approved header")
