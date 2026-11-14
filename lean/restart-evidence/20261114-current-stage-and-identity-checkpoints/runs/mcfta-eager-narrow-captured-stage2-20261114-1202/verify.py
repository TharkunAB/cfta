from pathlib import Path
import hashlib,json,importlib.util,sys
sys.dont_write_bytecode=True
root=Path(__file__).resolve().parent
pins=json.loads((root/"PINS.json").read_text())
assert hashlib.sha256((root/"MANIFEST.json").read_bytes()).hexdigest()==pins["manifest_sha256"]
manifest=json.loads((root/"MANIFEST.json").read_text())
for item in manifest["payloads"]:
 data=(root/item["name"]).read_bytes()
 assert len(data)==item["bytes"],item["name"]
 assert hashlib.sha256(data).hexdigest()==item["sha256"],item["name"]
spec=importlib.util.spec_from_file_location("stage2_metadata_replay",root/"patch_replay.py")
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
a=(root/"SourcePruningEnumerationSharedEagerReservation-stage2-before.lean").read_text()
b=(root/"SourcePruningEnumerationSharedEagerReservation-stage2-UNCOMPILED.lean").read_text()
p=(root/"stage2.patch").read_text()
assert module.replay(a,p)==b
assert module.replay(b,p,True)==a
h=(root/"OLD-eager_captured_resources-HEADER.txt").read_text().rstrip()
for source in [a,b]:
 assert source[source.index("private theorem eager_captured_resources\n"):].startswith(h+" := by\n")
assert a[:a.index("section ActualCapturedResources\n")]==b[:b.index("section ActualCapturedResources\n")]
assert a[a.index("\nend ActualCapturedResources"):]==b[b.index("\nend ActualCapturedResources"):]
print(f"PASS: {len(manifest['payloads'])} payloads, exact header, untouched regions, forward/inverse replay")
