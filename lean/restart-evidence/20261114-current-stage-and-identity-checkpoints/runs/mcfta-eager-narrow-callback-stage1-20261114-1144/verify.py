from pathlib import Path
import hashlib,json,importlib.util,sys
sys.dont_write_bytecode=True
root=Path(__file__).resolve().parent
manifest=json.loads((root/"MANIFEST.json").read_text())
for item in manifest["payloads"]:
 data=(root/item["name"]).read_bytes()
 assert len(data)==item["bytes"],item["name"]
 assert hashlib.sha256(data).hexdigest()==item["sha256"],item["name"]
spec=importlib.util.spec_from_file_location("retained_patch_replay",root/"patch_replay.py")
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
base=(root/"SourcePruningEnumerationSharedEagerReservation-before.lean").read_text()
check=json.loads((root/"STATIC-CHECKS.json").read_text())
source=(root/check["final_candidate"]).read_text()
patch=(root/check["final_patch"]).read_text()
assert module.replay(base,patch)==source
assert module.replay(source,patch,True)==base
for name,file,delimiter in [("private def EagerResumeComplete\n","OLD-EagerResumeComplete-HEADER.txt"," :=\n"),("private theorem callback_eager_induction_resources\n","OLD-callback_eager_induction_resources-HEADER.txt"," := by\n")]:
 header=(root/file).read_text().rstrip()
 for text in [base,source]:
  assert text[text.index(name):].startswith(header+delimiter)
assert base[:base.index("section ActualEagerCallback\n")]==source[:source.index("section ActualEagerCallback\n")]
assert base[base.index("\nend ActualEagerCallback\n"):]==source[source.index("\nend ActualEagerCallback\n"):]
print(f"PASS: {len(manifest['payloads'])} payloads, exact old headers, forward and inverse replay")
