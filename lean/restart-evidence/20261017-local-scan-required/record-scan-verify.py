"""Verify the initial numeric record Scan component."""
import hashlib
import json
from pathlib import Path
import re
p=Path(__file__).resolve().parent
root=p.parents[2]
m=json.loads((p/"record-scan-manifest.json").read_text())
assert len(m["entries"])==m["entry_count"]
for e in m["entries"]:
    b=(root/e["path"]).read_bytes()
    assert len(b)==e["bytes"] and hashlib.sha256(b).hexdigest()==e["sha256"],e
assert (root/"lean/MicroCFTA/SourceCurrentRecordScanNumeric.lean").read_bytes()==(p/"record-scan-direct-2.source.lean").read_bytes()
assert (p/"record-scan-direct-2.log").stat().st_size==0
assert "Build completed successfully (1627 jobs)" in (p/"record-scan-canonical-1.log").read_text()
for name,pairs in [("record-scan-public-1",3),("record-scan-kernels-2",2)]:
    source=(p/(name+".source.lean")).read_text(); log=(p/(name+".log")).read_text()
    assert not re.search(r"error(?:\(|:)|warning(?:\(|:)|sorryAx|truncated|⋯|\.\.\.",log)
    assert len(re.findall(r"^#check @",source,re.M))==pairs
    assert len(re.findall(r"^#print axioms ",source,re.M))==pairs
    for opt in ["pp.explicit","pp.fullNames","pp.proofs","pp.universes","pp.deepTerms"]:
        assert "set_option "+opt+" true" in source
    assert "set_option pp.maxSteps 10000000" in source
    blocks=re.findall(r"depends on axioms: \[([^\]]*)\]",log,re.S)
    assert len(blocks)+log.count("does not depend on any axioms")==pairs
    for block in blocks:
        axioms={re.sub(r"\.\{[^}]+\}","",n.strip()) for n in block.split(",") if n.strip()}
        assert axioms<={"propext","Classical.choice","Quot.sound"},axioms
for name in ["record-scan-direct-1","record-scan-kernels-1"]:
    assert "error:" in (p/(name+".log")).read_text()
k=(p/"record-scan-kernels-2.source.lean").read_text()
for fragment in ["private def records := [record, record]","[[7], [8]]","exists_room","reserved_of_room","constructed_duplicate_records","constructed_empty_records","no_cap","SourceCurrentRecordScanNumeric.complete","scan_done_unique"]:
    assert fragment in k,fragment
print(f"PASS: {m['entry_count']} hashes; strict empty; canonical1627; public3 + constructed kernels2")
