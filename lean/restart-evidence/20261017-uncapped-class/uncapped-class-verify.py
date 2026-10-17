"""Verify initial uncapped Class/Fold/Pass/Caller production and imported checks."""
import hashlib
import json
from pathlib import Path
import re
p=Path(__file__).resolve().parent
root=p.parents[2]
m=json.loads((p/"uncapped-class-manifest.json").read_text())
assert len(m["entries"])==m["entry_count"]
for e in m["entries"]:
    b=(root/e["path"]).read_bytes()
    assert len(b)==e["bytes"] and hashlib.sha256(b).hexdigest()==e["sha256"],e
for module,attempt,canonical,jobs in [("SourceCurrentClassNumeric","class-direct-2","class-canonical-1.log",1570),("SourceCurrentClassPassNumeric","class-pass-direct-1","class-pass-canonical-1.log",1571),("SourceCurrentClassCallerNumeric","class-caller-direct-1","class-caller-canonical-1.log",1585)]:
    src=(root/("lean/MicroCFTA/"+module+".lean")).read_bytes()
    assert src==(p/(attempt+".source.lean")).read_bytes()
    assert (p/(attempt+".log")).stat().st_size==0
    assert f"Build completed successfully ({jobs} jobs)" in (p/canonical).read_text()
    text=src.decode()
    for absent in ["(depth : Nat)","(caps :","(bounded :","(merged :","MixedShared.Stored","Cap Plain"]:
        assert absent not in text,(module,absent)
for name,pairs in [("uncapped-class-public-1",4),("uncapped-class-kernels-2",3)]:
    source=(p/(name+".source.lean")).read_text();log=(p/(name+".log")).read_text()
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
for name in ["class-direct-1","uncapped-class-kernels-1"]:
    assert "error:" in (p/(name+".log")).read_text()
k=(p/"uncapped-class-kernels-2.source.lean").read_text()
for fragment in ["constructed_uncapped_class","constructed_uncapped_caller","constructed_empty_caller","private def records := [record, record]","no_cap","forest_open","selected_domains","exists_room","SourceCurrentClassNumeric.complete","SourceCurrentClassCallerNumeric.complete"]:
    assert fragment in k,fragment
print(f"PASS: {m['entry_count']} hashes; three strict empty; canonical1570/1571/1585; public4 + initial integrations3")
