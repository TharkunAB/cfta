"""Verify independent literal Scan/Required factorization and initial forecast checks."""
import hashlib
import json
from pathlib import Path
import re
p=Path(__file__).resolve().parent
root=p.parents[2]
m=json.loads((p/"prefix-forecast-check-manifest.json").read_text())
assert len(m["entries"])==m["entry_count"]
for e in m["entries"]:
    b=(root/e["path"]).read_bytes()
    assert len(b)==e["bytes"] and hashlib.sha256(b).hexdigest()==e["sha256"],e
for module,attempt,jobs in [("SourceCurrentScanRequiredWorker","scan-required-worker-direct-2",1405),("SourceCurrentScanRequiredForecast","scan-required-forecast-direct-1",1632)]:
    assert (root/("lean/MicroCFTA/"+module+".lean")).read_bytes()==(p/(attempt+".source.lean")).read_bytes()
    assert (p/(attempt+".log")).stat().st_size==0
    canonical=attempt.rsplit("-direct-",1)[0]+"-canonical-1.log"
    assert f"Build completed successfully ({jobs} jobs)" in (p/canonical).read_text()
for name,pairs in [("prefix-forecast-check-public-1",10),("prefix-forecast-check-kernels-7",4)]:
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
for i in range(1,7):
    assert "error:" in (p/f"prefix-forecast-check-kernels-{i}.log").read_text()
assert "error:" in (p/"prefix-forecast-check-reduce-1.log").read_text()
k=(p/"prefix-forecast-check-kernels-7.source.lean").read_text()
for fragment in ["theorem primary_failure","theorem required_failure","theorem empty_records_propagate","theorem initial_stage_order","[record, record]",".exhausted .worker","SourceCurrentScanRequiredWorker.classes","SourceCurrentInitialSelectionForecast.required_selected"]:
    assert fragment in k,fragment
print(f"PASS: {m['entry_count']} hashes; public10 + fixtures4; root strict empty; canonical1405/1632")
