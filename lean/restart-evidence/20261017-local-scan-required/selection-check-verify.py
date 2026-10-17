"""Verify the independent finite positional selection forecast review."""
import hashlib
import json
from pathlib import Path
import re
p=Path(__file__).resolve().parent
root=p.parents[2]
m=json.loads((p/"selection-check-manifest.json").read_text())
assert len(m["entries"])==m["entry_count"]
for e in m["entries"]:
    b=(root/e["path"]).read_bytes()
    assert len(b)==e["bytes"] and hashlib.sha256(b).hexdigest()==e["sha256"],e
assert (root/"lean/MicroCFTA/SourceCurrentInitialSelectionForecast.lean").read_bytes()==(p/"selection-forecast-direct-2.source.lean").read_bytes()
assert (p/"selection-forecast-direct-2.log").stat().st_size==0
assert "Build completed successfully (1597 jobs)" in (p/"selection-forecast-canonical-1.log").read_text()
for name,pairs in [("selection-check-public-1",17),("selection-check-kernels-1",2)]:
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
k=(p/"selection-check-kernels-1.source.lean").read_text()
for fragment in ["private def original := [record, record]","[[], [record], [record], original]","length = 4","all_initial_choices","required_selected","required_reader_selected","class_profile_selected","class_fuel_selected"]:
    assert fragment in k,fragment
print(f"PASS: {m['entry_count']} hashes; root strict empty/canonical1597; public17 + pure fixtures2")
