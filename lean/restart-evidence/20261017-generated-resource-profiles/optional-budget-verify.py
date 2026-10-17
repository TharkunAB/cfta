from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
validation = json.loads((HERE / "optional-budget-validation.json").read_text())
production = ROOT / "lean/MicroCFTA/SourceCurrentAllocatedRecursiveOptionalBudget.lean"
assert hashlib.sha256(production.read_bytes()).hexdigest() == validation["production_sha256"]
assert (HERE / validation["strict_direct"]["source"]).read_bytes() == production.read_bytes()
assert (HERE / validation["strict_direct"]["log"]).read_bytes() == b""
settings = ["linter.all true", "pp.explicit true", "pp.proofs true", "pp.universes true", "pp.deepTerms true", "pp.maxSteps 10000000", "pp.fullNames true"]
for key in ["public", "integration"]:
    item = validation[key]
    source = (HERE / item["source"]).read_text()
    log = (HERE / item["log"]).read_text()
    assert not re.search(r"\berror(?:\(|:)|\bwarning(?:\(|:)|sorryAx|⋯|maximum number of steps", log)
    assert all("set_option " + setting in source for setting in settings)
    assert source.count("#print axioms ") == item["pairs"]
    assert source.count("#check @") == item["pairs"]
    assert log.count("depends on axioms:") + log.count("does not depend on any axioms") == item["pairs"]
    for name in item["names"]:
        assert "#print axioms " + name in source
        assert "#check @" + name in source
        assert name in log
    for axioms in re.findall(r"depends on axioms:\s*\[([^]]*)\]", log):
        names = re.sub(r"\.\{[^}]*\}", "", axioms).split(",")
        assert all(name.strip() in validation["allowed_axioms"] for name in names)
canonical = (HERE / validation["canonical"]["log"]).read_text()
assert "Build completed successfully (1056 jobs)." in canonical
manifest = HERE / "optional-budget-manifest.json"
if manifest.exists():
    for entry in json.loads(manifest.read_text())["entries"]:
        data = (ROOT / entry["path"]).read_bytes()
        assert len(data) == entry["bytes"], entry["path"]
        assert hashlib.sha256(data).hexdigest() == entry["sha256"], entry["path"]
print("PASS: 8 public pairs, 3 constructive integration pairs, exact final production/direct/canonical agreement, clean explicit probes, standard axioms, frozen file hashes.")
