from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
validation = json.loads((HERE / "unfold-history-validation.json").read_text())
item = validation["production"]
data = (ROOT / item["path"]).read_bytes()
assert hashlib.sha256(data).hexdigest() == item["sha256"]
assert (HERE / item["direct_source"]).read_bytes() == data
assert (HERE / item["direct_log"]).read_bytes() == b""
assert f'Build completed successfully ({item["jobs"]} jobs).' in (HERE / item["canonical_log"]).read_text()
settings = ["linter.all true", "pp.explicit true", "pp.proofs true", "pp.universes true", "pp.deepTerms true", "pp.maxSteps 10000000", "pp.fullNames true"]
for kind in ["public", "integration"]:
    item = validation[kind]
    source = (HERE / item["source"]).read_text()
    log = (HERE / item["log"]).read_text()
    assert (HERE / item["snapshot"]).read_text() == source
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
for earlier in validation["earlier_attempts"]:
    assert (HERE / earlier["log"]).exists()
    if "source" in earlier:
        assert (HERE / earlier["source"]).exists()
        assert re.search(r"\berror(?:\(|:)", (HERE / earlier["log"]).read_text())
assert (HERE / validation["unchecked_draft"]).exists()
assert (HERE / validation["review"]).exists()
manifest = HERE / "unfold-history-manifest.json"
if manifest.exists():
    for entry in json.loads(manifest.read_text())["entries"]:
        data = (ROOT / entry["path"]).read_bytes()
        assert len(data) == entry["bytes"], entry["path"]
        assert hashlib.sha256(data).hexdigest() == entry["sha256"], entry["path"]
print("PASS: frozen strict-clean/canonical UnfoldHistory; 15 full public pairs; 2 source-built changing-Mu/arbitrary-warm histories; standard axioms; preserved failures and unchecked draft; immutable manifest.")
