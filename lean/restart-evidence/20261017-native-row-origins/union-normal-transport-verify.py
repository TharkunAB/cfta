#!/usr/bin/env python3
from pathlib import Path
import hashlib
import json
import re

here = Path(__file__).resolve().parent
root = here.parents[2]
manifest = json.loads(here.joinpath("union-normal-transport-manifest.json").read_text())
for entry in manifest["entries"]:
    assert hashlib.sha256(root.joinpath(entry["path"]).read_bytes()).hexdigest() == entry["sha256"], entry["path"]
strict = [("union-normal-native-final-1","SourceCurrentRequiredUnionNormalNative"),
          ("union-normal-read-final-1","SourceCurrentRequiredUnionNormalRead"),
          ("union-normal-kernel-strict-1",None)]
monitored = [name for name, _ in strict] + ["union-normal-public-2","union-normal-kernels-2"]
for stem in monitored:
    assert json.loads(here.joinpath(stem+".json").read_text())["exit_code"] == 0, stem
    limits = json.loads(here.joinpath(stem+".limits.json").read_text())
    assert limits["memory.max"] == limits["memory.high"] == "4294967296", (stem,limits)
    assert limits["memory.swap.max"] == "0", (stem,limits)
    assert limits["cgroup"].startswith("/user.slice/")
for stem,module in strict:
    assert here.joinpath(stem+".log").stat().st_size == 0, stem
    if module:
        assert here.joinpath(stem+".source.lean").read_bytes() == root.joinpath("lean/MicroCFTA/"+module+".lean").read_bytes()
allowed = {"propext","Classical.choice","Quot.sound"}
options = ["pp.all true","pp.explicit true","pp.fullNames true","pp.proofs true",
           "pp.proofs.threshold 254","pp.universes true","pp.deepTerms true","pp.maxSteps 10000000"]
for stem,count,full in [("union-normal-public-2",17,True),("union-normal-kernels-2",2,False)]:
    source = here.joinpath(stem+".source.lean").read_text()
    for option in options: assert "set_option "+option in source, (stem,option)
    assert source.count("\n#check @") == count
    assert source.count("\n#print axioms ") == count
    if full:
        assert sum(line.startswith("#print ") and not line.startswith("#print axioms ") for line in source.splitlines()) == count
    log = here.joinpath(stem+".log").read_text()
    assert not re.search(r"warning:|error:|sorryAx|⋯|…|\.\.\.|truncat",log), stem
    blocks = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log)
    independent = re.findall(r"'([^']+)' does not depend on any axioms",log)
    assert len(blocks)+len(independent) == count, (stem,len(blocks),len(independent))
    for _,block in blocks:
        names = {re.sub(r"\.\{[^}]*\}","",name.strip()) for name in block.split(",")}
        assert names <= allowed, (stem,names)
kernel = here.joinpath("union-normal-kernels-2.source.lean").read_text()
assert kernel == here.joinpath("union-normal-kernels.lean").read_text()
assert kernel.split("\n#check",1)[0] == here.joinpath("union-normal-kernel-strict-1.source.lean").read_text()
for stem,jobs in [("union-normal-native-canonical-1",1305),("union-normal-read-canonical-1",768)]:
    meta = json.loads(here.joinpath(stem+".json").read_text())
    assert meta["exit"] == 0 and meta["jobs"] == jobs
    lines = here.joinpath(stem+".log").read_text().splitlines()
    assert lines[:3] == ["4294967296","4294967296","0"]
    assert f"Build completed successfully ({jobs} jobs)." in "\n".join(lines)
for stem in manifest["failed_attempts"]:
    assert json.loads(here.joinpath(stem+".json").read_text())["exit_code"] != 0, stem
    assert here.joinpath(stem+".source.lean").is_file()
    assert here.joinpath(stem+".log").is_file()
print(f"PASS {len(manifest['entries'])} entries; public17 + kernels2; three empty strict logs; actual4GiB/swap0")
