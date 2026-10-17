#!/usr/bin/env python3
"""Verify frozen evidence without changing source or rebuilding."""
from pathlib import Path
import hashlib
import json
import re
ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).resolve().parent
PREFIX='causal-winner'
manifest=json.loads((HERE/(PREFIX+"-manifest.json")).read_text())
assert len(manifest["entries"])==manifest["entry_count"]
seen=set()
for entry in manifest["entries"]:
    assert entry["path"] not in seen, entry["path"]
    seen.add(entry["path"])
    data=(ROOT/entry["path"]).read_bytes()
    assert len(data)==entry["bytes"],entry["path"]
    assert hashlib.sha256(data).hexdigest()==entry["sha256"],entry["path"]
for check in manifest["checks"]:
    source=(ROOT/check["source"]).read_text()
    log=(ROOT/check["log"]).read_text()
    assert not re.search(r"error(?:\(|:)|warning:|sorryAx",log),check["log"]
    pairs=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]",log,re.M|re.S)
    assert len(pairs)==check["pairs"],(check["log"],len(pairs))
    for name,axioms in pairs:
        assert "#print axioms "+name in source
        assert "#check @"+name in source
        assert re.search(r"^@?"+re.escape(name)+r"\s*:",log,re.M),name
        names=[re.sub(r"\.\{[^}]*\}","",item.strip()) for item in axioms.split(",") if item.strip()]
        assert set(names)<={"propext","Classical.choice","Quot.sound"},(name,names)
    for setting in ["pp.explicit true","pp.fullNames true","pp.proofs true","pp.universes true","pp.deepTerms true","pp.maxSteps 10000000","linter.all true"]:
        assert "set_option "+setting in source,setting
    assert source.endswith("\n") and not source.endswith("\n\n")
print("PASS:",manifest["entry_count"],"hashes;",sum(c["pairs"] for c in manifest["checks"]),"complete pairs; diagnostics 0")
