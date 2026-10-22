"""Check saved original-row-group-chain evidence. This script does not run Lean."""
import argparse
import difflib
import hashlib
import json
import re
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--root", required=True, type=Path)
parser.add_argument("--live", action="store_true")
args = parser.parse_args()
root = args.root.resolve()
evidence = root / "lean/restart-evidence/20261022-original-row-group-chain"
def load(name):
    return json.loads((evidence / name).read_text())
def digest(data):
    return hashlib.sha256(data).hexdigest()
def canonical(text):
    return re.sub(r"[ \t\r\n]+", " ", text).strip(" \t\r\n")
name = "SourceCurrentOriginalRowGroupChain"
namespace = "MicroCFTA." + name + "."
specs = [("groups_complete", "theorem")]
short_names = [short for short, kind in specs]
selected_sha = "45ee19aba69aec9339203917841052791a389fe46f511ab9574105c8f3d254bb"
source_lines = int("257")
strict_stem, full_stem, audit_stem = "original-row-group-chain-strict-1", "original-row-group-chain-public-1", "original-row-group-chain-audit-1"
metrics = dict(actual_jobs=int("3"), source_jobs=int("2"), audit_jobs=int("1"),
    failed_jobs=int("0"), warned_source_exit_zero_jobs=int("0"),
    rejected_public_type_jobs=int("0"))
jobs = json.loads('{"original-row-group-chain-strict-1": [0, "45ee19aba69aec9339203917841052791a389fe46f511ab9574105c8f3d254bb", "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", 0, 0], "original-row-group-chain-public-1": [0, "371df134b728314fd3c9b814c316b5df36a8e23df5891427244c73798035834e", "936e45b4a31049d6ea43cb1f2bd9756fabef7af92922ff5c0fa294b74442c502", 0, 0], "original-row-group-chain-audit-1": [0, null, "e203450759dce90167537f93f88e37be32bc0663f062883775e61d1da88164f3", 0, 1]}')
rejected = json.loads('[]')
assert re.fullmatch(r"[0-9a-f]{64}", selected_sha)
assert jobs and all(stem.startswith("original-row-group-chain-") for stem in jobs)
assert strict_stem in jobs and full_stem in jobs and audit_stem in jobs
assert jobs[strict_stem][0] == jobs[full_stem][0] == jobs[audit_stem][0] == 0
assert jobs[strict_stem][1] == selected_sha and jobs[strict_stem][3:] == jobs[full_stem][3:] == [0, 0]
assert (evidence / (audit_stem + ".json")).is_file(), "Audit is pending; no complete proof report is available"
actual = set()
for path in evidence.glob("*.json"):
    item = json.loads(path.read_text())
    if isinstance(item, dict) and "wrapper" in item and "exit_code" in item:
        if Path(item.get("command", [""])[0]).name in {"lean", "lake"}:
            actual.add(path.stem)
assert actual == set(jobs), actual
assert metrics["actual_jobs"] == len(actual) and metrics["source_jobs"] == sum(bool(row[1]) for row in jobs.values())
assert metrics["audit_jobs"] == sum(not row[1] for row in jobs.values()) and jobs[audit_stem][1] is None
assert metrics["failed_jobs"] == sum(row[0] != 0 for row in jobs.values())
assert metrics["warned_source_exit_zero_jobs"] == sum(row[0] == 0 and bool(row[1]) and bool(row[4]) for row in jobs.values())
assert len(rejected) == len(set(rejected)) == metrics["rejected_public_type_jobs"] and full_stem not in rejected
assert all(stem in jobs and "public" in stem and jobs[stem][0] == 0 for stem in rejected)
public_hashes = [row[1] for stem, row in jobs.items() if row[1] and "public" in stem]
assert len(public_hashes) == len(set(public_hashes)), "FULL repeated on an unchanged source variant"
for stem, (exit_code, source_hash, log_hash, errors, warnings) in jobs.items():
    receipt = load(stem + ".json")
    assert receipt["exit_code"] == exit_code and receipt["log"] == stem + ".log" and receipt["observed_at"]
    raw = (evidence / receipt["log"]).read_bytes()
    assert re.fullmatch(r"[0-9a-f]{64}", log_hash) and digest(raw) == log_hash, stem
    assert receipt["limits"] == stem + ".limits.json"
    assert load(receipt["limits"]) == {"memory.max": "4294967296", "memory.high": "4294967296", "memory.swap.max": "0"}
    usage = load(stem + ".usage.json")
    assert 0 <= usage["age_seconds"] <= 600 and usage["remaining_percent"] > 1, stem
    assert receipt["wrapper"][1:5] == ["--mem", "4G", "--time", "5m"]
    if source_hash:
        assert receipt["source"] == stem + ".source.lean" and receipt["sha256"] == source_hash
        source = (evidence / receipt["source"]).read_bytes()
        assert digest(source) == source_hash and Path(receipt["command"][-1]).resolve() == (evidence / receipt["source"]).resolve()
        assert len(receipt["command"]) == 3 and Path(receipt["command"][0]).name == "lean" and receipt["command"][1] == "-Dlinter.all=true"
        assert len(re.findall(r"^.+?:\d+:\d+: error(?:\([^)]*\))?:", raw.decode(), re.M)) == errors
        assert len(re.findall(r"^.+?:\d+:\d+: warning(?:\([^)]*\))?:", raw.decode(), re.M)) == warnings
        if "public" not in stem:
            assert not re.search(r"^\s*set_option (?:maxHeartbeats|maxRecDepth|linter\.)", source.decode(), re.M)
    else:
        assert Path(receipt["command"][0]).name == "lake" and receipt["command"][-2:] == ["build", "MicroCFTA.Audit"]
strict_source = (evidence / (strict_stem + ".source.lean")).read_bytes()
assert len(strict_source.splitlines()) == source_lines <= 350
assert (evidence / (strict_stem + ".log")).read_bytes() == b""
selection = load("selected-sources.json")
source_path = "lean/MicroCFTA/" + name + ".lean"
assert selection == {source_path: dict(sha256=selected_sha, lines=source_lines, strict=strict_stem, full=full_stem)}
source = (evidence / (name + ".lean")).read_bytes()
assert digest(source) == selected_sha and source == strict_source
gate = load("selected-source-gate.json")
assert gate == dict(status="ROOT_ACCEPTED", path=source_path, sha256=selected_sha, lines=source_lines, snapshot="selected-sources/" + name + ".lean")
assert (evidence / gate["snapshot"]).read_bytes() == source
history = load("source-history-gate.json")
assert history == json.loads('{"status": "ROOT_ACCEPTED", "selected_source_sha256": "45ee19aba69aec9339203917841052791a389fe46f511ab9574105c8f3d254bb", "variants": [{"path": "proposal/SourceCurrentOriginalRowGroupChain.lean", "sha256": "45ee19aba69aec9339203917841052791a389fe46f511ab9574105c8f3d254bb", "lines": 257, "reason": "The sole complete author proposal."}, {"path": "original-row-group-chain-strict-1.source.lean", "sha256": "45ee19aba69aec9339203917841052791a389fe46f511ab9574105c8f3d254bb", "lines": 257, "reason": "The actual first clean strict input; identical to the sole proposal, not a repair."}], "artifacts": [{"path": "SourceCurrentOriginalRowGroupChain.full.lean", "sha256": "371df134b728314fd3c9b814c316b5df36a8e23df5891427244c73798035834e", "bytes": 16655}, {"path": "SourceCurrentOriginalRowGroupChain.lean", "sha256": "45ee19aba69aec9339203917841052791a389fe46f511ab9574105c8f3d254bb", "bytes": 16151}, {"path": "actual-header.lean.txt", "sha256": "7554e1bf17932006e786810a328cad36c0499f78a5f9bec27b9d1ea955c4dea9", "bytes": 4462}, {"path": "check-full-public.py", "sha256": "0fc5f475834c50e284dde838cb42d68ef09e9c114156c75bcfb199cbe42b92e9", "bytes": 8307}, {"path": "frozen-modules.json", "sha256": "eb9a8de37e28c52bce1ac73075b75b4846b00b06a821f89ce7661bc8ad7c43e2", "bytes": 111}, {"path": "full-preparation/check-full-public.py", "sha256": "0fc5f475834c50e284dde838cb42d68ef09e9c114156c75bcfb199cbe42b92e9", "bytes": 8307}, {"path": "original-row-group-chain-audit-1.json", "sha256": "0b1ffda1dca314c8fd16560a11eea09b1451b3701688c059af1d7640f5e255cb", "bytes": 601}, {"path": "original-row-group-chain-audit-1.limits.json", "sha256": "408bad6c1715f2c15adecf485dbfcb2753512b2f94e0a96011ddef6f6650faf3", "bytes": 90}, {"path": "original-row-group-chain-audit-1.log", "sha256": "e203450759dce90167537f93f88e37be32bc0663f062883775e61d1da88164f3", "bytes": 690}, {"path": "original-row-group-chain-audit-1.usage.json", "sha256": "cbf0552fce3e906d163b5bb378b19ceb7aa6cbf772d96cc39b9a606a41798620", "bytes": 114}, {"path": "original-row-group-chain-public-1.json", "sha256": "c50847fd4a24a883a33e9976c9c9e84ca3e4302484140baa4730653d5f67ce62", "bytes": 820}, {"path": "original-row-group-chain-public-1.limits.json", "sha256": "408bad6c1715f2c15adecf485dbfcb2753512b2f94e0a96011ddef6f6650faf3", "bytes": 90}, {"path": "original-row-group-chain-public-1.log", "sha256": "936e45b4a31049d6ea43cb1f2bd9756fabef7af92922ff5c0fa294b74442c502", "bytes": 10540073}, {"path": "original-row-group-chain-public-1.source.lean", "sha256": "371df134b728314fd3c9b814c316b5df36a8e23df5891427244c73798035834e", "bytes": 16655}, {"path": "original-row-group-chain-public-1.usage.json", "sha256": "d6951fd6d344abfd91f42e72191f56d66a037ef4a3da31e9753f6cceae035b81", "bytes": 114}, {"path": "original-row-group-chain-strict-1.json", "sha256": "8a8637f8c95d97351f03b9d1ef15d4b0c6d2481448e474850d2fb7e3a4ca530b", "bytes": 820}, {"path": "original-row-group-chain-strict-1.limits.json", "sha256": "408bad6c1715f2c15adecf485dbfcb2753512b2f94e0a96011ddef6f6650faf3", "bytes": 90}, {"path": "original-row-group-chain-strict-1.log", "sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", "bytes": 0}, {"path": "original-row-group-chain-strict-1.usage.json", "sha256": "8fc83c61888145217b9d6858dee1ff32eec7c1e14832805d7f90e9f339692782", "bytes": 114}, {"path": "original-source-index.json", "sha256": "42417533124526b9f177fdf1fc4412970591369901cdee51d720b4d1b959ae3b", "bytes": 244}, {"path": "proposal/FROZEN.json", "sha256": "3557246237f742f433f60581165493a33a99d95e74d3821ab35b248b3f3fa743", "bytes": 356}, {"path": "proposal/approved-declarations.lean.txt", "sha256": "75e7f8e8c10fa84857c95d9b320d67f19d2db241019331a7a5f7c9f3317ebd5d", "bytes": 9297}, {"path": "proposal/approved/FROZEN.json", "sha256": "f0e5f8072dc6fce129b173231532ca69b8793865426e97196e01d0823ade195d", "bytes": 450}, {"path": "proposal/approved/context.lean.txt", "sha256": "04a702ce3d985b0d503fec07f4f8899fae080f0768dae5ece402f2441eba575f", "bytes": 986}, {"path": "proposal/approved/contracts.json", "sha256": "ce5fc0d2d39bc3a19fd3186f825ffe35684cea2397c777078f3c6ecff7c2148d", "bytes": 786}, {"path": "proposal/approved/import-graph.json", "sha256": "de63cd41992d3765927875356edd5fdbed3aa11fdf4a363cb7f35c06523dae2b", "bytes": 1053}, {"path": "proposal/approved/local-induction.lean.txt", "sha256": "025a5e8c504465b53e6725195d8d6344e9a42367ca9d6f29bd8d56d423255e5e", "bytes": 3290}, {"path": "proposal/approved/pins.json", "sha256": "bd594d11ec64c7205a5faf76ff98967d1af638c52f218cbba831d40f2cc574a3", "bytes": 14438}, {"path": "proposal/approved/private-header.lean.txt", "sha256": "ac402bc349a4617b958f1b6382a07e403ce3f265243264afde777c8f6206e952", "bytes": 563}, {"path": "proposal/approved/proof-route.md", "sha256": "6096c3b09c0be370da4ed564e7b420ddbc360b5b48e9195760dea85a13d0ead8", "bytes": 2583}, {"path": "proposal/approved/public-header.lean.txt", "sha256": "24207f42da0137904262175e682c878b8838c352a4e645897859f276525ceaa3", "bytes": 4456}, {"path": "proposal/approved/root-declaration-review.json", "sha256": "648867ce06fb952f34263c4052b379a6b344cc0b0a4b03af8f55036e3f16b724", "bytes": 2749}, {"path": "proposal/approved/scope-status.json", "sha256": "d70ed33db59e25c47d40f6186d3a12d61789bda4b0d8d021142447e446e106df", "bytes": 1046}, {"path": "proposal/approved/source-index.json", "sha256": "f81d14fb41b7b6b485468a51b27515b7355dcdcc05b81215fe09f98e90028e47", "bytes": 21283}, {"path": "proposal/approved/stitch-equations.txt", "sha256": "3716187b5b107c941fefba9d0c14ab1c0420ff44d698488f59053dc9dd761502", "bytes": 988}, {"path": "proposal/cuts/R01-0153-0182-Operations.hs.txt", "sha256": "56cd88d87b5044dcbc1334d6267de9266120063a0994b2dda79b69f1df7a9e06", "bytes": 1420}, {"path": "proposal/cuts/R01-0334-0370-Operations.hs.txt", "sha256": "f2fc69f84894812af3cb1503fc1141f3913dd672bbc96ce5e7f738f16866f249", "bytes": 1679}, {"path": "proposal/cuts/R01-0743-0771-Operations.hs.txt", "sha256": "aabe4917ef50134e84fcded20e43a55898169d0b571b7845527b763097277b2b", "bytes": 1451}, {"path": "proposal/cuts/R01-0755-0771-Operations.hs.txt", "sha256": "392cf581336fbfe86b3e9cc62a5029e7838eff892c9241b385eda033b74b30a8", "bytes": 923}, {"path": "proposal/cuts/R01-0790-0798-Operations.hs.txt", "sha256": "dce1a4ee4bff67aa6949b69a4ed97f9a5c4d846ca84bed9fda8ec583634c5578", "bytes": 368}, {"path": "proposal/cuts/R02-0195-0197-Type.hs.txt", "sha256": "cd9374e9425b4592ee24fc9ee75977f5ba8edf66d97ca857bc96cac9af9de39f", "bytes": 108}, {"path": "proposal/cuts/R03-0001-0017-SourceCurrentOriginalRowClusterLanguage.lean.txt", "sha256": "adcbe391190ae6bdabb1a4bfd714bf7ae82928d1d0c48c0db831e3c5a8bf04c5", "bytes": 1104}, {"path": "proposal/cuts/R03-0243-0302-SourceCurrentOriginalRowClusterLanguage.lean.txt", "sha256": "3ef279e4493382d257d12ca3c38fcf12f964d7b573ab42f7c8bbe769e2e3d3a8", "bytes": 3676}, {"path": "proposal/cuts/R03-0353-0390-SourceCurrentOriginalRowClusterLanguage.lean.txt", "sha256": "29be75686e79c10a765dbd17b6387a0eaa3ae714723ee50db45ca294bb35b73c", "bytes": 2809}, {"path": "proposal/cuts/R04-0001-0089-SourceCurrentPrependGrouping.lean.txt", "sha256": "3d293c27b502aa308c8cc05f21796264b18f873221b3343910e77d6bcb6b53ba", "bytes": 4475}, {"path": "proposal/cuts/R05-0018-0030-SourceCurrentMergeGrouping.lean.txt", "sha256": "3be7efc9d578f79bc57cd16fa155211d4ffea2e0f5c7064bbfeb325b2131e8e5", "bytes": 834}, {"path": "proposal/cuts/R05-0062-0104-SourceCurrentMergeGrouping.lean.txt", "sha256": "e885a2e29951f2a9cc551a3a31f60acd8f532e5ab3d446bebac86ce4474674ef", "bytes": 2287}, {"path": "proposal/cuts/R05-0149-0181-SourceCurrentMergeGrouping.lean.txt", "sha256": "057f9c618f7acf2945fa854d26d09f7984bfd96fcaf1e0531a9ce774b9c13d0b", "bytes": 2160}, {"path": "proposal/cuts/R06-0001-0129-SourceCurrentOriginalRowClusterScan.lean.txt", "sha256": "37bcce3d4b04310f6e3c1e394e27a875baf98547f4078d1b3be7252c47d0a5f7", "bytes": 7109}, {"path": "proposal/cuts/R07-0055-0110-SourceCurrentSameSymbolEdgeComparisonDomains.lean.txt", "sha256": "0c6de3b97a6c866b90b2cbeb87e96ff9268c8ecc426a0c48c13ff76f70935ed6", "bytes": 3702}, {"path": "proposal/cuts/R07-0113-0128-SourceCurrentSameSymbolEdgeComparisonDomains.lean.txt", "sha256": "871fdcf1444a369c1cd742d9a44aa4e07f75deb3b2ed7c631359cfc90b387dbd", "bytes": 1399}, {"path": "proposal/cuts/R07-0171-0185-SourceCurrentSameSymbolEdgeComparisonDomains.lean.txt", "sha256": "318b57b1a12703c5e75d6230b4b397f6c32d23aad80343684c0e61d25a3264dc", "bytes": 1339}, {"path": "proposal/cuts/R08-0008-0022-SourceRecursiveIntersectionDomainAllocation.lean.txt", "sha256": "33d7e362101f4cc7b4c4ddf81c1d0aa7dc258ac9f0d0b3a18878b8775c48766a", "bytes": 759}, {"path": "proposal/cuts/R08-0049-0077-SourceRecursiveIntersectionDomainAllocation.lean.txt", "sha256": "47f2242c9bdce373b35257c6d6133345050dff0eeb4102cf475d03aa2565cdb9", "bytes": 1437}, {"path": "proposal/cuts/R09-0105-0115-SourceCurrentAllocatedNativeResourceForecast.lean.txt", "sha256": "58e50811b32ab9369008c5c20df88176fa0f01693c012dbf1f7dfc630a137823", "bytes": 713}, {"path": "proposal/cuts/R09-0118-0145-SourceCurrentAllocatedNativeResourceForecast.lean.txt", "sha256": "bc322b26a13659d9a756ed68f7429956ad8cfb8abf560326a2a624302058276f", "bytes": 1419}, {"path": "proposal/cuts/R10-0014-0035-SourceRecursiveIntersectionKernelFacts.lean.txt", "sha256": "fa9f5c36f5f055a6566904f86b8533fb31b0861e1c6126b19a4c60ec4ce69b09", "bytes": 1428}, {"path": "proposal/cuts/R11-0027-0035-Cache.lean.txt", "sha256": "faf93fa10fad15b0a9efe56f3046b8b35e62d2608e6a8523587b84dc751c34d6", "bytes": 446}, {"path": "proposal/cuts/R12-0011-0023-FlatMemoThunkReturned.lean.txt", "sha256": "8f61e5726bd70cbd451209b60a1c34aedb6869b0d994aa69158998d1e2b8ff14", "bytes": 760}, {"path": "proposal/cuts/R13-0240-0265-Sized.lean.txt", "sha256": "46e20af64dbbd6eec9fa5c1cba5a2dd55a02f8635355166eb0025a2fadd66b2e", "bytes": 1249}, {"path": "proposal/cuts/R14-0021-0026-SourceCurrentSameSymbolEdgeControl.lean.txt", "sha256": "b7d23ce712e92193215725844d630585f1aa5d8d61bd9cb6b98f3f1e4f7a32f9", "bytes": 382}, {"path": "proposal/cuts/R15-0015-0018-InternedEdgeResidency.lean.txt", "sha256": "02364e8ff5eeb185a20f23bef0e05c0d811a7502ffb4d98923de28c7aacc5efc", "bytes": 184}, {"path": "proposal/cuts/T16-0285-0290-Basic.lean.txt", "sha256": "95c6a0e38409f44dc6542580d0093dbf1e302fd075f1ee5c3c7682ed261848ed", "bytes": 168}, {"path": "proposal/cuts/T16-0330-0337-Basic.lean.txt", "sha256": "e9c0e51a069cb63807c6ed6ec3fb92e4efcfb12b9cbc56321ec807d358b6b36d", "bytes": 222}, {"path": "proposal/cuts/T17-0591-0623-Lemmas.lean.txt", "sha256": "8ee884880723738b7313a9e1c65c0fd7ef75d3f48ea7af4156fcb3f21439bc22", "bytes": 1354}, {"path": "proposal/cuts/T17-0944-0966-Lemmas.lean.txt", "sha256": "ec2f499a53addb9ddfa092588183b37990262d41657caa75d8475d8ef4a69925", "bytes": 1112}, {"path": "proposal/cuts/T18-0031-0034-OfFn.lean.txt", "sha256": "51048c3b9f8a36b2796b096c0fbdbd8dc5827fc9f6c9fe185c35b16279f45c6f", "bytes": 233}, {"path": "proposal/cuts/T18-0077-0121-OfFn.lean.txt", "sha256": "d50a75b960e0eab43d3aca30e960676b5a167d09b337e6fd1865ecdc43f9d95c", "bytes": 1382}, {"path": "proposal/cuts/T19-0367-0367-Lemmas.lean.txt", "sha256": "0e983eb263b8dfbbb396fdb6f504d43a9fb95df2d8a5c9b8ca765a66ad574130", "bytes": 72}, {"path": "proposal/cuts/T19-0389-0389-Lemmas.lean.txt", "sha256": "9afea231a7b74f7d449ce01172ddd7d1628e1a9c081e0a58b6c6b32925fe8333", "bytes": 94}, {"path": "proposal/cuts/T19-1598-1605-Lemmas.lean.txt", "sha256": "c9dd095756355d7f4ca1f76d183882f199e72cdf4df259b0cc1db38f37a585bb", "bytes": 296}, {"path": "proposal/cuts/T19-1946-1971-Lemmas.lean.txt", "sha256": "6f22d81f1fb02350a0d2ac38519bd76e039630b265f971edcf0283065fb26e99", "bytes": 1038}, {"path": "proposal/cuts/T19-3774-3781-Lemmas.lean.txt", "sha256": "79226f293c1b07764180db1dd130735e4942b53a99b23227b1da900a22a7495c", "bytes": 324}, {"path": "proposal/cuts/T19-3821-3827-Lemmas.lean.txt", "sha256": "fd1aba629761e5da46e369935c5e82162c27fef512d270d2bb5449fbdbdcbbeb", "bytes": 270}, {"path": "proposal/cuts/T20-0090-0096-Perm.lean.txt", "sha256": "bb7e77db64d208af446e58fdbb1e71a7411f1d1718061318380b8d91ae377c34", "bytes": 284}, {"path": "proposal/cuts/T20-0142-0147-Perm.lean.txt", "sha256": "623ebaa57cdb7b2366dc3ef4bd84eec94118dd38b930c223a91f0b1ca39c2cfa", "bytes": 248}, {"path": "proposal/cuts/T20-0566-0572-Perm.lean.txt", "sha256": "d8e6fb15acd6f952f236b537d3ef501496abc56c648c70c96799e3989fb679f9", "bytes": 367}, {"path": "proposal/cuts/T21-0064-0072-Core.lean.txt", "sha256": "1440e3504eb00878cd070156368515590174e55986902a54ba3c3b077667e5a7", "bytes": 424}, {"path": "proposal/cuts/T22-0631-0635-Basic.lean.txt", "sha256": "b566488a47d15aa35f225b7e38c7bf4badce19ebc8ac787ca824c874e783d7b6", "bytes": 188}, {"path": "proposal/cuts/T22-0671-0672-Basic.lean.txt", "sha256": "6bfa0743b5fb562fb521bb7a4f0eb6ed564c14a4ab222db612467f52f53691c2", "bytes": 167}, {"path": "proposal/cuts/T23-0008-0035-List.lean.txt", "sha256": "fcb62b5b691f4ee18f2866a1f1e29de5dba7705f625e39a7c3cfedcd750010f4", "bytes": 982}, {"path": "proposal/cuts/T24-0086-0088-PropLemmas.lean.txt", "sha256": "b1412ed8cb7f5e1f24e25b9102eb7c28f24daaa5429e020e098adb208c4976d6", "bytes": 286}, {"path": "proposal/cuts/T24-0125-0125-PropLemmas.lean.txt", "sha256": "00d4c9e51604ea3bad4fd838dff127cd546fdf1501d5c64b35b36e92c4955b65", "bytes": 137}, {"path": "proposal/cuts/T24-0338-0340-PropLemmas.lean.txt", "sha256": "14999f5af19c46710457a3556c1e89607689c11443001beec392cf17a8b02519", "bytes": 244}, {"path": "proposal/header-inverses.json", "sha256": "06ecb997a697cd27d0ead008ad4e5143345c858d42c650c61c5f2d245b057dd9", "bytes": 1297}, {"path": "proposal/note.md", "sha256": "a6e15523342d5084598e7c7441def31077854c970afea3b4292e9b8eda96339f", "bytes": 3072}, {"path": "proposal/pins.json", "sha256": "7593b5b8bce47564b0cfa4db0aa97281b9053eae058462fa6b2ce606a50018ea", "bytes": 15290}, {"path": "proposal/source-addition.patch", "sha256": "15f8a601a18e4b4e1d023d6b2f3168bd9f74ba147bbd49e6d82f211420f260c7", "bytes": 8388}, {"path": "proposal/source-index.json", "sha256": "456817b80ff06408664f670f82fb526ce4d89bd43c3ea7cc26057cec082be77a", "bytes": 23394}, {"path": "proposal/source-status.json", "sha256": "2d314de72c288b0d7158df4a0f497330dc4f858637b2f345541dc716450503e8", "bytes": 1095}, {"path": "proposal/sources/R01-Operations.hs.txt", "sha256": "1f3b8d64936ef85efbc886263f52ede7c8d557149f6f4ad98d52160fc16bd836", "bytes": 38260}, {"path": "proposal/sources/R02-Type.hs.txt", "sha256": "f79fbaf37d986569e572649e6779084a7e7c78429b0f82558de867418c690b77", "bytes": 36883}, {"path": "proposal/sources/R03-SourceCurrentOriginalRowClusterLanguage.lean.txt", "sha256": "e1c54fe63f95392a928cf539b108a061b64101596a3fc6bfc5c09b72a030eba8", "bytes": 24807}, {"path": "proposal/sources/R04-SourceCurrentPrependGrouping.lean.txt", "sha256": "3d293c27b502aa308c8cc05f21796264b18f873221b3343910e77d6bcb6b53ba", "bytes": 4475}, {"path": "proposal/sources/R05-SourceCurrentMergeGrouping.lean.txt", "sha256": "d958bc556a2d8f29645c463beffdc0f63f8854369e0bd11f59feae469069ad4d", "bytes": 10531}, {"path": "proposal/sources/R06-SourceCurrentOriginalRowClusterScan.lean.txt", "sha256": "37bcce3d4b04310f6e3c1e394e27a875baf98547f4078d1b3be7252c47d0a5f7", "bytes": 7109}, {"path": "proposal/sources/R07-SourceCurrentSameSymbolEdgeComparisonDomains.lean.txt", "sha256": "8ae94566570cf99ec3eb61ec991d36a1df196c5b9c2bc2fca4aeb88fd6305e15", "bytes": 12833}, {"path": "proposal/sources/R08-SourceRecursiveIntersectionDomainAllocation.lean.txt", "sha256": "480bbf11d7411c11c76b31ff4449b0a3c70168feeb7f2bdedd0df4eca63a34ba", "bytes": 6056}, {"path": "proposal/sources/R09-SourceCurrentAllocatedNativeResourceForecast.lean.txt", "sha256": "401fa57e9d964cd601fa2b0b0a1d79cdb37fbd9d37842da236d79b4acf6c6a1e", "bytes": 8329}, {"path": "proposal/sources/R10-SourceRecursiveIntersectionKernelFacts.lean.txt", "sha256": "3d357ba3752609d4c9d6c46e871535de8c22db56b1a834da29b58c526dfb2ac0", "bytes": 10430}, {"path": "proposal/sources/R11-Cache.lean.txt", "sha256": "139de1fc30ece4ef377ec87afd42d0b82ec57a01869339015e7eab21eece4215", "bytes": 16352}, {"path": "proposal/sources/R12-FlatMemoThunkReturned.lean.txt", "sha256": "50c175da9fb0dac94f7a782f559cc4a232ba4a3aaf5c98eedf70c33a67bf84b0", "bytes": 7289}, {"path": "proposal/sources/R13-Sized.lean.txt", "sha256": "36dbdc2e2fd85c6d57860668f854f8ee7e77618cdc85e106111677ecf2a514d6", "bytes": 21019}, {"path": "proposal/sources/R14-SourceCurrentSameSymbolEdgeControl.lean.txt", "sha256": "dbf416168635ecc34effe17891f557f31ec14df2f7cb368c52863d69a6174559", "bytes": 19667}, {"path": "proposal/sources/R15-InternedEdgeResidency.lean.txt", "sha256": "c0596750df3bc2472271cf68451f233c27846bcff0baea5eb4d31da05d5723b0", "bytes": 15975}, {"path": "proposal/sources/T16-Basic.lean.txt", "sha256": "bb3d4e46cb40a24f5a09e6e003c76f2b84140a598df81233f0bffe3afe08cbf4", "bytes": 12956}, {"path": "proposal/sources/T17-Lemmas.lean.txt", "sha256": "03a06d6c8b826d7ef0774eecd5f7fc6c8640c1c4e8188ed97c9a4a066d284456", "bytes": 49095}, {"path": "proposal/sources/T18-OfFn.lean.txt", "sha256": "b91368ac7239f0171498250d1de0e270102c5f8431fa5723a449c83b02807c1b", "bytes": 6342}, {"path": "proposal/sources/T19-Lemmas.lean.txt", "sha256": "9f9177396114b7b5898b0c4ac95f91bb3ee139f16dcde3becabdf9f948170dda", "bytes": 152710}, {"path": "proposal/sources/T20-Perm.lean.txt", "sha256": "c778ecb634cad13616e994adb18f7028a0ea3c229e747a0fee02e033108a8d39", "bytes": 27500}, {"path": "proposal/sources/T21-Core.lean.txt", "sha256": "6218a9825a0ce51a6bbe3949ec7a86c4406f4f216bd3cd1262736cfc1c997c54", "bytes": 100653}, {"path": "proposal/sources/T22-Basic.lean.txt", "sha256": "9d39c20a6de1e973e13490ec81a30672296f173e34014a0e8ba0109958534346", "bytes": 87017}, {"path": "proposal/sources/T23-List.lean.txt", "sha256": "9d4127179da53d3b7fa59204024db7cd5db60e12c24d7be9fb274befca80ce71", "bytes": 1334}, {"path": "proposal/sources/T24-PropLemmas.lean.txt", "sha256": "725e3fd04fe5edca754503c3a9f6efbd31070306c71cd25c4880663e75fdd150", "bytes": 45617}, {"path": "public-readback/original-row-group-chain-full-readback.json", "sha256": "e1e2acb2696ee6c8b5e7f9cd9192c26f0ead79bb972d00aff64d4ea376b975e8", "bytes": 3342}, {"path": "public-readback/original-row-group-chain-groups_complete-axioms.txt", "sha256": "2fc109540808323a0f7140e87cbaecacdeb86b53e0caa80114fb34583ab60453", "bytes": 132}, {"path": "public-readback/original-row-group-chain-groups_complete-body.txt", "sha256": "8d558b9269ab532ce8832cc00095497844b8f28f4a43ce8e64f2a905655cac64", "bytes": 10316689}, {"path": "public-readback/original-row-group-chain-groups_complete-printed-public-type.txt", "sha256": "7fcdbdb51a0578b4bb359d7ef1648799cbf188cf7bdda79c1ac0d58f7b4b5410", "bytes": 111557}, {"path": "public-readback/original-row-group-chain-groups_complete-public-type.txt", "sha256": "7fcdbdb51a0578b4bb359d7ef1648799cbf188cf7bdda79c1ac0d58f7b4b5410", "bytes": 111557}, {"path": "root-declaration-review.json", "sha256": "648867ce06fb952f34263c4052b379a6b344cc0b0a4b03af8f55036e3f16b724", "bytes": 2749}, {"path": "root-full-review.json", "sha256": "4334cadefe4de2fac526b0d5417d47b96d089de7c1eff4bbecc9c6a93fcbbe31", "bytes": 2985}, {"path": "root-source-review.json", "sha256": "511c645a9b3e99bf8f8ed4480a72093a6c1cc41d5faf08d0944258aa4aad61fa", "bytes": 1036}, {"path": "selected-source-gate.json", "sha256": "bd4b5e18b240c2d4e760cd8e2b2e77b52fcb7b987481fde49d79c4cdff313ac7", "bytes": 270}, {"path": "selected-sources.json", "sha256": "c5ed3f6aad8bbc1ebf6eaa9b8fdf7f76f8ba8c04c3a39f8f61a51c28ca7f7000", "bytes": 269}, {"path": "selected-sources/SourceCurrentOriginalRowGroupChain.lean", "sha256": "45ee19aba69aec9339203917841052791a389fe46f511ab9574105c8f3d254bb", "bytes": 16151}], "patches": [], "rejected_public_types": []}') and history["status"] == "ROOT_ACCEPTED"
assert history["selected_source_sha256"] == selected_sha
assert set(history) == {"status", "selected_source_sha256", "variants", "artifacts", "patches", "rejected_public_types"}
variants = {item["path"]: item for item in history["variants"]}
artifacts = {item["path"]: item for item in history["artifacts"]}
assert variants and len(variants) == len(history["variants"]) and len(artifacts) == len(history["artifacts"])
for path, item in {**artifacts, **variants}.items():
    relative = Path(path)
    assert not relative.is_absolute() and ".." not in relative.parts
    data = (evidence / relative).read_bytes()
    assert re.fullmatch(r"[0-9a-f]{64}", item["sha256"]) and digest(data) == item["sha256"]
    if path in variants:
        assert 0 < len(data.splitlines()) == item["lines"] <= 350 and isinstance(item["reason"], str) and item["reason"].strip()
    else:
        assert len(data) == item["bytes"]
assert not set(variants) & set(artifacts)
for stem, row in jobs.items():
    for suffix in [".json", ".log", ".limits.json", ".usage.json"]:
        assert stem + suffix in artifacts, ("unretained actual job artifact", stem, suffix)
    if row[1] and "public" in stem:
        assert stem + ".source.lean" in artifacts, "FULL printer sources are artifacts, not bounded math variants"
assert any((evidence / path).read_bytes() == source for path in variants)
for stem, row in jobs.items():
    if row[1] and "public" not in stem:
        assert any(pin["sha256"] == row[1] and (evidence / path).read_bytes() == (evidence / (stem + ".source.lean")).read_bytes() for path, pin in variants.items()), stem
for patch in history["patches"]:
    assert isinstance(patch["reason"], str) and patch["reason"].strip()
    assert patch["before"] in variants and patch["after"] in variants
    assert patch["path"] in artifacts and artifacts[patch["path"]]["sha256"] == patch["sha256"]
    before, after = [(evidence / patch[key]).read_text() for key in ["before", "after"]]
    expected = "".join(difflib.unified_diff(before.splitlines(True), after.splitlines(True), fromfile=patch["fromfile"], tofile=patch["tofile"]))
    assert (evidence / patch["path"]).read_text() == expected
rejections = {item["stem"]: item for item in history["rejected_public_types"]}
assert len(rejections) == len(history["rejected_public_types"]) and set(rejections) == set(rejected)
for stem, item in rejections.items():
    assert item["raw_sha256"] == jobs[stem][2] and item["reason"] and item["artifacts"]
    assert all(path in artifacts for path in item["artifacts"])
contracts = json.loads('{"context.lean.txt": {"path": "signature-plan/context.lean.txt", "sha256": "04a702ce3d985b0d503fec07f4f8899fae080f0768dae5ece402f2441eba575f", "lines": 16}, "private-header.lean.txt": {"path": "signature-plan/private-header.lean.txt", "sha256": "ac402bc349a4617b958f1b6382a07e403ce3f265243264afde777c8f6206e952", "lines": 9}, "public-header.lean.txt": {"path": "signature-plan/public-header.lean.txt", "sha256": "24207f42da0137904262175e682c878b8838c352a4e645897859f276525ceaa3", "lines": 71}, "local-induction.lean.txt": {"path": "signature-plan/local-induction.lean.txt", "sha256": "025a5e8c504465b53e6725195d8d6344e9a42367ca9d6f29bd8d56d423255e5e", "lines": 48}}')
expected_contracts = {'context.lean.txt': {'path': 'signature-plan/context.lean.txt', 'sha256': '04a702ce3d985b0d503fec07f4f8899fae080f0768dae5ece402f2441eba575f', 'lines': 16}, 'private-header.lean.txt': {'path': 'signature-plan/private-header.lean.txt', 'sha256': 'ac402bc349a4617b958f1b6382a07e403ce3f265243264afde777c8f6206e952', 'lines': 9}, 'public-header.lean.txt': {'path': 'signature-plan/public-header.lean.txt', 'sha256': '24207f42da0137904262175e682c878b8838c352a4e645897859f276525ceaa3', 'lines': 71}, 'local-induction.lean.txt': {'path': 'signature-plan/local-induction.lean.txt', 'sha256': '025a5e8c504465b53e6725195d8d6344e9a42367ca9d6f29bd8d56d423255e5e', 'lines': 48}}
assert contracts == expected_contracts and list(contracts) == list(expected_contracts)
contract_data = {}
for filename, item in contracts.items():
    relative = Path(item["path"])
    assert not relative.is_absolute() and ".." not in relative.parts
    data = (evidence / relative).read_bytes()
    assert digest(data) == item["sha256"] and len(data.splitlines()) == item["lines"]
    contract_data[filename] = data
context = contract_data["context.lean.txt"]
assert source.startswith(context)
positions = []
for filename in ["private-header.lean.txt", "public-header.lean.txt", "local-induction.lean.txt"]:
    header = contract_data[filename].rstrip(b"\n") + b" := by\n"
    assert source.count(header) == 1 and source.index(header) >= len(context), filename
    positions.append(source.index(header))
assert positions == sorted(set(positions))
public = re.findall(r"(?m)^\s*(?:(?:noncomputable|unsafe|partial)\s+)?(def|theorem|lemma|abbrev|opaque|instance|structure|inductive)\s+([^\s(\[{:=]+)", source.decode())
assert public == [(kind, short) for short, kind in specs]
helpers = []
for line in source.decode().splitlines():
    if re.match(r"^\s*(?:(?:noncomputable|unsafe|partial)\s+)?private\b", line):
        declaration = re.match(r"^\s*(?:(?:noncomputable|unsafe|partial)\s+)?private\s+(?:(?:noncomputable|unsafe|partial)\s+)?(?:def|theorem|lemma|abbrev|opaque|instance|structure|inductive)\s+([^\s(\[{:=]+)", line)
        assert declaration, ("unsupported private declaration", line)
        helpers.append(declaration.group(1))
assert helpers == ["bucket_readback"], "Only the approved H22 private helper is permitted"
declaration_review = load("root-declaration-review.json")
assert declaration_review["status"] == "ROOT_DECLARATION_REVIEW_CLEAR"
assert declaration_review["module"] == "MicroCFTA." + name
assert declaration_review["public_names"] == short_names and declaration_review["private_names"] == helpers
assert declaration_review["local_induction"] == "complete" and declaration_review["source_hard_stop"] == 350
assert declaration_review["contract_sha256"] == "ce5fc0d2d39bc3a19fd3186f825ffe35684cea2397c777078f3c6ecff7c2148d"
assert digest((evidence / "signature-plan/contracts.json").read_bytes()) == declaration_review["contract_sha256"]
assert [{key: item[key] for key in ["path", "lines", "sha256"]} for item in declaration_review["contracts"]] == [dict(path=filename, lines=item["lines"], sha256=item["sha256"]) for filename, item in expected_contracts.items()]
if args.live:
    assert (root / source_path).read_bytes() == source
original = (evidence / "original-sources/Audit.original.lean.txt").read_bytes()
assert digest(original) == "4c54e8f578cc9e12084e7306671e6c6410150811a3868fc128b90805ae5452e1" and len(original.splitlines()) == 3127
assert load("original-source-index.json")["sources"] == [dict(path="lean/MicroCFTA/Audit.lean", snapshot="original-sources/Audit.original.lean.txt", lines=3127, sha256=digest(original))]
addition = b"import MicroCFTA.SourceCurrentOriginalRowGroupChain\n"
audit_source = (root / "lean/MicroCFTA/Audit.lean").read_bytes()
assert audit_source.count(addition) == 1 and audit_source.replace(addition, b"", 1) == original
assert audit_source.index(addition) < audit_source.index(b"/-!")
report = load("public-readback/original-row-group-chain-full-readback.json")
printer = (evidence / (full_stem + ".source.lean")).read_bytes()
raw = (evidence / (full_stem + ".log")).read_bytes()
options = ["maxRecDepth 30000", "maxHeartbeats 0", "linter.all true", "pp.explicit true", "pp.fullNames true", "pp.proofs true",
    "pp.proofs.threshold 254", "pp.universes true", "pp.deepTerms true", "pp.maxSteps 10000000"]
tail = "\n" + "".join("set_option " + option + "\n" for option in options)
for short, kind in specs:
    tail += "".join(d + namespace + short + "\n" for d in ["#check @", "#print ", "#print axioms "])
assert printer == source + tail.encode() and len(printer.splitlines()) == source_lines + 14 and len(tail.splitlines()) == 14
assert all(printer.decode().splitlines().count("set_option " + option) == 1 for option in options)
assert all(printer.decode().splitlines().count(d + namespace + short) == 1 for short, kind in specs for d in ["#check @", "#print ", "#print axioms "])
for stem, row in jobs.items():
    if row[1] and "public" in stem:
        public_source = (evidence / (stem + ".source.lean")).read_bytes()
        assert any(public_source == (evidence / path).read_bytes() + tail.encode() for path in variants), stem
assert source.rstrip().endswith(("end MicroCFTA." + name).encode())
assert (report["source_sha256"], report["source_lines"], report["printer_sha256"]) == (selected_sha, source_lines, digest(printer))
assert report["log_sha256"] == digest(raw) and report["log_bytes"] == len(raw) == int("10540073")
assert report["receipt_sha256"] == digest((evidence / (full_stem + ".json")).read_bytes()) and report["owned_public_job_exit"] == 0
assert all(report[key] for key in ["all_eight_printer_settings", "exact_module_and_diagnostic_tail", "diagnostic_limits_after_module_only", "no_omissions"])
assert (report["pp_option_count"], report["linter_option_count"], report["diagnostic_limit_count"]) == (7, 1, 2)
assert report["configured_paths"] == {key: str(path.resolve()) for key, path in dict(source=evidence / (name + ".lean"), printer=evidence / (full_stem + ".source.lean"), raw=evidence / (full_stem + ".log"), receipt=evidence / (full_stem + ".json")).items()}
assert [(item["head"], item["kind"]) for item in report["heads"]] == [(namespace + short, kind) for short, kind in specs]
head_metrics = json.loads('{"groups_complete": {"type_bytes": 111557, "type_characters": 111495, "type_logical_lines": 1156, "type_line_feeds": 1155, "type_final_newline": false, "type_sha256": "7fcdbdb51a0578b4bb359d7ef1648799cbf188cf7bdda79c1ac0d58f7b4b5410", "body_bytes": 10316689, "body_characters": 10315127, "body_sha256": "8d558b9269ab532ce8832cc00095497844b8f28f4a43ce8e64f2a905655cac64", "actual_axioms": ["Classical.choice", "Quot.sound", "propext"], "printed_type_bytes": 111557, "printed_type_sha256": "7fcdbdb51a0578b4bb359d7ef1648799cbf188cf7bdda79c1ac0d58f7b4b5410", "raw_type_byte_identity": true}}')
assert list(head_metrics) == short_names
log = raw.decode()
assert not re.search(r"sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.", log)
starts = []
for short, kind in specs:
    pattern = re.escape(namespace + short) + r"(?:\.\{[^}\n]*\})?"
    matches = list(re.finditer(r"^(?:@)?" + pattern + r" :", log, re.M))
    assert len(matches) == 1, short
    starts.append(matches[0])
assert starts == sorted(starts, key=lambda match: match.start()) and not log[:starts[0].start()].strip()
allowed, actual_by_head, retained_names = {"Classical.choice", "Quot.sound", "propext"}, {}, []
for index, (short, kind) in enumerate(specs):
    head = namespace + short
    segment = log[starts[index].end():starts[index + 1].start() if index + 1 < len(starts) else len(log)]
    pattern = re.escape(head) + r"(?:\.\{[^}\n]*\})?"
    delimiters = list(re.finditer(r"\n" + kind + " " + pattern + r" :", segment))
    assert len(delimiters) == 1, short
    checked, printed = segment[:delimiters[0].start()], segment[delimiters[0].end():]
    axioms = list(re.finditer(r"^'" + re.escape(head) + r"' (depends on axioms:|does not depend on any axioms)", printed, re.M))
    assert len(axioms) == 1, short
    axiom = axioms[0]
    declaration, axiom_output = printed[:axiom.start()], printed[axiom.start():]
    normalized, matches = canonical(checked), []
    for match in re.finditer(r" :=\n", declaration):
        prefix = canonical(declaration[:match.start()])
        if prefix == normalized:
            matches.append(match)
        elif len(prefix) > len(normalized):
            break
    assert len(matches) == 1, short
    declared, body = declaration[:matches[0].start()], declaration[matches[0].end():]
    raw_identity = checked.encode() == declared.encode()
    assert canonical(checked) == canonical(declared)
    metric = head_metrics[short]
    assert set(metric) == {"type_bytes", "type_characters", "type_logical_lines", "type_line_feeds", "type_final_newline", "type_sha256", "body_bytes", "body_characters", "body_sha256", "actual_axioms", "printed_type_bytes", "printed_type_sha256", "raw_type_byte_identity"}
    assert len(checked) == metric["type_characters"] and len(checked.encode()) == metric["type_bytes"]
    assert len(checked.splitlines()) == metric["type_logical_lines"] and checked.count("\n") == metric["type_line_feeds"] and checked.endswith("\n") == metric["type_final_newline"]
    assert digest(checked.encode()) == metric["type_sha256"]
    assert len(declared.encode()) == metric["printed_type_bytes"] and digest(declared.encode()) == metric["printed_type_sha256"]
    assert raw_identity is metric["raw_type_byte_identity"]
    assert not any(token in checked + declared for token in ["_private", "✝", "†", "‡"])
    assert not any(re.search(re.escape(namespace + helper) + r"(?![\w'])", checked + declared) for helper in helpers)
    head_report = report["heads"][index]
    assert all(head_report[key] for key in ["check_print_type_identity", "check_print_type_lexical_identity", "unique_complete_type_body_delimiter", "actual_axioms_within_standard_allowed"])
    assert head_report["check_print_type_byte_identity"] is raw_identity
    assert head_report["private_namespace_helpers_checked"] == helpers and head_report["private_type_spellings_checked"] == ["_private", "✝", "†", "‡"] and head_report["private_public_type_names"] is False
    assert head_report["checked_type_characters"] == len(checked) and head_report["normalized_type_characters"] == len(normalized)
    assert head_report["checked_type_bytes"] == len(checked.encode()) and head_report["checked_type_sha256"] == digest(checked.encode())
    assert head_report["printed_type_bytes"] == len(declared.encode()) and head_report["printed_type_characters"] == len(declared)
    assert head_report["printed_type_sha256"] == digest(declared.encode()) and head_report["canonical_type_sha256"] == digest(normalized.encode())
    assert head_report["body_characters"] == len(body) == metric["body_characters"] and len(body.encode()) == metric["body_bytes"]
    assert body.startswith("fun ") and len(body) > 50 and digest(body.encode()) == metric["body_sha256"]
    values = re.fullmatch(r"\s*\[([^\]]*)\]\s*", printed[axiom.end():]) if axiom.group(1) == "depends on axioms:" else None
    assert values or (axiom.group(1) == "does not depend on any axioms" and not printed[axiom.end():].strip())
    actual_axioms = {re.sub(r"\.\{[^}]*\}", "", item.strip()) for item in values.group(1).split(",") if item.strip()} if values else set()
    assert sorted(actual_axioms) == head_report["actual_axioms"] == metric["actual_axioms"] and actual_axioms <= allowed
    assert head_report["actual_standard_three_axioms"] == (actual_axioms == allowed)
    actual_by_head[short] = sorted(actual_axioms)
    for suffix, text in [("public-type", checked), ("printed-public-type", declared), ("body", body), ("axioms", axiom_output)]:
        filename = "original-row-group-chain-" + short + "-" + suffix + ".txt"
        retained = (evidence / "public-readback" / filename).read_bytes()
        assert retained == text.encode() and report["retained_slices"][filename] == dict(bytes=len(retained), sha256=digest(retained))
        retained_names.append(filename)
assert set(report["retained_slices"]) == set(retained_names)
assert digest((evidence / "full-preparation/check-full-public.py").read_bytes()) == "0fc5f475834c50e284dde838cb42d68ef09e9c114156c75bcfb199cbe42b92e9"
assert digest((evidence / "check-full-public.py").read_bytes()) == "0fc5f475834c50e284dde838cb42d68ef09e9c114156c75bcfb199cbe42b92e9"
review = load("root-full-review.json")
assert review["status"] == "ROOT_ACCEPTED_FOR_OFFICIAL_INSTALL_AND_AUDIT" and review["source_sha256"] == selected_sha and review["source_lines"] == source_lines
assert review["public_heads"] == [namespace + short for short in short_names]
assert review["complete_public_type_root_review"] == review["independent_complete_public_type_review"] == "CLEAR"
assert review["root_read_complete_public_types"] and review["root_printed_type_lexical_identity_verified"] and review["four_private_markers_and_all_helpers_absent_from_type"]
assert review["raw_type_byte_identity_by_head"] == {short: head_metrics[short]["raw_type_byte_identity"] for short in short_names}
assert all(review.get(key, all(head_metrics[short]["raw_type_byte_identity"] for short in short_names)) == all(head_metrics[short]["raw_type_byte_identity"] for short in short_names) for key in ["root_printed_type_byte_identity_verified", "check_print_type_byte_identity"])
assert review["types_sha256"] == {short: head_metrics[short]["type_sha256"] for short in short_names}
assert review["full_raw_sha256"] == digest(raw) and review["actual_axioms_by_head"] == actual_by_head
assert review["body_retained_and_programmatically_checked"] and review["whole_body_manual_read_claimed"] is False
required_true = ['actual_finite_group_chain_derived', 'each_group_actual_control_equation', 'concrete_per_group_fuels', 'same_evolving_full_state', 'all_boundary_packets', 'fixed_admitted_source_model_rank_parent', 'literal_original_parent_rows', 'supplied_iteration_order_preserved', 'reversed_buckets_are_original_symbol_filters', 'flattened_original_membership_and_length', 'all_ambient_physical_union_iff', 'single_initial_room_global_trace', 'cumulative_native_extension_table_extends_returned', 'local_remaining_not_full_iteration', 'all_declared_contracts_exact', 'literal_non_node_and_mu_empty_row_view']
required_false = ['common_fuel_outer_traversal_claimed', 'hash_map_refinement_claimed', 'haskell_execution_or_refinement_claimed', 'public_pass_claimed', 'whole_goal_complete', 'heap_or_node_identity_claimed', 'fixed_hash_map_outer_key_order_claimed', 'generated_parent_or_mu_behavior_claimed', 'practical_width_or_convergence_claimed', 'future_success_or_semantic_oracle', 'post_room_or_model_replacement_oracle', 'physical_union_without_admission_claimed']
assert all(review[key] is True for key in required_true) and all(review[key] is False for key in required_false)
audit = (evidence / (audit_stem + ".log")).read_text()
build = re.search(r"Build completed successfully \((\d+) jobs\)\.", audit)
dependencies = re.search(r"Checked axiom dependencies of (\d+) MicroCFTA theorems", audit)
assert build and dependencies and not re.search(r"\berror(?:\([^)]*\))?:", audit)
assert int(build.group(1)) == int("3639") and int(dependencies.group(1)) == int("75499")
print(json.dumps(dict(status="PASS", live=args.live, **metrics, new_lean_lake_jobs=0, selected_modules=1, original_archives=1,
    public_definitions=0, public_theorems=1, audit_build_jobs=int(build.group(1)), audit_dependencies=int(dependencies.group(1)), audit_log_sha256=digest(audit.encode())), indent=2))
