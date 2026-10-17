"""Verify committed source bytes, modes, evidence, preservation, and remote identities."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parents[3]
evidence = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--remote-file", type=Path)
args = parser.parse_args()


def git(*arguments: str) -> bytes:
    return subprocess.run(["git", *arguments], cwd=root, check=True, capture_output=True).stdout


head = git("rev-parse", "HEAD").decode().strip()
assert git("rev-parse", "--show-object-format").decode().strip() == "sha1"
index = {}
for row in git("ls-files", "--stage", "-z").split(b"\0"):
    if row:
        metadata, name = row.split(b"\t", 1)
        mode, digest, stage = metadata.decode().split()
        assert stage == "0", name
        index[name.decode()] = (mode, digest)
committed = {}
for row in git("ls-tree", "-rz", "HEAD").split(b"\0"):
    if row:
        metadata, name = row.split(b"\t", 1)
        mode, kind, digest = metadata.decode().split()
        assert kind == "blob", name
        committed[name.decode()] = (mode, digest)
assert index == committed
for name, (mode, expected) in index.items():
    path = root / name
    if mode == "120000":
        assert path.is_symlink(), name
        data = os.readlink(path).encode()
    else:
        assert mode in {"100644", "100755"} and path.is_file(), name
        data = path.read_bytes()
        assert bool(path.stat().st_mode & 0o111) == (mode == "100755"), name
    actual = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
    assert actual == expected, name

checksums = 0
assert str((evidence / "SHA256SUMS").relative_to(root)) in index
for row in (evidence / "SHA256SUMS").read_text().splitlines():
    expected, name = row.split(maxsplit=1)
    path = root / name.removeprefix("*")
    assert str(path.relative_to(root)) in index, name
    assert hashlib.sha256(path.read_bytes()).hexdigest() == expected, name
    checksums += 1

checkpoint = subprocess.run(
    ["python3", str(evidence / "verify-checkpoint.py")], cwd=root, check=True, capture_output=True, text=True
)
assert json.loads(checkpoint.stdout) == json.loads((evidence / "checkpoint-validation.json").read_text())
preservation = subprocess.run(
    ["python3", str(evidence / "verify-preservation.py"), "--require-current"],
    cwd=root, check=True, capture_output=True, text=True,
)
status = git("status", "--porcelain=v1").decode()
assert not status, status
remote = None
if args.remote_file:
    remote = {name: digest for digest, name in (row.split() for row in args.remote_file.read_text().splitlines())}
    assert remote["refs/heads/formalize"] == head
    assert remote["refs/heads/main"] == git("rev-parse", "c0cc8a05").decode().strip()
print(json.dumps({
    "head": head,
    "tracked_blobs_and_modes": len(index),
    "filesystem_index_head_equal": True,
    "evidence_checksums": checksums,
    "checkpoint_matches_retained_report": True,
    "preservation_passes": True,
    "clean": True,
    "remote": remote,
    "scope": "Initial cached fields, inherited readiness, causal Context/Frame/Fits, available values, and pure original-source reservations construct the complete literal allocated local reduction. Its own precheck derives the reached branch and original records. Scan, selected Required, and the tail-first class pass retain actual strict reads, the full old semantic receipt, same-inventory Frame/Post, numeric Fits, exact outer tables, arity, original and returned availability, and all nine independently larger worker fuels. Force, Leaf, editors, and Class/Fold/Pass no longer need finite input Cap or semantic Cap-Merge sidecars. No finite output Cap is claimed. No future branch, graph, reached range, worker success, returned invariant, or whole-forest closedness is an initial premise. Pure majorants are partly noncomputable and do not establish extracted runtime budgets or concrete host capacity. Outer parent and mutual recursion, convergence, arbitrary unsupported open recursion, current Haskell adapters, laziness, publication, and complete public Haskell correspondence remain open. The whole-library goal remains active.",
}, indent=2))
