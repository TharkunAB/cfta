# Exact bucket projection

A per-key projection of sorted buckets equals the original ordered value filter. Optional lookup retains exact key presence. Appended batches append each old bucket before its new bucket. This supplies the source cumulative-map value order.

The source is `lean/MicroCFTA/SourceSortedBucketsProjection.lean`.
The Haskell source is `cfta-generator/src/Data/CFTA/Gen/Internal/Table.hs`.

Run from the repository root under the serial heavy-job cap:

```sh
env XDG_RUNTIME_DIR=/run/user/1000 DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/1000/bus \
  HEAVY_PEAKS=/tmp/mcfta-ordered-determinization-peaks.tsv \
  /home/tritlo/Code/heavy-management/bin/capped --mem 4G --time 380 \
  python3 lean/restart-evidence/20261107-sorted-buckets-projection/check.py
```

The checker enters `shell.nix`, builds the actual Lake target, and checks
this source with own warnings as errors and all public axiom reports.
Only `propext`, `Classical.choice`, and `Quot.sound` are allowed.
`checked.json` records the source hash and reports. Temporary reports are
removed. No copied source/build tree is needed. No clean/CI/Haskell execution
is claimed. Native container/holder simulation, generated-arity zip targets,
signed limits and current public Sized routes still need their full attachment.
The original-input total-work/word/capacity and native identity/cache/interner/
Eq/hash/machine-Int results remain open. No Haskell source changed.
