# Ordered bounded discovery

The controller uses sorted token/tuple batches and ascending found keys. It retains the current final batch. Actual successful evaluation derives coverage, child closure and distinct keys/choices. Its Left roots preserve the original plain language and its full graph has unique size classes. The nonnegative limit bounds checking rounds by limit+1, not total tuple work.

The source is `lean/MicroCFTA/SourceSizedDeterminizationOrderedRun.lean`.
The Haskell source is `cfta-generator/src/Data/CFTA/Gen/Internal/Table.hs`.

Run from the repository root under the serial heavy-job cap:

```sh
env XDG_RUNTIME_DIR=/run/user/1000 DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/1000/bus \
  HEAVY_PEAKS=/tmp/mcfta-ordered-determinization-peaks.tsv \
  /home/tritlo/Code/heavy-management/bin/capped --mem 4G --time 380 \
  python3 lean/restart-evidence/20261107-sized-determinization-ordered-run/check.py
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
