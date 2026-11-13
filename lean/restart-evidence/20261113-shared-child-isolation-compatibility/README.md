# Shared-child and opaque isolation compatibility

The combined full Audit check passes. It covers all six affected modules:
the new shared-child observer, the eager resource source, the current eager
width/resource/output modules, and Audit. The import graph has 5896 live
project modules and 4893 Audit imports. The audit checks 94893 axiom reports.
These totals include private and generated declarations.

Audit adds one import. Its previous 266701 bytes remain an exact suffix.
The current eager width/resource/output sources remain byte-identical.
The new child observer's own one-name check and the eager source's own
five-name check pass in the adjacent source packets. The existing global
eager output statement stays unchanged.

`frontier.json` pins the changed and affected sources. `checked.json` records
the actual successful check and cgroup limits. The checker verifies every
pinned source before and after the complete Audit check. All reports allow
only the existing standard Lean axioms. No placeholder axiom is accepted.

From the repository root, run the standalone checker in the existing serial
Nix 4 GiB max/high scope, with swap 0 and one Lean thread:

```sh
python3 lean/restart-evidence/20261113-shared-child-isolation-compatibility/check.py
```

No Haskell/Cabal/test-suite file changes are part of this checkpoint.
Whole eager-marker retention and finite original Type model construction
remain open. Source patches, failed trials and diagnostics are preserved in
the adjacent shared-child source-history packet.
