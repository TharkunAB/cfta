# Captured/prepared marker compatibility

The full affected Audit frontier passes for all five modules: the eager
resource source, current eager width/resources/outputs, and Audit. The graph
has 5896 live modules and 4893 Audit imports. Its 94912 axiom reports include
private and generated declarations. Only standard Lean axioms are accepted.

`frontier.json` pins all affected sources. `checked.json` records the actual
pass and cgroup limits. The checker verifies those sources before and after
the complete Audit check. The adjacent own-module packet verifies all five
unchanged public theorem names and replays the three archived source cuts.
The public shared-child isolation module, Audit and eager width/resource/output
sources remain byte-identical. No new public global result is claimed.

From the repository root, run the checker in the existing serial Nix 4 GiB
max/high scope, with swap 0 and one Lean thread:

```sh
python3 lean/restart-evidence/20261113-eager-captured-prepared-isolated-compatibility/check.py
```

No Haskell/Cabal/test-suite change is part of this checkpoint. Whole marker
induction, finite accepted partial-root completion and original typing remain
open. The adjacent semantic audit records an UNPROVED root-witness target.
