# Whole-marker worker compatibility

The complete affected Audit frontier passes for all five modules: the eager
resource source, current eager width/resources/outputs, and Audit. The graph
has 5896 live modules and 4893 Audit imports. All 94921 axiom reports use only
standard Lean axioms; totals include private/generated declarations.

The adjacent own-module packet builds the real module, verifies all SIX public
theorem names, and runs the three archived reverse-patch replays. Its new public
law adds whole-worker marker retention. All five old public laws, Audit, the
child-isolation module and original eager width/resource/output sources remain
exact. The original-input output result stays unchanged.

`frontier.json` pins every affected source. `checked.json` records the actual
pass and cgroup limits. The checker verifies snapshots before and after Audit.
From the repository root, run it in the existing serial Nix 4 GiB max/high scope,
with swap 0 and one Lean thread:

```sh
python3 lean/restart-evidence/20261113-eager-whole-marker-compatibility/check.py
```

Whole-marker structural preservation is proved. Finite accepted completion,
original typing and the remaining full-system obligations stay open.
No Haskell/Cabal/test-suite file changes are part of this checkpoint.
