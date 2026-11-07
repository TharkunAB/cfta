# Enumeration expansion depth and allocation budgets

Run from the repository root:

```sh
python3 lean/restart-evidence/20261107-enumeration-expansion-depth/check.py
```

Use the project Nix shell and Lean toolchain. The checker builds the actual module.
It then checks the source and the axioms of all 11 public theorems.
The only reported axioms are propext, Classical.choice, and Quot.sound.
No archived build tree or large temporary log is required.
The recorded check used one Lean job under a 4 GiB cap. Peak memory was 176M.

The budget is monotone in fuel. An internal ordinary-depth certificate makes the
budget stable above that depth. The budget at that depth bounds every fuel value.
Initial successful node and edge results therefore preserve one reference cap
that does not depend on the action fuel, when the internal depth is established.

The abstract interface also admits an ordinary self-cycle. Its budget at
fuel 2*count+1 is count. It has no uniform budget bound and no ordinary depth.
This concerns the current upper-budget formula. It is not a counterexample to
actual native reachability, successful execution bounds, or Haskell correctness.

The native structural graph connection and the derivation from original inputs
remain open. The depth certificate is sufficient for these local lemmas. The final
worker proof must derive it or use another justified bound. It must not add a
caller-supplied depth or validity premise. Both full workers, failing prefixes,
total branch work, exact enumeration and Haskell correspondence remain in scope.

This check adds no Original Source, TYPE, or compiler-interface view. It does not
recover the permanent historical SourceProcess FAIL or Root upper UNKNOWN.
