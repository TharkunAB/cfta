# Enumeration references within allocated value slots

Run from the repository root:

```sh
python3 lean/restart-evidence/20261107-enumeration-index-validity/check.py
```

The checker uses the project Nix shell and Lean toolchain. It builds the actual
module. It then checks the source and the axioms of all four public theorems.
The reported axioms are propext, Classical.choice, and Quot.sound.
No archived build tree or large temporary log is required.
The recorded final check used one Lean job under a 4 GiB cap. Peak memory was 209M.

Indexed means ReferenceBounds.Invariant at the CURRENT state counter. It retains
value-count/counter agreement, UF support and parent bounds, UF Total, stored
suspension references, stored fragment holes, and obligation holes. All referenced
variables are below the actual allocated value count. This is stronger than a
reference bound at a larger worst-case allocation cap.

Both actual imported node and edge expansions preserve Indexed on every successful
return. Their returned fragment holes are below the returned counter. The counter
does not decrease. Initial-state/empty-constraint corollaries require no supplied
invariant, capacity, allocation budget, depth, or graph-size premise.

These theorems cover successful expansion returns. They do not establish all
intermediate states on failing paths or complete-worker resource bounds. Native
ID validity, the original-input/request-size bound, exact end-to-end enumeration,
and actual Haskell correspondence remain open. No Haskell code changed.
No new Original Source, TYPE, or compiler-interface view occurred for this proof.
Historical SourceProcess FAIL and Root upper UNKNOWN remain permanent.
