# Actual value reads at computed current-counter fuel

Run from the repository root:

```sh
python3 lean/restart-evidence/20261107-enumeration-value-access/check.py
```

The checker uses the project Nix shell and Lean toolchain. It builds the actual
module. It then checks the source and the axioms of all four public theorems.
The reported axioms are propext, Classical.choice, and Quot.sound.
No archived build tree or large temporary log is required.
The recorded final check used one Lean job under a 4 GiB cap. Peak memory was 172M.

For an Indexed state and an allocated variable, actual rawValue has a successful
result and preserves the state. Its returned stored value obeys the current
reference bound. Actual getValue succeeds at fuel state.counter+1. It preserves
Indexed and the counter. Its result obeys the returned current-counter bound.
The proof combines actual representative success with actual indexed value access.

The initial node and edge corollaries derive Indexed from actual successful
expansion. They do not require a supplied invariant or capacity. The queried key
must be an allocated variable. The final worker proof must derive that fact for
its actual queries. It must not add a new caller-supplied validity premise.

The fuel here is computed from the current state. It is not the requested single
bound computed from original inputs and requested size. Complete-worker control,
failing paths, total work, native ID validity, exact end-to-end enumeration, and
actual Haskell correspondence remain open. No Haskell code changed.
No new Original Source, TYPE, or compiler-interface view occurred for this proof.
Historical SourceProcess FAIL and Root upper UNKNOWN remain permanent.
