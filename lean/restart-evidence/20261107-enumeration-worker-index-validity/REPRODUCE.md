# Actual enumerateOut references within allocated value slots

Run from the repository root:

```sh
python3 lean/restart-evidence/20261107-enumeration-worker-index-validity/check.py
```

The checker uses the project Nix shell and Lean toolchain. It builds the actual
module. It then checks the source and the axioms of all four public theorems.
The reported axioms are propext, Classical.choice, and Quot.sound.
No archived build tree or private Source cut is required for proof reproduction.
The final check used one Lean job under a 4 GiB cap. Peak memory was 210M.

Every successful actual enumerateOut result preserves Indexed and counter
monotonicity. Its fragment holes are below the returned counter. The internal
step requires an Indexed incoming state and an allocated queried variable.
The initial-state/root-index-zero corollary derives those requirements without
supplied validity or capacity. Compositions after initial node or edge expansion
also preserve the earlier and final fragment references at the final counter.

This is a result for the actual imported Graph-parameterized Lean worker. It is
not a replacement worker. It does not prove all states on failing paths, total
work, an original-input/request-size bound, or actual Haskell correspondence.
The actual enumerateFully Oracle slots permit enumeration-state actions. Their
concrete native realization must establish the required preservation laws.
No caller-supplied validity or callback law may be added to the final theorem.

The same Native reader replayed already-owned rows244..329: 86 repeated Source
lines and zero new unique Source. Capture and separate receiver each passed all
three guard phases with all nine then-current own math sources. Root reviewed
only numeric receipts and the new guard code. Root did not view the private cut.
These historical guards used the pre-proof worker header. That role has since
changed. Any later Source job needs fresh pins, not a replay of those guard claims.
No new TYPE or compiler-interface view occurred. All quotas remain unchanged.
Historical SourceProcess FAIL and Root upper UNKNOWN remain permanent.
No Haskell code changed and no Haskell fix was established.
