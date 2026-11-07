# Actual enumerateFully index preservation under its internal callback law

Run from the repository root:

```sh
python3 lean/restart-evidence/20261107-enumeration-fully-index-validity/check.py
```

The checker uses the project Nix shell and Lean toolchain. It builds the actual
module. It then checks the source and the axioms of all five public theorems.
The reported axioms are propext, Classical.choice, and Quot.sound.
No archived build tree or private Source cut is required for proof reproduction.
The final check used one Lean job under a 4 GiB cap. Peak memory was 348M.

OraclePreservesIndices is an INTERNAL proof dependency. It concerns both actual
Oracle slots. Every successful pre-expansion callback reply must preserve Indexed
and counter monotonicity when its UVar is allocated. The post-expansion slot also
receives a fragment whose holes are below the current counter. The property covers
both Bool values in successful callback replies. It does not require a bound on
native node IDs or add a callback allocation/cost bound.

Under that property, actual enumerateFully successful returns preserve Indexed
and counter monotonicity. Initial-state and composed Node/Edge/Out corollaries
derive the incoming state conditions. Held fragments remain below the final
counter. The proof checks the actual scan, selection, repeated-recursion reset,
Oracle slots, actual Out call, and recursive continuation.

The actual native Oracle realization has NOT established this property. The final
system theorem must derive the law from that realization. It must not add a new
caller-supplied callback, validity, closure, resource, fuel, or success premise.
No replacement worker or safe alternative Oracle is introduced.

All successful Bool replies include False replies, but callback-error/internal
prefixes and all worker failing traces remain open. No callback cost bound,
original-input/request-size resource bound, exact end-to-end enumeration, or
actual Haskell correspondence is proved here. No Haskell code changed or fix
was established. No new Source replay, TYPE, or compiler-interface view occurred.
The prior 86LF owned replay belongs to the separate Out proof epoch. All permanent
quotas remain unchanged. SourceProcess FAIL and Root upper UNKNOWN stay permanent.
