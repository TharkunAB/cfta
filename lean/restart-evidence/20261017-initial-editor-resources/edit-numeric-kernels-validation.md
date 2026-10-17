# Concrete edit integration validation

Lean: pinned 4.34.1, absolute source path, `-Dlinter.all=true`.
Final command checks `edit-numeric-kernels-14.source.lean` directly.
Final raw log: `edit-numeric-kernels-14.log`, exit 0.
It contains 2 complete explicit signature/axiom pairs and no diagnostics.
The only reported axioms are `propext`, `Classical.choice`, and `Quot.sound`.
Printing enables full names, explicit terms, proofs, universes, deep terms,
and 10000000 print steps. No `.olean` file is written.

The final live kernel equals the immutable attempt 14 snapshot.
Attempt 11 also independently checks the recovered concrete Node kernel.
Attempts 1, 9, and 10 contain foreign collision artifacts. The original
attempt 1 raw log is unavailable. A separately named reconstruction of its
source has explicit provenance. It is not used as an original snapshot.
All remaining failed sources and raw logs stay in the component registry.
No production source, Haskell file, Audit import, or older evidence changed.
