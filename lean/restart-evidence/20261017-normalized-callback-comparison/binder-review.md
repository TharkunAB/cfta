# Actual completed binder decomposition

The new production source is `SourceCurrentNativeBinderExecution.lean`.
Its SHA256 is `52800a69fd008c7eaa8c4ccaeaf5b1534792dfbe741b3958e3789fe3a447f3e7`.
The three earlier owned sources and packages remain unchanged.

`decompose` requires the existing initial `SourceHistory.Context` and the
literal completed repaired binder build equation. It derives both normalized
callback equations and the final request equation. It derives historical
contexts at afterDepth, cut, and final. Each context includes DepthHeap;
the final context also supplies Normal at the exact returned heap.

The result retains the actual raw ordinary build before filtering, its exact
filter pair, and its return context with the actual ordinary reference in
the lexical environment. The raw return heap physically grows to the full
binder return heap. Its issued-reference history extends to that heap.
The actual Depth and ordinary probe values are both Available at final.
These facts follow from actual full callback/request receipts. There is no
assumed output comparison, result law, desired history, or result origin.

The helper is an actual-completed-execution verifier, not an initial generic
completion theorem. `binder-kernels-1` composes the existing full closed
source completion producer with this helper. This integration supplies no
future run or final-state premise. It includes arbitrary nested binder body
syntax rather than a restricted source fragment.

Strict attempt 3 has an empty log and matches production byte for byte.
Canonical attempt 1 passes 273 jobs. Public attempt 1 checks the one public
helper. Kernel attempt 1 checks the one initial closed-source composition.
Both use all eight explicit printer/linter options and full proof/axiom
printing. Only the three standard axioms occur. Effective memory limits are
4 GiB / 4 GiB / zero swap. Failed strict attempts 1 and 2 remain preserved.
`binder-CONTINUE.md` contains the final restart state and exact API.

This module does not prove normalized unused-Mu equality. It provides the
actual branch states and transport facts needed by that separate proof.
