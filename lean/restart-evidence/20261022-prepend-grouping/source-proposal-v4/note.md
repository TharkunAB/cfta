# Prepend grouping V4 repair proposal
Status: FINAL/FROZEN COMPLETE SOURCE-ONLY UNCOMPILED, HOLD FOR REVIEW.
Actual root strict2 on V3 exited1 with only the empty-table specialization error and no warnings. Its complete failed source/raw/receipt/caps/usage/peak evidence is retained; the V3 predecessor retains strict1 too.
The only changed proof is reverse_fromRows. It unfolds the two fromRows definitions, applies the existing fold bridge, transports initial-table equality through the append fold, and proves that equality pointwise by funext/rfl.
No named local lemma, helper, assumption, definition or public type was added. Context, all nine headers, all three equations and the reviewed generalized IH remain exact.
The complete89-line source was read. The exact V3-to-V4 proof-site patch, body-deletion inverse and all earlier packages remain. Nine indexed source pins match live bytes.
The actual ledger is two failed strict jobs, no FULL and no root metadata failure. V4 has not run. Default limits and all linters remain.
No compiler, prepared tool, runtime, Git, network or repository write ran. Root and Required whole-source review must precede a further root check. This package is immutable after freeze.
