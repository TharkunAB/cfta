# Current Haskell class-fold comparison

Audited source main is c0cc8a05. No Haskell source changes are required by
this increment.

cfta/src/Data/CFTA/Equality/Operations.hs lines 201 to 211 retain the
source right fold and final empty propagation. Lines 235 to 245 define
reduceEClass. The class captures its actual input ns. Each path's target
uses the other paths of that same class and that same input. The edit
compiler uses ascending class paths. The modeled record must retain that
source order.

The checked class worker starts new class-local target slots over the
supplied checked state and warm Merge memo. Its fold executes the tail
before the head captures the tail result. All global read receipts pass
through the same actual reads. Empty propagation changes the forest and
leaves the returned checked state and Merge memo unchanged.

The new initial producers construct this modeled execution. They do not
prove Haskell lazy demand, host memo publication, hash-consing, concrete
capacity, or the full source gate. Refused-class tests, required-child
preparation, outer descent, and general constrained Mu remain separate
caller obligations. Existing selected domains and all-root caps remain
explicit. The handwritten worker still needs full Haskell correspondence.

Root FINDINGS retains the current Haskell repair handoff first. The field
pool repair b9219b9e is merged and validated in the unchanged source.
Every later Haskell fix must have a failure, executable reproducer,
affected paths, commit, validation, and upstream status in FINDINGS.
