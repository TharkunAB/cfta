# Constructed finite ordinary class-pass resources

Frozen: 2026-10-16 21:32 CEST.
Source: `lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinaryPassResources.lean`.
Source SHA256: `44af41891ebdd406c5d95f297898443d4f3551bc2f49b1ffb56bbe2da6915aed` (232 lines).

## Result and public API

The four pure functions outputRows, outputArity, nodeBudget, and edgeBudget compute a tail-first profile and cumulative constructor budget. They depend only on the record list and initial forest envelope. Duplicate classes remain in the source list and are charged again.

fold_complete and complete construct their own Fold or Pass, strict Reads, and full physical and semantic receipt. They also return literal six-bound StableRun, NativeStored, OutputStored, Merge profile Stored, uniform output profile, ordered NodeNarrow, exact forest length, height bound, actual ConstructorWorkTrace, request-count bounds, final Capacity, and both final supply bounds.

Initial arguments are formula and solver models, initial inventory, width bits, records, every record's coherence and nontriviality, initial forest and full Checked state, physical and profile Merge certificates, native/output certificates, CacheCovers, initial global validity, initial forest profile/length/height and all class path depths, and total numeric headroom. There is no supplied tail result, old PassCapacity, completed enclosing graph, future profile, body-law callback, range plan, or future capacity premise.

## Composition and scope review

The induction constructs the tail first. The head receives that exact tail forest, full Checked state, Merge table, global bundle, and computed inventory. Tail supplies and initial total headroom derive headroom for the head. The next ClassResources call uses the computed tail row and arity limits. It keeps the original forest-length and height bounds because actual positional narrowing preserves both.

The complete FoldReads are built from the same raw tail and head graphs. Fold.verified derives the full receipt for that actual joined return. StableRun comes from the same raw graph. The exact Work traces append tail before head. Request counts and both supply bounds add in that order. No cache or interner reset occurs between classes. Class construction clears only its own target slots through the existing class producer.

Pass construction adds literal Empty propagation after the fold. This changes the returned forest but not the Checked state, Merge memo, global bundle, or Work trace. Empty erasure preserves the uniform profile and forest length. Existing FiniteOrdinaryClassPass.pass derives the same actual receipt and positional narrowing. Its language iff remains conditional on satisfaction of every class. The new endpoint does not assert unconditional language equality.

The input profiles permit full guards and nonempty own classes. They exclude Mu, references, and explicit union throughout. The result accounts for constructor Work and constructor supplies. It does not cover equality-interner capacity, all host instruction costs, GHC demand or IntMap forcing, repeated outer-pass resources, general recursive input forms, or the whole library.

No Haskell source changed. The current field-pool repair and other source validation remain root-owned evidence. This proof does not add a new Haskell behavior claim.

## Validation

- Direct check 1: terminal exit 0. It reported only unused typeclass variables in a private erasure lemma. The exact draft and raw log are retained.
- Direct check 2: terminal exit 0 with no warnings. It omits unused typeclass variables in two private profile lemmas. Public statements do not change.
- Root canonical pass-resources-build-1.log: observed terminal exit 0, 1382 jobs. Only the historical inputs dependency warning appears.
- Six public axiom/full-signature pairs: imported direct check exit 0, 1266 lines. Four definitions use no axioms. Both theorems use only propext, Classical.choice, and Quot.sound. No warning, error, sorryAx, or truncated term appears.
- Two imported integration axiom/full-signature pairs: final direct check 3 exits 0, 802 lines, no warnings or errors. Draft checks 1 and 2 and their exact sources are retained.
- No Lake or Git command ran under this task. No older proof changed. The temporary direct-check olean is removed after canonical import checks.

## Integration checks

1. two_classes constructs both classes using only the combined initial budget. It decomposes its own raw Fold to prove that the second record executes at the original entry and the first record captures that exact literal tail return. It returns full receipt, stores, uniform profile, narrowing, StableRun, Work trace, request bounds, and final capacity. No intermediate profile or success is an input.
2. empty_pass constructs the pass for an empty class list. Its own strict Reads prove global identity. Raw graph inversion proves exact full state and Merge identity. The literal worker succeeds with all six bounds zero. Work is empty, both request counts are zero, and final Empty propagation has exact forest-language equivalence. The input may already contain Empty.

These are component and integration checks. They do not establish whole-library correspondence or unqualified termination of all inputs.
