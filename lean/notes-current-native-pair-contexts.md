# One-sided contexts for checked recursive intersection

This checkpoint preserves the actual checked query work and all older proofs.
The full-library goal remains active. General checked query completion and
recursive Mu language correctness remain open.

## Why exact contexts do not suffice

`SourceEqualityNativeDemandOpenMeaning.SeenContext` fixes every seen pair
reference to the exact intersection of its original operand languages.
An optional binder interprets its body at every candidate language.
These two conditions cannot hold for every candidate at a newly added pair.
The new `unrestricted_extension_impossible` theorem proves that conflict.
The false and true candidate languages would have to equal the same fixed
original intersection. One finite term separates them. This refutes a proposed
induction hypothesis. It does not refute the source intersection algorithm.

## Fixed original inputs and one-sided contexts

`SourceCurrentAllocatedNativePairContexts.source_input_models` constructs
one independent `InputMeaning` and `RankedInput` from original available closed
physical inputs and source facts. It derives root validity, exact rank erasure,
and both original guarded language equations. No output value, successful
checked query, or desired result language occurs in that construction.

`SoundPairs` requires each enclosing output pair reference to accept only
terms in the fixed original pair language. `CompletePairs` requires it to
accept common original terms whose two input derivation ranks fit the bound.
Fresh typed pair references are injective. Their overrides retain old entries.
Sound extension can choose the independent original pair language directly.
Complete extension retains an explicit local candidate-containment premise.

Actual repeated references inherit these one-sided laws. Soundness plus
completeness at every bound in one fixed environment gives exact repeated
meaning. Rank erasure derives the equivalence between the bounded union and
the independent original intersection. Empty-domain, restriction, and bound
weakening laws preserve these obligations in the required directions.

## Remaining recursive proof

The full Mu proof must derive the local complete-extension premise by strict
induction on the original input rank sum. It must connect that induction to
actual checked body traces and the least-language optional binder. The local
context lemma is not a proof of the parent result and must not become a public
assumed result law. Actual accepted/rejected child scheduling remains checked.
Do not replay the old eager worker's skipped children or returned heaps.

Warm completed cells currently store only closed/empty-domain language laws.
Open requests can make those laws vacuous. Their historical body receipts do
not include an initial open-cache semantic invariant. Derive a stronger
preserved open-cache invariant or an adequate causal-history theorem.
The original free-binding interpretation still needs its contextual bridge.
This checkpoint does not supply these missing invariants.

General finite checked completion also needs the requiredFuel induction and
derived reached input receipts. The previous running-cell and actual request
bounds are prerequisites. Initial whole-heap allocation history, the new
current class Scan, and the general constrained outer caller remain open.
Keep all other full-library and separate Sized targets in scope.

## Verification

The new module's focused build, eighteen public axiom probes, nine endpoint
signatures, and eight literal kernel examples pass. Independent review found
no output-result assumption, freshness error, or reversed bound law.
Aggregate checks and preservation are in the restart package.
Evidence uses `/tmp/mcfta-allocated-native-pair-contexts-*` and
`/tmp/mcfta-current-allocated-pair-contexts-review-20261016.md`.
