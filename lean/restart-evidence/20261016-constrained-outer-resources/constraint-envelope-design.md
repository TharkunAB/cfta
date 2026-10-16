# Constraint and path envelopes

Date: 2026-10-16 22:23 CEST.

The new module is `lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinaryConstraintEnvelope.lean`.
It derives path bounds for the actual existing natural-path normalizer, physical payload combination, indexed descent, and allocated local precheck.
It does not assume a completed outer call, future profile, future path bound, or finite global memo-key carrier.

## Source order and the required bound

Haskell `Equality/Operations.hs:93–96` combines the inherited constraints with the returned edge's effective own constraints before it reduces the children.
The combiner in `Equality/Constraint.hs:449–459` appends those two actual class lists and normalizes them.
Indexed descent in `Equality/Constraint.hs:467–485` descends each original trie, drops classes with fewer than two suffixes, and sorts the retained records.

The local class pass has a different input.
`Equality/Operations.hs:207–213` uses combined own and inherited constraints only for the contradiction test.
Its class scan reads the original own records.
The formal `SourceEqualityPrecheck.live_payload` at lines146–148 states that exact distinction.
Consequently an inherited payload can reject a local pass, but it cannot add classes to that pass.

The effective own field includes positive guard equalities.
Haskell `Constraint.hs:129–136` reads this field.
`Constraint.hs:171–176` normalizes positive `Same` and right-fold `And` operations.
`Constraint.hs:215–222` conjoins stored equalities and guards separately.
The present allocated precheck endpoint takes bounds on the INITIAL effective field.
It does not claim a hereditary bound for all guards produced later by arbitrary conjunction or query history.

## Quantitative input and output

`Bounds S D classes` counts all raw path occurrences, including duplicates, and bounds each raw path length by D.
It does not bound an index by the child arity or by any numeric limit.
Let:

- L = (D + 1) * (S + 1).
- W(B, 0) = 1.
- W(B, h + 1) = 1 + B * W(B, h).

A noncontradictory actual normalized output has at most S classes.
Each class has at most W(S * D, L) paths.
The total path-occurrence count is at most S * W(S * D, L).
Each output path has length at most L.
These are separate conclusions; a class count is not a path-occurrence count.

The proof derives the cardinality of the ACTUAL initial index alphabet from the flattened input: at most S * D entries.
It uses the initial alphabet, anchors, and segmented paths from `EqualityTermination.lean`.
The existing `bounded_state` theorem at line539 states the underlying finite-word argument.
The proof does not infer a finite carrier for constraints or recursive memo keys across growing heaps.

For two initial payloads, `combine` uses S = S1 + S2 and D = max D1 D2.
`payload_combine` transfers that result through the literal physical readback equation.
`payload_descend` retains the occurrence bound and replaces the depth by D - 1 for every actual indexed trie descent.
Its coherent ascending-trie premise is an initial representation fact, not a desired output law.

`precheck_bounds` preserves the INITIAL own count and depth at every actual live precheck branch.
`allocated_precheck_paths` derives the exact parent path obligation from initial operation validity, stored and inherited readiness, original stored readback, and an initial effective-field envelope.
It uses `PartialPrecheckAllocation.run_correct`; it does not require the current precheck or parent to complete as an input.
Its conclusion is conditional on each actual classes result, as the existing local resource API requires.

## Concrete path extension

The literal input is `[[[0], [1,1]], [[0,2], [3]]]`.
All four original path occurrences have length at most two.
The actual congruence step returns `[[[0], [1,1]], [[0,2], [1,1,2], [3]]]`.
The generated path `[1,1,2]` has length three.
The actual fixed-point algorithm `mkEqConstraints 3` returns this same output.

The final integration source proves both equations with `cbv`.
The observation log also records the executed model results.
This is the specified suffix propagation in Haskell `Equality/Constraint.hs:427–444`, not a Haskell defect.
A proposed invariant that normalization preserves the original maximum path length is therefore false.

## Model and remaining boundaries

The preserved formal path type is `List Nat` in `EqualityNormalize.lean:25–27`.
Haskell uses `ChildIndex Int` in `Index.hs:41` and `Path [ChildIndex]` in `Path.hs:37–39`.
The theorem imposes no index range within its natural-path model.
It does not prove signed-path conversion, negative-index behavior, or a whole-library Haskell correspondence theorem.

The result supplies a quantitative normalization and inherited-descent foundation.
It does not yet propagate guard envelopes through every generated native, Merge, warm outer-result, raw rebuild, and constructor history.
It does not derive the whole outer reached-parent capacity plan from a single initial resource reservation.
Equality-interner allocation counts, normalization instruction counts, general recursive progress, and host forcing remain separate obligations.
