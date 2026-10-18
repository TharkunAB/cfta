# Causal publication heap induction

The module defines `Heap predicate state` for a recursive payload predicate with no current-state argument. Each stored Mu must satisfy that predicate. A retained effect with `NoNewMu` preserves the heap. Reservation changes no `nodeRecords`. Completion uses the exact keep-first cases: an old record retains its proved property, or the exact new candidate supplies it.

`path_heap` inducts over `SourceCurrentNativeMuIssuedHistory.Path`. At publication, it first applies the induction hypotheses to the actual Depth callback and ordinary callback. It derives the allocated heap by unchanged payload storage. It then applies the body-path induction hypothesis. The publication obligation receives the invariant at `before`, `afterDepth`, `cut`, `allocated`, and `afterBody`. It must prove the predicate for the exact publication entry, body, Depth, and ordinary values. The completion lemma then preserves the invariant at the actual publication endpoint, including an earlier retained winner.

`build` obtains the actual path from the original initial Context and source call. Its conclusion uses `Outcome.state`. It therefore covers both completed and pending executions. `closed` supplies the empty initial Context and heap. Neither endpoint assumes successful execution or a future heap property.

The publication obligation remains explicit. This module proves an induction principle. It does not discharge the general body/probe reconstruction or binder fusion step. A predicate that depends on a changing reader needs a separate transport proof; `NoNewMu` alone does not provide that transport.

The focused integration builds `binder true (node7[])` from empty tables. It derives Ready and instantiates the new `closed` endpoint with `ConstrainedCapSourceHistory.Origin`. Each publication discharges the obligation by its actual common-expression `event.origin`. The integration does not call the existing `closed_origins` result. It derives that the exact installed Mu has an Origin. Its stored body is the returned ordinary value of depth zero. The Mu candidate has depth one. Actual smart cleanup returns the depth-zero body. This validates the unused-binder case that a strict returned-depth measure does not cover.

Seven public declarations and one constructed declaration have full signature, proof, and axiom output. The strict source and strict integration logs contain zero bytes. Canonical output has no warning. All runs use the verified 4 GiB memory limits, zero swap, and five-minute cap. The first production attempt lacked the existing `record_cases` namespace. The first fixture attempt ran one tactic after `cbv` had already solved the goal. Both attempts remain present. No resource cap was reached.

General recursive outer completion, full nested binder fusion, and Haskell correspondence remain open.
