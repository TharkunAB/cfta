# Delayed inherited owner progress

Written 2026-10-21 01:37 CEST. This is the author's proof report, not an independent review.

The new source `lean/MicroCFTA/SourceCurrentDelayedOwnerProgress.lean` has SHA256 `0d2b2433c63fdd0668499ab0f4c9f7bf42952628b557317776a2871a67840286`. It has 69 lines and two public theorems: `selected_split` and `key_ne_top`.

The prior `InheritedOwnerProgress.selected_split` derives nonempty immediate descent from a same-child pair in an effective own class. Its proof uses actual inherited-first combination, component coverage, coherent tries, and literal descent. `PositiveClassOrigins.field_split` and `key_ne_top` also use the immediate prefix return. Neither existing result quantifies over later operation growth before descent.

The new `selected_split` consumes the actual successful prefix equation. It calls the old producer once and identifies its combined value with that exact returned value. Combined readiness moves forward through the supplied operation growth. `descend_correct` at the immediate and later states gives the SAME payload expression `SourceEqualityDescend.descend combined.payload index`. The proof transfers the derived nonempty payload through these equations. It retains validity, readiness, later-to-child growth, and initial-to-child growth for the SAME literal later descent. It assumes neither the desired nonempty conclusion nor a later canonical identity.

`key_ne_top` consumes those derived facts. Initial Top readiness moves forward through total operation growth, and the existing identity uniqueness law excludes equal request keys. The underlying values and owner values may differ arbitrarily. No child mass decrease is asserted.

The caller supplies later operation validity and actual operation growth from the prefix return. This permits a caller to use effects from completed earlier siblings. Growth alone is not treated as validity. The input pair must have the SAME child index and distinct residual paths. Classes that only connect different children are outside this result. The theorem starts from effective own classes, so no raw-positive-guard coverage premise is silently assumed. A caller can use existing `PositiveClassOrigins.source_guard` to derive effective coverage separately.

No full Context, native memo History, GuardHeap, selected-child return, or enclosing walk return occurs in the public contract. This component does not prove a global renewal rank, general termination, or Haskell refinement.

Both owned capped Lean commands passed. `delayed-owner-direct-1` has a literal empty log. `delayed-owner-public-1` prints complete statements, proofs, and axioms for both public heads. Its 129,474-byte log has all eight printer options, exactly the standard three axioms, and no omissions or printer failures. Each command records fresh usage and effective 4 GiB memory/high, zero swap, and a five-minute cap. There were zero failed attempts, zero owned canonical jobs, and zero constructed examples. Parent-owned canonical/integration checks remain separate.
