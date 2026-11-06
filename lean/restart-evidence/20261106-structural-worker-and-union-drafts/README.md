# Unchecked worker and union proof drafts

These files use the `.lean.txt` extension. The normal Lean build excludes them.
No file in this directory adds a checked theorem.

- `partial327.lean.txt` preserves the selected-step statement. Its frozen header has 3628 bytes, eight caller gates, five fuel witnesses and nine universal binders. It replaces the observed-pair and equality tactics with primitive cases. Diagnostic328 exited with code 1. Filter329 found six matching error headers: one at line105 and five at line177. All 430 compile-context checks and all 445 filter-context checks passed. The diagnostic text remains opaque.
- `candidate334.lean.txt` preserves the same statement. It uses a fixed bind rewrite and total match projections. Diagnostic335 exited with code 1. Classifier336 found one known-source error header at line 104, column 10. Classifier337 matched a fixed rewrite-failure prefix there. All 471 compiler, 952 location-filter and 965 prefix-filter context checks passed. The error suffix and cause remain opaque. Global error completeness is unestablished. This draft adds no accepted theorem.
- `union-originality-v3.lean.txt` states a union-only equivalence under Facts and Available. It relates input originality to value originality. It does not prove that the value is original. Its first Nix diagnostic exited with code 1. All 454 context checks passed. A bounded classifier found one known-file type mismatch at line 103. Explicit nonunion cases replace that fallback in v5. The check used the supported `-j1` and `-DwarningAsError=true` flags. A strict kernel-control claim remains unestablished.
- `union-originality-v4-conditional.lean.txt` removes only the first import from v3. Its environment sufficiency is unestablished. It was not compiled.

The general provenance theorem and the common input-derived bound remain open.
All older drafts, failures and unknown correspondence conditions remain recorded.

`union-originality-remaining-obligation.txt` states the remaining union goal. The proof must derive `Original` for every actual union member from the unchanged `Facts` and `Available` premises. The checked equivalence does not construct these witnesses. The note supplies no new premise, proof or concrete counterexample.

The corrected v5 proof is in `../../MicroCFTA/SourceRecursiveIntersectionUnionOriginality.lean`. Normal Lean accepted its temporary check and the exact repository module in the pinned compiled environment. All 473 and 481 context checks passed. The new theorem report lists only `propext` and `Quot.sound`. The report is in `union-v5-new-theorem-type-and-axioms.txt`. The v3 and v4 files above remain failed or uncompiled drafts.

To check the new module with installed project dependencies, run from `lean`:

```sh
env -u LEAN_SYSROOT nix-shell ../shell.nix --run 'lake env lean -j1 -DwarningAsError=true MicroCFTA/SourceRecursiveIntersectionUnionOriginality.lean'
```

This check uses the existing compiled dependencies. It does not establish complete source/object equivalence, a recovered strict kernel-control protocol, or Haskell correspondence.
