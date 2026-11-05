# Unchecked worker and union proof drafts

These files use the `.lean.txt` extension. The normal Lean build excludes them.
No file in this directory adds a checked theorem.

- `partial327.lean.txt` preserves the selected-step statement. Its frozen header has 3628 bytes, eight caller gates, five fuel witnesses and nine universal binders. It replaces the observed-pair and equality tactics with primitive cases. Diagnostic328 exited with code 1. Filter329 found six matching error headers: one at line105 and five at line177. All 430 compile-context checks and all 445 filter-context checks passed. The diagnostic text remains opaque.
- `union-originality-v3.lean.txt` states a union-only equivalence under Facts and Available. It relates input originality to value originality. It does not prove that the value is original. Its first Nix diagnostic exited with code 1. All 454 context checks passed. Error classification is pending. The check used the supported `-j1` and `-DwarningAsError=true` flags. A strict kernel-control claim remains unestablished.
- `union-originality-v4-conditional.lean.txt` removes only the first import from v3. Its environment sufficiency is unestablished. It was not compiled.

The general provenance theorem and the common input-derived bound remain open.
All older drafts, failures and unknown correspondence conditions remain recorded.
