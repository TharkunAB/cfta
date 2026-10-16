# Merge profile foundation validation

Validated at 2026-10-16 19:50 CEST with pinned Lean 4.34.1. The final sources contain 353 lines before the one-line Selection linter correction and 354 lines after it.

The 29 public declarations each have a full `#check @...` and `#print axioms` pair in `merge-profile-public.lean`. Final imported output is `merge-profile-public-2.log`. The scan includes the dotted `Stored.domain` declaration. All 29 reports pass without diagnostics or `sorryAx`.

Six integration kernels pass in `merge-profile-kernels-4.log` with full signatures and axiom reports:

- Install a valid first result, then complete an invalid reference candidate. The first winner and table remain exact. The losing candidate has no certificate.
- Construct an actual warm hit from physical readback. Derive the candidate's exact owner, profile, height bound, and earlier domain certificate. The heap and memo remain unchanged.
- Use an actual ordinary column union. Derive its parent envelope and strict ordinary-height decrease.
- Use actual completed selection. Preserve source profiles and multiplicity, then eliminate the recursive-union retained-column branch.
- Erase an actual allocated group Run. Retain its exact heap, output, and memo, and derive its output multiplicity bound.
- Erase actual ordered allocated group traversal. Derive both the number of groups and the final flattened alternative bound.

Final canonical builds are `merge-profile-bounds-build-1.log` (1124 jobs), `merge-cache-projection-profile-build-1.log` (1128 jobs), and `merge-profile-selection-build-2.log` (1125 jobs). They finish successfully. They contain only the historical `InternedFreshOrdinaryClosedCompletion.inputs` warning. Selection build 1 contained a new unused-section-variable warning. The explicit `omit` correction removes it; direct 4 and canonical build 2 are clean for the new module.

Failed direct and kernel attempts remain as evidence. They are not final validation results. Direct kernel attempts 1 and 2 contain elaborator-created `sorryAx` reports after errors. Final kernel 4 has no errors, warnings, or `sorryAx`. No production proof uses placeholders.

The sources prove foundations only. The general recursive body certificate and mutually recursive actual producer remain open as specified in `merge-profile-producer-next.md`. There is no producer draft to preserve. No smaller production endpoint was added. No older proof, Audit, Haskell source, restart authority, or old evidence was edited by this component.
