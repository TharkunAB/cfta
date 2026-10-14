# Independent guarded language and actual stored plans

Updated: 2026-10-14 15:48 CEST. Proof checkpoint: `b3008aba`.

## Independent meaning

`InternedGuardedLanguage.meaning` interprets complete actual stored records.
A reference reads a language from an environment indexed by `Reference`.
A node retains each actual source symbol, full guard, and ordered child list.
A union denotes its member languages. A Mu denotes the least language of
its actual body at its own interned name. This definition ignores probe
metadata and cache allocation. It does not call the cold reader.

`meaning_mono` proves positivity. `mu_unfold` proves the least-language body
equation. `forest_all` identifies the ordered forest with `Language.All₂`.
`laws` derives the ordinary constructor interface for this interpretation.
The guards are arbitrary predicates on complete finite terms.

`InternedGuardedSyntax.evaluate` gives the complete lexical source syntax
its independent guarded meaning. Variables read their lexical positions.
Both binder forms denote the least language of their body with one new local.
`evaluate_mono` and `binder_unfold` prove positivity and unfolding.

## Actual metadata and normalization

`InternedGuardedLanguageSupport.meaning_free` follows coherent available
records. Actual cached free names contain every ambient reference that
the independent meaning can read. `closed_meaning` therefore makes a closed
captured record independent of the ambient environment.

`InternedGuardedConstructors.makeNode_exact` and `makeUnion_exact` apply the
proved actual normalization laws to this independent meaning. They retain
complete guards and child order. `unused_mu`, `self_mu`, `cleanup_exact`,
and `finish_exact` prove the actual smart cleanup and both finish paths.

`InternedGuardedSelfFilter.filter_closed` follows the actual callback root
filter and its union reconstruction. The original and filtered bodies have
the same closed candidate languages. `filter_least` and `filter_mu` derive
the same least language. No preparation, productivity, or literal identity
reconstruction premise is used.

## Actual stored compiler

`InternedGuardedStoredPlan.encode_language` interprets the exact
`InternedStoredSubstitution.encode` plan. Coherent canonical slot lookup
retains each closed captured record. Local names read the nearest lexical
slot. Open Mu records compile to lexical least-language binders.
The theorem covers arbitrary nested records and arbitrary lexical languages.
It keeps full symbols, guards, and ordered forests.

`execute_plan_language` specializes the theorem to the actual simultaneous
replacement map. Each original free name gets the ambient meaning of its
actual optional replacement. Closed captured records remain constants.
`unfold_plan_language` proves that the exact outer-Mu unfolding plan has
the independent least language of that Mu.

These are compiler laws. They do not yet identify the actual returned record
of `InternedFreshOrdinaryConstruction.build` or repaired `execute` with the
independent source-plan language. They do not use an assumed execution law.

## Next proof

Prove actual repaired source execution and a semantic probe-heap invariant
together. Cover canonical hits as well as fresh request completion.
Use exact coherent probe readback. Use actual fresh-name bounds and
`meaning_free` to keep captured languages unchanged under local binding.
Use actual normalization, cleanup, and root-self filtering from this checkpoint.
Do not replace a canonical hit with the candidate record that it discarded.

One candidate invariant equates the stored Mu's independent least language
with the least language obtained from its ordinary probe. Bind the probe's
actual name `.uninterned (ordinaryLevel depth)` to the candidate language.
Quantify over ambient environments and guards. This invariant is a proposed
proof target, not a theorem. Check its exact freshness requirements before
using it. Full body-transform equality can be stronger than necessary because
the root-self filter preserves closed candidates and least languages.

After execution correspondence, connect the actual final repaired graph and
finite table to the independent language. Then derive physical
`ProductReadback.members` and `.rejected`. Exact final-cache graph language,
native heap propagation, and finite native output tables are already proved.
The raw unused-binder identity counterexample still applies.

## Validation

Lean 4.34.1 passes 1,401 aggregate jobs and 43,344 theorem dependency checks.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. Log:
`/tmp/mcfta-independent-guarded-compiler-20261014-audit.log`.
No production Haskell source changed. Existing Nix and formatter checks remain
applicable. The earlier proofs, counterexamples, and marked drafts remain.
