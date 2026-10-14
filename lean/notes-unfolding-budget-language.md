# Actual stored languages at each Mu-unfolding budget

Updated: 2026-10-14 17:18 CEST. Proofs: `e8f06e62`, `19467e4a`.

## Purpose

The final repaired graph and cold table have proved independent-language
soundness. Completeness remains open. Equal unfolding equations do not prove
least finite-run completeness through unguarded epsilon cycles. A possible
measure is the minimum finite input unfolding bound. Transport of that bound
through actual stored reconstruction and canonical hits must be proved.

This bound is separate from node-count size and public distinct-term rank.
The primary reference, solver-decided, and optimized Sized laws remain proved
at their stated source-model boundaries.

## Budgeted least languages

`BinderBudgetLanguage.Lang` assigns a finite-term language to each natural
bound. `Upward` retains accepted terms when the bound increases. `least`
intersects upward closed candidates. `shift` requires a strictly smaller
body bound. `mu` is the least language of the shifted body transformer.

`mu_unfold` exposes exactly one smaller-bound body derivation. `mu_zero`
excludes zero-budget acceptance. `mu_constant` retains the step even when
the raw binder is unused. `mu_self` excludes every finite self derivation.
`mu_self_alternative` removes direct self alternatives without changing the
complete budgeted least language. The proof uses upward candidates.

## Complete stored records

`InternedGuardedBudget.meaning` interprets actual stored payloads. References
read budget languages from an ambient `Reference` environment. Nodes retain
full guards, source symbols, and ordered children at a common bound. Unions
retain their member languages. Each raw Mu consumes one step. Probe metadata
and cache allocation do not define this interpretation.

`meaning_mono` proves positivity. `meaning_upward` proves upward closure for
upward ambient inputs. `mu_unfold`, `forest_all`, and `laws` expose the exact
binder, child, and ordinary constructor interfaces.

`InternedGuardedBudgetSupport.meaning_free` derives support from actual
coherent cached free names. `closed_meaning` removes every ambient input
assumption for closed available records.

## Actual constructor transport

`InternedGuardedBudgetConstructors.makeNode_exact` and `makeUnion_exact`
preserve each fixed-budget language through actual normalization.
`unused_mu` identifies an unused raw Mu with the shifted body language.
`cleanup_refines` proves that actual smart cleanup retains every accepted
term at its original bound. Cleanup can remove a raw unused binder, so
budget equality would be false. `finish_refines` covers both finish paths.

`InternedGuardedBudgetSelfFilter.filter_closed` follows the actual root-self
filter and union reconstruction. It preserves the upward candidates closed
under a shifted body step. `filter_least` and `filter_mu` prove equality of
the complete budgeted Mu languages.

## Exact finite input derivations

`SourceRecursiveIntersectionBudgetInput` states the open free-reference
premises at identical budgets. `original_sound` and `original_complete`
follow actual `Original` payload syntax, cached row/member/body readback,
complete guards, and ordered child derivations. Strong induction handles
recursive reference derivations in the completeness direction.

`SourceRecursiveIntersectionBudgetExact.input_exact` proves, for every closed
available Original record and every ambient environment, exact equality
between its budget language and actual `InputDerivation` at each bound.
`erase_exact` proves that existentially erasing the bound gives the independent
stored least language. No assumed copy-language or rank-transport law is used.

## Exploratory checks and remaining obligations

The local Haskell unfolding probe checked 600 generated programs, seven
finite terms, and input bounds through 11. It found no accepted root-Mu
example whose actual outer unfolding failed to lower the minimum bound.
The local ordinary-probe check inspected 651 stored Mu records from 600
generated programs. It compared actual and ordinary-probe budget acceptance
for seven terms and bounds 0 through 8. It found no mismatch. Both checks use
unconstrained guards. These finite checks do not prove either transport law.

Evidence stays local:

- `/tmp/mcfta-input-rank-native.hs`
- `/tmp/mcfta-input-rank-native-20261014.log`
- `/tmp/mcfta-budget-probe-invariant-native.hs`
- `/tmp/mcfta-budget-probe-invariant-native-20261014.log`

The temporary Lean generated-source probes did not complete quantitative
evaluation. They were stopped after source-construction evaluation was
identified as the slow stage. They give no rank result or counterexample.
No worker remains active.

Next derive budget transport through actual stored compilation, source
execution, and canonical hits. Raw unused-binder reconstruction identity
remains refuted. Ordinary language equality alone supplies no budget bound.
Then prove final repaired graph/table completeness and physical product
readback. Do not repeat the proved soundness or finite traversal results.

## Validation

Lean 4.34.1 passes 1,428 aggregate jobs and 43,534 theorem dependency checks.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. Log:
`/tmp/mcfta-budget-input-20261014-audit.log`. No production Haskell code changed.
The prior Nix and formatter results remain applicable.
