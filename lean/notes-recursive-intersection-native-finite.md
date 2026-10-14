# Finite native observations from actual original roots

Proof checkpoint: `2129c3ed`. Upstream: `f59c198d`, 2026-10-14.
Earlier component checkpoints: `9a86559c`, `08340409`, and `88abb29e`.
Read [request progress](notes-recursive-intersection-request-progress.md)
and [native correctness](notes-recursive-intersection-native-correctness.md).

## Original scope and all compiled request limits

`SourceRecursiveIntersectionRequestScope.NodeScope` retains original syntax,
availability in the fixed source heap, and original Mu bindings. `EdgeScope`
retains the original ordered row children and their resident rows.
Scope extends through actual Mu allocation. Original binder reads retain
their payload, availability, and exact `.mu name` input codec after growth.

`SourceRecursiveIntersectionCodeBounds.Below` retains this scope and a strict
least semantic request bound at every recursive instruction. It excludes
explicit source failures and native finish instructions. Actual work, domain
allocation, reads, and successful optional binders use their exact returned
machines. Recursive continuations accept available values after valid source
growth. They do not assume callback purity or a supplied completed run.

`below_bind` and `below_walk` preserve the invariant through actual sequencing
and ordered walks. `compileNode_below` derives it for every physical branch.
`compileEdge_below` derives it for arity mismatch and every ordered paired
child. The other compiler-bound modules cover Mu requests, union and row
walks, child requests, and original reference reads.

`successful_action` derives a successful selected semantic branch from the
parent request certificate. It excludes incompatible payload branches and
unsupported control. It also excludes unbound reference requests. Original
binding readback excludes missing physical payloads. `mu_identities` derives
both actual source identities from selected recursive control. No successful
child execution is supplied as a premise.

## Word ranges on actual finite prefixes

`SourceRecursiveIntersectionNativeWordRanges.WordRanges` checks the existing
machine-word bounds at each memoized request reached by an actual finite
yielded prefix. It requires no completed native execution or sufficient fuel.
Prefix composition, source-body extraction, and actual completed bodies
retain these resource checks at their exact remaining continuations.

`Evaluation.bounds_of_ranges` constructs the earlier inductive word-bound
certificate from actual completed evaluation and this resource premise.
The completed-run correctness theorem can therefore derive strong memo
validity, exact source growth, available results, and stable kernel meaning.
Machine-word bounds remain an explicit resource premise.

## Finite native observation

`NativeBodyProgress.BodiesBelow` is an internal induction interface for
strictly smaller original requests. `node_terminal` and `edge_terminal`
use actual lookup and demand. Published handles cannot be absent. Checked
keys identify the captured original request. Its strict semantic decrease
excludes a busy demand.

A new demand weakens the active bound to its own request limit. A completed
body derives concrete `Produced` from the existing completed-run theorem.
Its original frame finishes its own cell and restores the stronger caller
bound. Returned source and memo states remain exact. Completed hits use
their proved replay and available result. Unresolved source references keep
the direct memo bypass.

`code_terminal_of_bodies` uses structural code induction through every actual
continuation. `code_terminal` closes the smaller-body interface by strong
induction on the semantic request limit. Neither theorem assumes finite
native completion or a body termination contract.

`NativeConstructorObservation.ReturnsOrPending` has exactly two cases:

- A successful native return with its actual value and complete native state.
- A pending constructor with its actual installed key, remaining code, and
  complete native state.

It has no source failure, absent-handle, busy, or yielded case. Its sequencing
lemmas preserve an exact pending constructor through appended code.
The more general `Terminal` lemmas still retain exact source failures for
arbitrary code. They do not identify failure with successful return.

`cold_node_terminal` starts from two actual closed original available roots,
complete source facts, a valid domain cache, and empty native memo tables.
It derives the initial semantic certificate and active invariant. Under
`WordRanges`, some finite native bound returns or reports an exact pending
constructor. No native trace, prepared result, callback execution, or
completion provenance is supplied. `done_correct_of_ranges` derives full
guarded source correspondence whenever the actual outcome is a return.

## Remaining successful-completion obligation

Finite return-or-pending is not successful completion. The next target is to
exclude pending optional binders at the actual source states and bodies
reached by this driver. `SourceRecursiveIntersectionMaybeMu.complete` already
does so under complete payload coverage and `PreparedWithoutMu`. Derive the
needed conditions for the intended input scope, or prove the larger nested
constructor invariant. Do not add a supplied no-pending callback contract as
a replacement for this source proof.

`PreparedWithoutMu` allows opaque closed nested Mu records. It excludes
dynamic open nested Mu requests. Closed original roots can contain such
requests beneath an outer binder. Closedness alone does not establish this
preparation premise. General output preparation also remains open.

After successful native completion, derive actual physical
`ProductReadback.members` and `.rejected` from child/row traces and canonical
returned rows. Then apply `product_exact`. Do not assume equivalent product
language or row contracts. The exact reference, solver-decided, and optimized
Sized source laws remain proved independently of this recursive path.

## Validation and preservation

The pinned Lean 4.34.1 aggregate audit passes 1,291 jobs and 41,663 theorem
dependency checks. Only `propext`, `Classical.choice`, and `Quot.sound` are used.
Log: `/tmp/mcfta-native-returns-or-pending-20261014-audit.log`.
The intermediate finite-observation audit passed 1,290 jobs and 41,645 checks.
The prefix-resource audit passed 1,284 jobs and 41,637 checks.
The all-branch request-bound audit passed 1,281 jobs and 41,625 checks.

No Haskell source changed. The prior Nix and formatter results remain the
source validation checkpoint. All 1,515 saved Lean-tree files remain.
Only the five recorded audit and coverage files differ from that original
manifest. The three marked drafts and retained counterexample keep their
original hashes. Both stashes and the other worktrees remain unchanged.
All work remains local.
