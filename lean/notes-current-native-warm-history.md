# Exact serial native query histories

Source main is `8f85ddb6`. The preceding published proof checkpoint is
`3e84dab7`. Proof commits are `ef5bbc8e`, `2bdf6641`, and `c8fe3b9f`.
This update changes no Haskell implementation or test. The Haskell fix
handoff near the top of root FINDINGS.md remains current.

## One input model covers the complete operand inventory

SourceCurrentAllocatedNativeInputInventoryModels.finiteInput constructs one
input interpretation from a finite list of closed Original operands that
are available in the source heap. Its domain is the union of input
reachability from those operands. Every root uses the same physical
representative function. The domain stays in the actual finite issued
inventory. No synthetic union node is allocated.

root_valid derives membership for every listed root. root_language derives
its exact original physical language. The model describes original inputs.
It assumes no generated result law. Empty lists and repeated operands are
allowed. No distinctness premise is required.

## Actual warm query completion

WarmQuery.query_complete keeps the original source and finite input model
fixed. It starts from physical Good, both contextual and scope cache
invariants, SemanticReady, Idle, source growth, and issued history. Each
query has closed Original operands available in the fixed source and valid
in the same input model. Reached WordRanges remains explicit.

The original input schedule derives independent request completion. Source
growth derives current operand readiness. The existing paired contextual
and scope inductions derive both actual returns. completed_unique identifies
their literal values and complete checked states. The resulting receipt
retains the actual physical trace and effects, both cache invariants,
SemanticReady, Idle, result availability, an empty free list, and exact
original intersection language. It has no supplied parent law, future
completed child, final invariant, or language-readback callback.

## Literal completed memo cells and unchanged repeats

CompletedMemo.completed_node reads an actual completed checked request.
For a cacheable key, it derives the final table handle and returned cell
with the exact original request and result. A miss preserves its original
evaluating cell through the actual body and protected finish. A hit derives
the original request from physical key validity.

completed_repeat then derives a two-step repeat with the whole checked
state unchanged. repeat_of_trace obtains initial readiness and key safety
from the first instruction of the actual physical trace. It requires no
supplied final memo cell. A request with no key retains its actual direct
body path. No warm-hit claim applies to that case.

The live Haskell node wrapper in Data.CFTA.Interned.Operations looks up
the ordered original operand keys before its body dispatch. A placeholder
bypasses the node memo. These proofs retain that order and distinction.
They do not prove GHC thunk publication or concrete flat-table behavior.

## Complete serial walk and cold admission

WarmHistory.program is the literal Code.walk of empty-domain requests.
walk_complete derives one actual trace for the complete ordered list.
It restricts the whole-walk WordRanges to the head. The completed head's
actual trace then derives the continuation and tail ranges. No future
per-query completion or range callback is supplied.

The head's returned invariants admit the tail in the same fixed model.
The composed receipt retains all final physical and semantic invariants,
closed resident results, and ordered pair/result language laws. Actual tail
completion preserves every earlier published key and returned cell.
Receipt.warm therefore derives unchanged two-step repeats for every
cacheable historical query at the final state.

ColdHistoryExact.cold_complete derives the fixed model from both operands
of every listed query. It derives initial Contextual, Scoped, and Idle from
literal empty native tables. It supplies every query's model membership.
Only initial physical Good, SemanticReady, original closed available
operands, and reached WordRanges remain at this cold history boundary.
There is no initial warm-cache or model-validity premise.

## Remaining integration and full scope

This history uses one fixed source heap and a finite inventory of original
operands. Newly allocated operands and generated intersection results are
not automatically admitted as later original inputs. Cross-model cache
admission remains separate. The result concerns serial checked-machine
execution. Runtime capacity, allocation order, GHC forcing and publication,
concurrency, concrete containers, and other global memo families retain
their correspondence boundaries.

Next derive initial Good and SemanticReady from complete original
allocation, normalization, and loaded-field histories at the actual caller
boundary. Compose native completion with the current class Scan and
constrained outer caller. General constrained completion and every other
full-library target remain active. Keep exact Sized classes, counts,
finite execution, actual order, and both inverse laws as separate contracts.
Preserve the optimized interned core and all older constructor/equality work.

## Validation and preservation

The pinned full Audit passes 2294 jobs and 56040 theorem dependency checks.
Across the five new modules, 21 public axiom reports, 21 signatures,
37 kernel examples, and two named kernel theorems pass. The named theorems
also have two axiom reports. Only propext, Classical.choice, and Quot.sound
occur. Canonical builds repeat only the old unused-input warning.
Two independent integration reviews found no material defect.

Evidence and frozen source copies are in
restart-evidence/20261016-warm-history/. Failed intermediate logs remain
unchanged. Final green logs are identified by the validation records.
The starting manifest covers 3291 tracked files. All 2288 older non-Audit
proof sources must retain identical bytes. The final preservation report
records that check and the preceding frozen module manifests.

The unchanged Haskell source retains the strict Nix all-component build,
777 examples plus golden, five-file Fourmolu, and four-package Cabal-gild
evidence recorded in FINDINGS.md. No local Haskell test changes occur.
Earlier missing external draft bytes remain unavailable. They are not
claimed recovered or reverified.
