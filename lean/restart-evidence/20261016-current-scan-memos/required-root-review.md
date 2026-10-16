# Current allocated Scan and required continuation review

Date: 2026-10-16 08:21 CEST.
Read-only review. No build or source edit ran.

## Verdict

No material defect found. The constructed endpoint derives finite current
Scan execution and its successful required-path continuation. It has no
public completed Scan, completed `requireAll`, selected-record callback,
future result law, or initial `At` premise. Initial history, construction,
coverage, residency, inherited readiness, memo invariants, and reached
ranges remain explicit.

## Successful state and memo composition

`RequiredGlobalMemos.scan_required_memos` uses the same actual successful
Scan for both global memo receipts and required completion. The required
worker starts at that Scan's literal final constructor heap. The derived
required `Receipt.stable` supplies finite worker bounds and a literal
`requireAll` done equation. `requireAll_memos` consumes that equation with
the Scan's derived semantic/cost/readiness facts and returned global
bundle (lines 57-68). No future physical or memo validity is supplied.

The required receipt advances the same checked state with `advanceHeap`.
It retains both native memo tables, the domain cache, and exact operation
state. Its effects retain loaded fields, stored costs, and original
residency. Its `At` uses the concrete inventory returned by the Scan.
The required stage returns unfolding-table extension and equality of both
global query tables with their Scan-final versions. It does not claim
those tables equal their pre-Scan versions, since actual gates can update
them.

`records_required_memos` derives `Retained` from the actual Scan. The
receipt identifies literal original record positions, preserves order and
multiplicity, and retains complete trie fields. The coherent/ascending/
nontrivial facts follow by original-record membership. Selection is not
supplied by an answer function or reconstructed from path equality alone.

The required domain comes from selected primary certificates replayed at
the actual Scan-final heap. These are proof certificates, not extra source
gate calls. Required completion and language use selected-path support;
unselected original siblings need no closedness premise. The result's
language is the original child-forest language with the required path
condition. Later equality-class edits are not included in this claim.

## Constructed public endpoint

`AllocatedRequired.finite` derives physical entry and record facts from
the actual covered allocation history, constructor build, resident field
load, and live accessor/precheck. `prefixState` retains the actual returned
equality operations. Cold native tables derive the initial empty-inventory
`At` directly. The theorem constructs an actual finite current Scan rather
than accepting its completion as input.

The stopped branch retains the prior uniform original-class refutation.
The success clause is an implication from that actual outcome being
`none`. It is a case split on the constructed result, not an assumed
successful future computation. Under this case, the theorem derives
retained original records, actual required completion, all required global
receipts, final global validity, and fourth-memo correctness. The physical
required receipt and global receipt use the same `results` and heap.

The public stopped branch in this particular wrapper returns its stated
refutation and Scan-final `Ready`/`At`. It does not export a required-stage
receipt on that branch. Full stopped Scan global receipts are available
from the separate allocated-global endpoint. No stronger stopped result
is implied by the successful continuation clause.

## Retained limits

The endpoint is conditional on an actual source build and live precheck,
initial original-field history coverage, a ready inherited physical
payload, initial global table validity, initial conservative fourth-memo
correctness, and reached machine ranges. These are initial/current model
conditions. The completed operation tables are the documented cold
projection over the retained interner, not a production-global cache reset.

The proof covers the current checked Scan and required-path worker. Later
class edits, whole constrained outer-caller completion, host table and
machine-identity adequacy, GHC lazy forcing/publication, and global unsafe-IO
initialization remain separate. The new headers preserve these limits.

## Evidence inspected

`required-global-build-2.log`: terminal success, 1284 jobs.
`allocated-required-build-1.log`: terminal success, 1348 jobs.
Only the preexisting unused `inputs` warning appears. No build was repeated.

```text
5d8356fac226b13a9e991beb1c0c8ab80a5489e90a0416977f01cd18650cc7b0  SourceCurrentConjunctionRequiredGlobalMemos.lean
3888e7d3187d2343af627c24a6d4faf8edd004cef0618b9f32e07f6eccc71175  SourceCurrentConjunctionAllocatedRequired.lean
ebcb0053a8760f6a1c831d8d89253c2dc1243f25fac8ba06a646dd3a42d9359e  SourceCurrentConjunctionRequired.lean
05eed7d11bc26435351edf0d0a6bf840d47b11b7c51bc97474621efbfe4f5cd0  SourceCurrentConjunctionSelectedRecords.lean
```
