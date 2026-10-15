# Original equality-field allocation and current cold entry

Source main is `e16f3b50`, merged at `50f21a5f`. Its core constructor,
equality, native, enumeration, and Sized bodies match `2ca1644c`. Full library
scope and the optimized interned core remain. Earlier proofs and drafts remain.

## Actual earlier constructor receipts

`SourceEqualityOriginalFieldOrigins.Origin` retains an earlier successful
`SourceEqualityConstraintAllocation.construct` call, its valid initial
interner, and table growth from its returned interner to the current one.
It does not assert a desired lookup answer. `of_construct` supplies this
receipt after an actual constructor call. `Origin.grows` retains the same
call through later canonical table growth.

`Origin.load` derives successful read-only field lookup, the exact original
guard and equality readback, stored-value readiness, and the physical
constructor receipt. It uses normalized original equality fields. It does
not allocate a missing field at the request site.

`constructed` follows the actual repaired graph build. The existing complete
literal inventory includes every child and stored binder body. An earlier
allocation receipt for each literal derives that receipt at every resident
original edge key. Constructor hits, probe bodies, and discarded records
remain covered by the source annotation heap proof. `resident_lookup`
derives each resident original field's current lookup result.

## Derived current entry and scan soundness

`SourceCurrentClassOriginalFields.constructed` composes these allocation
origins with the original native initialization proof. Actual source build
derives native IdleReady, CostHeap, normalized FieldHeap, available closed
root, and available children for every resident original edge. Each edge
also has a successfully loaded ready field with exact original readback.
`closed` derives the finite original build and these initial facts.

`cold_scan_sound` first derives a loaded value from the original allocation
inventory. For that SAME value, every actual live allocated prefix and
completed current Scan excludes rejection of a public accepted original
edge. No successful lookup or original class-satisfaction premise is
supplied. Valid operation tables, ready inherited storage, actual prefix,
and completed Scan remain explicit. The result covers the live class branch.

## Source boundary

`Constraint.constraintEqualities` is strict in `Constraint.hs:110`.
`EqConstraints` carries a strict identity in `Equality/Constraint.hs:265-278`.
Its public construction calls `internEqConstraints`. The separate cache is
global and uses `unsafePerformIO` (`Equality/Constraint.hs:280-287`). These
source facts motivate the earlier allocation inventory. They do not prove
GHC evaluation order, physical input erasure, or global cache publication.

The proof does not create a new allocation schedule. Actual GHC construction
must still supply a synchronized inventory of earlier field allocations
and the retained current interner. The node/edge heap and equality interner
remain separate stores. Normalized FieldHeap alone cannot supply this
inventory. Native cold initialization does not reset the equality interner.

The full caller still needs its unchanged, combined-contradiction, rejected,
and selected fallback branches. The fallback must retain original children
and selected records at the actual scan-final state. Path-local support must
survive requireAll, shared target construction, and class edits with unrelated
open siblings. Merge/subsumes global reads and their separate merge memo,
costs/fields, full operation-state transfer, general completion, machine
bounds, runtime correspondence, and broader library contracts remain open.

## Validation

The focused build passes 1,212 jobs. The aggregate audit passes 2,114 jobs
and 52,819 theorem dependency checks. Only propext, Classical.choice, and
Quot.sound occur. The old unused `inputs` warning is the only warning.
Evidence: `/tmp/mcfta-normal-form-original-fields-build-20261015.log` and
`/tmp/mcfta-normal-form-audit-20261015.log`.
