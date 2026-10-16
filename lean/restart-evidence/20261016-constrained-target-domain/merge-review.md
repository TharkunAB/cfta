# Actual memo-aware merge domain review

Reviewed: 2026-10-16T16:43:14+02:00.

Verdict: no material defect found in the reviewed code. The proofs derive the
finite ordinary domain for the same current memo-aware result. They do not
transfer an uncached execution or assert new language or height results.

## Actual recursion and stored winners

`SourceCurrentAllocatedFiniteOrdinaryMerge.run_domain` uses the mutual recursor
of current `SourceCurrentMemoMergeGraph.Run/Call` (lines 28–79). Its request
motive requires available domain input and returns available domain output,
physical effects, physical Stored, and structural Stored. The request branch
uses the recursive Call induction hypothesis. A miss derives `body_certified`
from its initial input facts, then uses the induction hypothesis on its actual
Run body. The candidate's ValuePost is obtained before completion (lines
67–75). No future body completion or result law is a public premise.

Completion retains `current`, the table returned by that body. Both physical
and structural remember lemmas preserve earlier entries. The final read uses
`winner_found current input candidate` and physical `hit_original` at the same
returned heap (lines 74–79). Thus a recursive reentry's earlier winner is not
replaced or silently identified with candidate. Its exact captured original
and result domain are read from the completed current table. Warm direct hits
likewise use full physical original equality before their structural law
(lines 62–66). Initial warm structural Stored remains an explicit legitimate
invariant. Empty tables derive it without a producer assumption.

## Body certificates are discharged

`MergeCode.Certified` requires actual work effects and its computed result;
request preconditions are available finite ordinary input; continuations may
use a request's ValuePost (lines 27–44). Generic run_domain explicitly takes a
static certificate. The public call_domain derives this certificate for its
literal request, and each miss constructs its body certificate internally
(Merge lines 69–70 and 81–89).

Local body proofs derive ordinary values for the exact constructors.
Domain plus coherent available records derives cached closedness where the
physical selection/constructor APIs need it (MergeCode lines 91–120). No new
closed-input premise is added to call_domain. `retained_certified` proves
recursiveBoundary false from each input's domain and thus excludes the
makeUnion branch (lines 126–150). Column selection uses literal retain and
distinctNodes membership to retain domain originals (lines 152–166). Small
rows recurse on exact resident children and retain full raw guards. Large
groups use actual columns, then actual Top edge construction (lines 168–202).
Root/body certificates use actual source groups and coherent makeNode readback
(lines 221–256). No all-guards-empty or equality-classes-empty premise appears.
Neither clear truth nor Top truth is needed for this structural theorem.

## Allocated and full checked transfer

`allocated` takes the supplied allocated Call, calls its existing physical
verified theorem, and applies the domain theorem to `actual.graph` (Merge
lines 102–113). The graph erasure is the exact CURRENT memo-aware graph:
AllocatedMergeGraph Run.graph/Call.graph preserve input/output, before/after
heap, and completed table at every instruction (lines 157–179). Only the
separate equality allocation of topRow is projected away. Actual allocated
effects independently retain that allocation. This erasure does not invoke
an old cold worker or equate distinct existential executions.

`finite` constructs an actual current allocated Call from initial physical
Ready, physical Stored, and availability, then verifies that same Call with
initial structural Stored and input domain (lines 115–125). Its imported
call_complete uses current memo-aware completion followed by actual allocated
call_lift. It has no future callback premise.

`merge` wraps the same actual full checked Merge (lines 127–143). ClassReady
is explicit here because the checked operation state and loaded fields must
be retained. It is not required by generic call_domain. Native structural
Stored is unchanged because advancePhysical retains both native result tables.
No Inventory/At or future semantic result is smuggled into this endpoint.

## Scope and evidence

Reviewed Merge source SHA256:
`22fc4bccb3362795fb7032da17451d6df29ca3d4888958e6d37ffbdda95d3bbf`.
Reviewed MergeCode source SHA256:
`eabab8ddf1f8037587afe47a919b6476113c73a18d6ee658c0ecff7b2eeed3ff`.
The existing parent merge-build-1.log records success with 1260 jobs and only
the historical unused inputs warning. This review ran no compiler or Lake.

This closes the identified current completed-merge DOMAIN component. It does
not add a merge min/max height theorem, target/slot/class structural theorem,
new native completion theorem, general Mu/union result claim, or host forcing
correspondence. The initial physical and structural cache facts remain
explicit. The completed serial source model retains its earlier publication,
concurrency, HashMap iteration/allocation, and GHC boundaries. Guard fields and
nonempty classes remain admitted by this component. No Haskell defect or
repair was found.
