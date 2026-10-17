# Initial bounds for complete checked native query instructions

Recorded: 2026-10-17 07:17 CEST. This is a read-only source survey. The recurrence below is proposed. No complete instruction-count theorem is claimed here.

## Existing complete execution and strict request rank

`IntersectSchedule.requiredFuel` in `IntersectRequiredFuel.lean:43` selects the least successful SEMANTIC fuel for an exact source view and request. It is not a checked-machine instruction count. `requiredFuel_positive` at line 58 proves every complete request has rank at least 1, including leaves. Thus a count recurrence can use a zero base case without treating a real rank-zero request.

`SourceRecursiveIntersectionRequestProgress.initial_complete` (`SourceRecursiveIntersectionRequestProgress.lean:77`) derives semantic completeness from actual closed original operands and source Facts. It calls `SourceRecursiveIntersectionInputView.source_schedule_total` (`SourceRecursiveIntersectionInputExact.lean:100`). This supports the full original Mu/union/reference family. It does not require the later physical query result. The selected `requiredFuel` is an initial-only mathematical value; it is noncomputable in the current declaration. A computed syntax-only upper bound on it is a further theorem.

The exact strict-child APIs are:

- `SourceRecursiveIntersectionRequestProgress.physical_child_requiredFuel` (line 33) for actual selected node branch calls; `entered_requiredFuel` (line 53) identifies the allocated Mu domain with its semantic domain.
- `SourceRecursiveIntersectionCode.compileNode_below` (`SourceRecursiveIntersectionCompileNodeBounds.lean:18`) produces `Below` at the parent's least rank through the actual continuations.
- `mu_request_below` (`SourceRecursiveIntersectionCompileMuBounds.lean:74`), `leftReference_below` / `rightReference_below` (`SourceRecursiveIntersectionCompileReferenceBounds.lean:17,43`), and `leftUnion_member_below` / `rightUnion_member_below` / `rows_member_below` (`SourceRecursiveIntersectionCompileChildBounds.lean:38,52,66`) retain original scope and strict rank decrease.
- The CHECKED edge APIs `SourceCurrentAllocatedNativeRequestBounds.child_below`, `children_below`, and `body_below` (lines 21,41,85) cover the actual accepted child code and rejected sentinel code. The generic eager `compileEdge_below` is not a substitute for this checked branch.

`SourceCurrentAllocatedNativePhysicalTraceCompletion.request_complete` (line 517) already constructs its own complete physical Receipt from scope, completeness, Good, readiness, growth/history, ActiveAbove, and WordRanges. `node_complete` / `edge_complete` (lines 487,502) construct body returns. None of these endpoints bounds the constructed `fuel` by initial syntax or semantic rank. Their private `all_bodies` and `code_of_bodies` contain the relevant induction, but currently erase quantitative lengths.

## Fixed original operands give fixed branching

Yes: within one query, recursive request operands remain in the fixed source, even when their returned constructor results grow. `SourceRecursiveIntersectionCode.NodeScope` and `EdgeScope` in `SourceRecursiveIntersectionRequestScope.lean` contain initial-source availability or row residency. Their `mu`, `rows`, `child`, `leftUnion`, `rightUnion`, and `OriginalBindings.read` producers preserve that source. Results are consumed by constructor continuations. They do not become operands of later recursive source requests in that query.

Let `R`, `M`, and `A` be the initial `SourceRecursiveIntersectionSourceProfile.limits source` fields for rows, members, and arity. Its `node_scope` / `edge_scope` (lines 164,171) derive these bounds from actual source payloads. `binding_read` (line 212) recovers the same old Mu at a later read using record growth and issued-key extension. Therefore matched row schedules have length at most `R*R`, union schedules at most `M`, and child zips at most `A`, without a bound on current returned payload mass. `pairs_length` / `node_pairs_mass` in `SourceRecursiveIntersectionCompileMass.lean` retain multiplicities; no uniqueness claim is needed.

Alternatively use an INITIAL `InternedValueMassHeap.Stored B0 source`. Its `available` and `resident` laws bound each original operand. Then rows and members are at most `B0`, row pairs at most `B0*B0`, and child zips at most `B0`. This does not bound the mass of generated returned children by `B0`. Ordered walk length, rather than returned mass, controls the outer request schedule.

## Proposed conservative recurrence

Define `L = max 1 (max (R*R) (max M A))` and

```
T 0       = 0
T (h + 1) = 4 + L * T h
```

Count YIELDED checked steps until the returned pure control. The final `execute` step that observes `.done` costs one more. For a request of semantic rank `h`, every recursive request has rank less than `h`; monotonicity of `T` bounds it by `T (h-1)`.

| Actual request branch | Conservative yielded cost |
| --- | --- |
| Warm hit | 1 |
| Node leaf miss | request + finish = 2 |
| Node Mu miss | request + enter + optionalBinder + finish + child = 4 + child |
| Node reference miss | request + read + finish + child = 3 + child |
| Node ordinary or union miss | request + Work + finish + child sum = 3 + child sum |
| Checked edge miss | request + checked body + Work + finish + child sum = 4 + child sum |

Reset and swap add at most request + finish around one smaller request. Direct unmemoized nodes omit the finish. Guard rejection skips the child schedule. The recurrence therefore covers these paths conservatively. It counts one complete Work or optionalBinder as one CHECKED instruction. It does not count the constructor operations inside that instruction, solver work, or Haskell execution time.

## Smallest full-scope additive producer

Add a quantitative certificate for the ACTUAL compiler skeleton, with bind and ordered-walk addition, atomic effect cost 1, and each recursive request charged by `T` at its strict semantic rank. Derive this certificate for `compileNode` and the actual checked body from initial SourceProfile and the existing strict-child APIs. `Below` alone is insufficient: arbitrarily many `.read` or `.work` instructions can satisfy the same `Below` bound without any recursive request. The certificate must retain instruction counts as well as rank decrease.

Prefer an instruction-credit code/control invariant analogous to `CodeMass.At`. Its initial credit is `T h`. Each actual yielded step consumes at least one credit. Native request expansion distributes the remaining credit to the smaller body, its captured finish, and the existing continuation. Ordered list continuations use their fixed original lengths. This can bound EVERY physically checked prefix by the initial credit, rather than only counting after completion. The actual source rank and initial branching limits determine that credit; no Receipt fuel is selected as an initial budget. Combine this producer with the existing raw-prefix admission induction.

The protected-body proof can reuse `SourceEqualityNativeDemandPrefixSplit.steps_bind_cases` / `Steps.length_le_complete` (lines 16,60), `SourceEqualityNativeDemandRunning.node_body_cell` / `edge_body_cell` (lines 216,227), and `SourceCurrentAllocatedNativeRunning.node_finish_active` / `edge_finish_active` (lines 258,269). Do not erase the finish or substitute a newly looked-up owner. After the initial credit producer is proved, a public bounded `request_complete` can reuse old completion and bound THAT SAME trace. It must not choose the initial bound from the returned Receipt fuel or copy completion merely to add a length field. Its public input needs no completed execution or future length.

WordRanges need not be derived from the proposed total allocation forecast. Existing `SourceCurrentAllocatedRecursiveInitialRanges.initial_ranges` (line 51), and `SourceCurrentAllocatedRecursiveWarmInitialRanges.warm_initial_ranges` (line 27), derive them independently from initial source counters and finite domain-inventory room. Using generic `CapacityWords` with an assumed all-prefix capacity would reintroduce the future premise.

Warm tables require the existing admission boundary: Good alone allows a matching evaluating cell and thus a busy outcome. Complete-query construction must retain Idle or the appropriate ActiveAbove bound, along with original scope/readiness and the existing semantic/field conditions. Warm hits can only reduce the proposed count. The optional-binder success used by the old completion proof is produced by `SourceEqualityNativeDemandHeapPrimitives.optionalBinder_complete` from Ready and current body availability; its internal construction is not bounded by the instruction recurrence.

Finally compose the bounded SAME trace with the current width/mass prefix producer. Prove the required numeric schedule monotonicity before replacing actual `fuel` by `T h` in `MassTrace.massAfter` and `credit`. This would give initial-only constructor supply bounds in terms of source profiles, initial mass, and initial semantic rank. A computed syntax-only rank bound, equality-operation resource bounds, runtime correspondence, and bounds across later queries with newly generated operands remain separate obligations.
