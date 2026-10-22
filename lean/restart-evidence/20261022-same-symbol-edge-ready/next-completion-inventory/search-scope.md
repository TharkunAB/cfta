# Read-only search scope
Search root: lean/MicroCFTA, live .lean source files.
Patterns: call_eventual; ready_rows; source_schedule_total; Completes.*edgeSemantic; edgeSemantic.*Completes.
Additional patterns: theorem/def edge completion; call_numeric; WorkReady/Completes; NodeScope.rows; EdgeReady.
Observed direct generic semantic producer: IntersectTotal.call_eventual with .edge WorkReady.
Observed closed physical initial producer: SourceRecursiveIntersectionRequestProgress.initial_complete, node-shaped result.
Observed child producers: physical_child_requiredFuel and IntersectImmediateCalls.immediate_requiredFuel, each with actual child membership.
Observed native edge_complete APIs retain an explicit semantic Completes premise.
Observed SourceCurrentAllocatedNativeInstructionTrace.edgeBudget_of_complete retains that premise; edgeBudget selects zero when it is absent.
No public physical-row-packet to empty-domain edgeSemantic Completes adapter was found by these searches.
This is a bounded source search result, not a proof that no equivalent formulation exists.
