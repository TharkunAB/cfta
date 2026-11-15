# Actual incoming union-normal preservation

Status: UNCOMPILED DRAFT. Only Root may compile or promote this module.
No live source, old packet, Git state, board entry or /tmp file was changed.

The main theorem is `SourcePruningEnumerationIncomingNode.run_unionNormal`.
It proves UnionNormal at the actual returned caller projection of `run` for
arbitrary representativeFuel, nativeFuel, p and h. It includes zero budgets,
raw errors, unsupported encodings, failed checks and incomplete native outcomes.
Its only logical premise is UnionNormal of the original caller heap. It does
not require completed execution, a model, Post, resource admission, pending
realization, input closure or a future callback certificate.

The module also provides:

- `SourceCurrentAllocatedTargetQuery.Step.unionNormal`, from Step.done and
  SourceCurrentUnionNormalNativePrograms.request at the literal empty-domain
  requestNode and its actual completed return.
- `SourceCurrentAllocatedTargetQuery.Receipt.unionNormal`, from its actual Step.
- `SourcePruningEnumerationEnabledEmpty.check_unionNormal`, for every actual
  returned checked state, including a failed physical call.

## Actual operation connection

The incoming run uses the exact native requestNode for `incoming` and the old
node decoded at its actual original heap. The existing request theorem covers
ALL outcomes of execute at the supplied nativeFuel. No alternate backend,
completion bound or sufficient-budget result replaces that execution.

EnabledEmpty.check executes the exact endpoint memo and, if enabled, the literal
AllocatedTupleConjunctionWorker.call with p, h and currentTupleBudget. That
adapter has the same defining body as AllocatedConjunctionWorker.call: both
match the same ConjunctionDemandWorker.call and install the same advancePhysical
endpoint. Existing SourceCurrentUnionNormalConjunction.call therefore applies
by definitional equality. Its proof covers actual done and failed endpoints.

The main proof follows the established IncomingGuardHeap.run_heap case split.
Cases with no native call retain the original caller. Native incomplete/error
cases retain request normality. The done case derives enabled-check normality
and follows both phase outcomes and both replacement-encoding branches. It
keeps the original literal caller, query memo and all supplied budgets.

## Scope

This result is for SourcePruningEnumerationIncomingNode.run, exactly as requested.
It does not silently substitute SourcePruningEnumerationSharedIncomingNode.run.
UnionNormal is the existing stored-union structural invariant. This result
alone does not produce a domain model or finite completion, and it does not
close the main worker/history induction or the full joint-witness objective.

The four probes are in PROBES.lean.txt. Source hashes and exact primitive headers
are preserved here. Static checks verify byte pins and prohibited proof markers;
they do not count as Lean elaboration or proof credit.
