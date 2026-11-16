# Actual cases and source APIs

SourcePruningEnumerationSharedDispatch.afterQuery:35 and dispatch:55 are the exact operations.

- Equal source and target: literal no-op action, original caller and queries.
- Missing source: no action, original caller.
- Eliminated source: no-op, original caller.
- Enumerated source: missing target or invalid-intersection enum action, original caller.
- Missing, eliminated, or enumerated target: no native call; original caller.
- Either source/target unbound: finishOptional enum action, original caller.
- Either full native handle lookup missing: no native call; original caller.
- Both lookups present: the exact source-first/target-second emptyDomain checked request at supplied nativeFuel.
- Native yielded, failed, constraintError, or blocked: same outcome's state advances the returned caller.
- Native done: same actual query/queried state enters afterQuery.
- checkEmpty=false: actual skipped phase.
- checkEmpty=true with descendant false: shared check skips.
- checkEmpty=true with descendant true: actual shared conjunction call at p/h/currentTupleBudget.
- Optional-check completion/fault and encoded/unencoded replacement: caller follows the same actual phase state.

SourceCurrentUnionNormalNativePrograms.request:213 covers all checked request outcomes without a future physical/model premise. SourceCurrentSharedUnionNormalConjunction.call:211 covers the actual shared conjunction. SharedIncomingUnionNormal.run_unionNormal:32 covers the later incoming operation separately. SharedDispatchQueryEvents.observe_exact:65 supplies the already-public branch structure used for this proof. No adequate-completion theorem or legacy Incoming law is used here.
