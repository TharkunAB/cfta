# Reference and absent-node failure consumers

Status: source-only inventory. Zero Lean, Lake, canonical, runtime or official-edit jobs. No implementation is authorized.
Dependency: OuterClosedInputs.reached, NodeStored and InputsClosed are proposed, not checked. Their frozen historical plan is an input; this inventory does not upgrade its status.

## Existing endpoints and exact gap

1. Worker.nodeBody emits unexpectedReference only for a literal `.reference name`; its caller is unchanged [S1:74–95]. Value.free for that constructor is `[name]` [S2].
2. Worker.nodeCall emits nodeMemo(handle,absent) only from the actual beginNode absent observation [S1:60–71]. nodeCall_absent is a forward equation, not an inverse [S1:195–200].
3. ExecutionAncestry.failed is BUSY-only [S3:683–693]. ParentFailure.failed and EdgeMemoFailure.failed invert different fault constructors [S4,S5]. No existing public inverse for either requested fault was found in the complete rare-constructor search recorded in search-inventory.json.
4. ActiveAncestry.Reached.failed propagates an already supplied reached failure back to the entry. It does not find a cut from a failed run [S6:245–295]. Do not use it in the reverse direction.
5. The reusable actual inverse pattern is ParentFailure.all_failures: private six-phase fuel induction, literal Outcome.bind inversion and ExecutionAncestry.Step constructors. Completed earlier siblings contribute only their actual done equations [S4:21–178]. No future return, semantic oracle or new activation graph is needed.

## Smallest proposed consumer

6. Propose one public no_reference_or_node_absent with the SAME genuine initial resource packet as pending ClosedInputs.reached, initial NodeStored and initial InputsClosed. Its two conclusions exclude the two literal failed-run equations. The exact header is proposed-signature.lean.txt.
7. Keep two private cut conclusions, stated in proposed-private-cuts.lean.txt. They use only actual failed execution. They return the SAME final caller, the literal captured reference body, or the exact absent beginNode tuple. No new datatype or generic failure framework is needed.
8. reference_cut returns Reached first (.body fuel ⟨inherited,.reference name⟩ after). Apply pending ClosedInputs.reached ONCE to THAT cut. InputsClosed there is `[name]=[]`, a contradiction. This does not inspect or ban references bound inside opaque Mu.
9. absent_cut returns Reached first (.node fuel request before) and beginNode request before=(handle,.absent,after). No closure theorem is needed for this arm.
10. Derive initial NodeValid from Context.sound.valid.nodes with existing Valid.keyMap, or Protocol.of_valid.nodes. ExecutionAncestry.Reached.valid transports it to THAT same before [S3:407–412,S7]. A private node not_absent proof uses only this pure Valid and the literal beginNode definition [S8,S9]. Its existing edge analogue is InitialEdgeMemoFailure.not_absent [S10:32–38].
11. A lookup hit has a present cell by Valid.linked. A miss publishes a suspended cell; demand returns evaluate. Hence neither case returns absent. No NodeIdle, EdgeIdle, current semantic context, canonical request equality or closure premise is needed for this local absence fact.
12. The combined header uses one common packet for the reference arm. A separately exported minimal no_node_absent could take only NodeValid at entry; it would not depend on OuterClosedInputs. Do not export an additional corollary unless root requests the split.

## Review and limits

The missing work is real cut extraction, not a two-line application of an existing inverse. Keep one local joint inversion proof for these two fault constructors. Do not copy all existing busy-owner/resource/closure inductions or introduce an arbitrary-fault framework.
Both private cuts and the consumer remain unproved. Root must approve the complete plan/header and extraction scope before implementation. Complete source review must precede any compiler job.
This result would exclude only unexpectedReference and nodeMemo(absent). Busy, edge memo, Parent, binder, inherited and exhaustion cases retain their separate contracts. No first adequate outer fuel, capacity envelope, successful graph or unrestricted termination follows.
Authorship disclosure: the reviewer authored the local ResourceParentClosed dependency and several resource/native adapters inside the genuine packet. This inventory does not independently re-certify those proofs.
