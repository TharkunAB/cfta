# Generic callback output blocks

Status: COMPLETE CANDIDATE. UNCOMPILED. All declarations were frozen before proofs.

Normal module: MicroCFTA.SourcePruningEnumerationSharedCallbackOutputBlocks.
It imports the existing eager and scan-origin modules. No owner-private dependency
or runtime code is changed. Appendable probes have no import lines.

OutputBlock records an entire callback list inside the actual visitor output,
with ordered prefix/suffix, exact local indexed occurrence, and global offset.
CallbackBlocksAt is a proof-only law for a fixed child visitor and input value.
The generic tuple/selected combinators consume this local law. The final actual
eager theorem must derive it by genuine height induction; it is not a premise
for the final real-source callback-origin theorem.

The tuple proof uses list induction. It composes a whole head callback block
with a whole tail callback block. The stopped head forwards the original
stopped callback with an empty prefix of completed fragments. The selected
proof inverts the literal prepare result and retains the actual complete or
stopped selected consumer receipt. Other preparation shapes call the actual
unhandled/rejected consumer. The shallow proof inspects the literal shared
ChildDispatch result. consumeSelected retains the whole done block; every
noncomplete receipt emits no output.

The fixed implicit width, Output, and Reason parameters are explicit only where
standalone propositions would otherwise leave them unconstrained. The earlier
header-only draft is retained. No premise, runtime budget, output list, stop
behavior, or checker limit is changed. Default checker limits apply.
No compiler was run. The actual eager height theorem is a separate packet.
