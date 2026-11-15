# Actual node return finish origin

Status: UNCOMPILED candidate. Root owns Lean validation and publication.

`SourceCurrentAllocatedNativeNodeReturnOrigin.returned_node_cell_finish_prefix`
derives an actual earlier finish instruction from a returned node cell.
The input is ONE literal checked Trace from `Native.initial width machine`.
Both complete memo families are empty at that initialization. The theorem keeps
the actual whole trace count and its bound by the original supplied fuel.
The final control can be incomplete. No completion or termination is assumed.

The result retains all of the following in ONE execution:

- The SAME cell handle, complete captured NodeRequest and complete returned value.
- An indexed prefix from the ORIGINAL control and full checked initial state.
- The real `finishNode handle value next` control and its evaluating owner cell.
- The actual one-step finish, full returned state, unchanged operation cache,
  literal continuation, and exact installed returned cell.
- A literal suffix from that finish to the SAME observed final control/state.
- Whole count = prefix count + 1 + suffix count; prefix < whole and original fuel.

The prefix can precede a later authentic original U/P entry in the SAME trace.
The statement assumes no ordering between the finish and another entry.
It adds no future heap extension, pattern availability, model, admission,
cache-law, Good, Fields, Clean, or recursive-result supplier.

## Proof scope

Private inverse lemmas show that lookup and demand create no returned payload.
An actual step either retains the SAME returned cell or executes the matching
finish against its evaluating captured request. Induction on the literal Trace
constructs the prefix, one-step event and suffix. Complete initialization rules
out an inherited initial returned cell. This proof uses no semantic cache law.

The result is a finish-event receipt. It does NOT identify the earlier
`compileNode request` evaluation that installed that finish continuation.
Arbitrary initial Code can contain a handwritten finish. The other bounded
producer proof must derive compiler dispatch ancestry from genuine source
controls or their actual BodyCode/Clean facts. It must not splice the unrelated
existential `Written` body from NodeWriterHistory into this indexed trace.

The full native C/M goal and SAME-root finite accepted joint witness remain OPEN.
No Haskell defect or fix was found. No compiler, live source, Git, board, runtime,
subagent or /tmp operation was performed for this packet.

## Files

PUBLIC-HEADER.lean.txt was frozen before the proof. Its SHA256 is
`64ac3ff5d7ced321138dff4e6eef049289a14c1c0ae9099debfa75cc46c52676`.
The raw source header matches it exactly. PROBES.lean.txt contains only appendable
commands. SOURCE-PINS.json records the actual inspected definitions.
MANIFEST.sha256 records this frozen packet. Failed checks must be retained and
repairs must use a NEW packet.
