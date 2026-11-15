# Actual edge query endpoint residency

Status: existing public API found. The application example is UNCOMPILED.
No new public theorem is needed. No compiler was run for this packet.

`SourceCurrentAllocatedNativeRequestResults.edge_result` proves the requested
residency at the complete returned `after` state. Its inputs are weak physical
cache validity before the request and the actual completed protected physical
trace of the same literal `requestEdge`. The theorem retains the full request,
domain, operands, before state, returned row and after state.

The application keeps the original supplied execution fuel and its exact done
equation. The existing theorem needs only the stronger trace observation. The
proof does not change the execution fuel, request or endpoint.

## Actual cases

- The protected first step supplies actual `EdgeReady` and key safety.
- Actual lookup preserves weak physical cache validity.
- Absent and busy observations cannot yield a completed physical trace.
- A ready observation reads `EdgeGood` from the same actual returned cell.
- An evaluating observation splits the same protected body and finish trace.
- `finish_edge_result` obtains residency from the actual `finishEdge` input.
  The finish and terminal pure trace retain that heap and identify the full
  returned row. No child residency premise or extra growth transport is needed.
- Actual edge queries have no direct dispatch branch. Node direct dispatch
  does not change the edge query cases.

There is no semantic language premise, model, strong thunk validity, future
producer premise or replacement evaluator. This local result does not prove
that a whole worker trace exists. A caller must still supply its actual
protected trace and initial weak physical cache validity. Root may use this
existing result to remove a separate row residency assumption from the actual
scan child interface.

The original full coupled target header is copied byte for byte. Whole family
provenance, compatible completion and worker history remain open. The packet
contains no live source, Haskell, Git, board or temporary-directory changes.
