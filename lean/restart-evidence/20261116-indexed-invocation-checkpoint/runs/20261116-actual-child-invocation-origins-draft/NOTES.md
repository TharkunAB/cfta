# Actual shallow and eager indexed invocations

Status: UNCOMPILED. Both public headers were frozen before proof. No logical proof credit is claimed.

Normal prospective module: `MicroCFTA.SourcePruningEnumerationSharedChildInvocationOrigins`. It imports only the normal invocation-combinator module. That module depends on Canonical's frozen invocation ABI and checked existing scan APIs. Root owns dependency staging and serial compilation. The candidate does not use an import overlay or the large resource owner.

The shallow theorem derives the trace from the literal `ChildDispatch.run` result. Every nonsuccess branch proves `ShallowStopped` and uses the literal stopped callback. A completed singleton with a current cache uses `shallow_done` and the exact done callback. The retained output list and callback index are unchanged.

The eager theorem uses genuine `Nat.strongRecOn` on ordinary height. The actual ordinary guard determines the scan route. Its guarded child policy uses the induction hypothesis only when the literal lower-height test is true. Otherwise it uses the proved actual shallow trace. No selector, membership, Packet, resource or source-shape premise is added.

For an ordinary scan output, the checked indexed scan block origin gives the actual earlier complete prefix, producing row, row output index and whole output block. Canonical's selected producer derives a trace for that SAME row and its consumer index. Only then does the proof invert `consumeSelected`: noncomplete receipts have no outputs. The actual complete selected trace is retained in `ChildInvocationAt.eager_ordinary`. Its terminal index is the same index at the original done callback. The root output block is composed from those same concrete rows and callbacks.

The return values contain BOTH the invocation trace and a full output block. Both use the same terminal index. No constructor is obtained from an extensional output block. All retained stopped outputs, duplicates and original order remain in the lists.

The generic width and Output/Reason universes are unrestricted. The module sets no checking budget and changes no algorithm, fuel, callback or result constructor. It does not prove a full recursive worker history, all-raw alias transport, a compatible historical assignment or accepted original-root completion.
