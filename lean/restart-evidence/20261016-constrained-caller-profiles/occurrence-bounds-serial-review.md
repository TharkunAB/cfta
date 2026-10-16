# Serial caller resources independent review

Date: 2026-10-16 19:51 CEST.

Reviewed source: `lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinarySerialCallerResources.lean`.
SHA256: `3011a8ff22ee7f18de5f3b8da8b12ff66449c07c3393a3035d4538b35b3c2990`.
The evidence copy is byte-identical.

No material defect was found.

The theorem constructs one actual Required return. It derives the returned forest's exact uniform profile, availability, semantic heap, length, and height. It uses that same returned heap and forest for the actual Projection return. Neither stage takes a supplied result, completed callback, output profile, or intermediate occurrence-count premise.

`OccurrenceBounds.children` bounds both the original forest and the returned forest from the same initial row, arity, height, and length limits. Required retains the uniform profile and does not increase height or length. Projection adds at most one node request beyond its input occurrences and adds no edge request. The cumulative bounds are therefore `2 * (count * nodeCount R A H) + 1` node requests and `count * edgeCount R A H` edge requests. Literal occurrences include repeated identities and repeated positions.

Both Work traces retain their actual endpoint heaps. Their append joins at the literal Required return. Final supplies follow from actual stage supply bounds. The budget definitions do not use final counter differences.

The imported `serial_layout_capacity` kernel constructs both stable literal returns and the same actual Forest graph. It derives both final supplies fitting the node and edge layouts from initial headroom alone. The kernel supplies no intermediate count, profile, height, or completion premise.

This result concerns the constructor node and edge supplies in the generic physical heap. It does not claim a host demand schedule, equality-operation reservation, full native query capacity, or a whole recursive caller bound.
