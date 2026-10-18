# Positive full-row field integration

This package validates `SourceCurrentOuterRowFieldOrigins` at source SHA256
`6fd6ea71912533f1c3900f9ffa5677cfb48aaa490c1ebde16b741b578e20fa80`.
It adds no production theorem or source change.

The fixture builds one closed ordinary `pair` node. Its full row field has
own equality class `[[0], [1]]` and guard `top`. Both ordered children are the
same ordinary `leaf` node. The leaf field is plain. The fixture allocates
both fields before it starts the outer worker. Actual source construction
and allocation history derive the initial physical Good invariant, inherited
Ready, field availability, and row residency. Both outer result tables start
empty. The initial row-origin predicate follows from `Origins.initial`.

The fixture executes the literal cold `nodeCall` with outer bound 6 and all
nine lower bounds 8. The actual call returns the original node. It derives
final Good from `OuterPrefixInvariants.node_done` and all returned-cell field
origins from `OuterRowFieldOrigins.node_done`. It then proves an actual ready
edge hit at handle 0 with the same full caller. The returned full field is
exactly the original positive field, and this field differs from the plain
sentinel. `edge_call` verifies the retained field against the captured edge
request. Finally, the fixture constructs the literal completed-edge prefix
from `rows 1` to `descendants 0`. `reached` transports all-cell origins across
that prefix.

The selected declaration is
`MicroCFTA.OuterRowFieldKernels.cold_node_warm_positive_row`.
Its signature has no caller-supplied completion, graph, returned invariant,
or row-origin premise. Its private fixture proof derives all initial facts.
The public alias has the same full statement. The printed proof resolves to
that checked private proof. The selected full probe checks its complete
signature and proof and reports only `propext`, `Classical.choice`, and
`Quot.sound`.

Attempt 1 combines the then-current root draft with the independent fixture.
It fails because Required receives bound 0. It also uses an invalid `.grows`
projection on the edge-residency equality. The immutable source and complete
raw log remain present. Attempt 2 imports the final canonical root module,
uses lower bounds 8, and calls the existing `edge_grows` theorem. Its strict
log has exactly zero bytes. The full constructed probe is
`outer-row-kernels-public-1`. All three executions record effective
MemoryMax and MemoryHigh of 4 GiB and swap limit 0. The largest recorded peak
is 309 MiB. The final successful strict peak is 271 MiB.

This is one constructed completed-execution case. The final prefix starts
from the actual cold node return. It is not a proof that descendants later
complete. It does not prove a key collision, collision exclusion, a finite
fresh-request bound, or general outer termination. It contains no Mu or open
input case. It does not establish Haskell runtime correspondence.
