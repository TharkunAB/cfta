# Fixed-model cold history and completed memo review

Reviewed 2026-10-16 06:31 CEST. This review read the current source and the
owners' validation artifacts. It did not rebuild or edit the reviewed
modules. No material defect was found in the stated checked-machine scope.

## Fixed model and original input domain

`InputInventoryModels.Reachable` is an existential reachability predicate
over the listed original operands (lines 16–19). It does not select a model
from a desired intersection result. `finiteInput` uses the same actual
physical representative function for every root (lines 55–80). The body,
reference, row-child, and union-member closure laws follow from actual input
reachability. `reachable_original` and `reachable_inventory` derive actual
original-record residency and inclusion in the finite issued carrier.

The semantic interpretation and ranks are independent finite derivations.
`finiteInputMeaning` and `finiteRankedInput` use `InputDerivation`; their
equations are proved in `IntersectInput.lean`. `root_language` uses the
closed Original physical readback theorem and `finiteLanguages_exact`.
The public inventory endpoint does not assume source-language agreement or
model validity as a callback.

An empty operand list has an empty valid domain. All closure obligations
are then vacuous. This does not make a nonempty query admissible. Duplicate
roots use the same membership predicate and physical representative. They
do not require distinct identities or unique list positions. The owner's
inventory probes check both the empty domain and duplicate-root domain
equivalence. Root-list permutation preserves this domain; it does not claim
that query execution order or final allocation is invariant under a
permutation.

## Cold adapter and actual history

`ColdHistoryExact.cold_complete` (lines 30–61) constructs one `FiniteInput`
from the complete flat operand list. It derives each listed operand's
model membership with `root_valid`. The initial contextual and scope
caches follow from the actual empty native tables. The native state is
idle. Source growth and issued history are reflexive at entry. There is no
initial contextual-cache, future-success, final-state, model-validity, or
accepted-result callback in this endpoint.

Its remaining initial premises are substantive: `Good` for the actual cold
checked state, `SemanticReady`, original/available/closed listed operands,
and the actual whole-walk `WordRanges`. `Good` includes physical native
validity, physical heap readiness, valid equality-operation caches, and
allocated field coverage. The adapter does not construct these source
heaps or initialize arbitrary missing equality fields. `WordRanges`
quantifies only over actual yielded prefixes and asks their literal key
checks. It supplies no completed body or result law, but a general machine
capacity theorem remains separate.

`WarmHistory.walk_complete` (lines 117–160) uses the actual head return as
the tail's initial state. It derives head and tail ranges from the original
whole walk by bind-prefix lemmas. It carries the same model and rank
family through the entire induction. The independently completed semantic
and scope executions in `WarmQuery.query_complete` are aligned by literal
returned-value and full checked-state uniqueness (lines 104–110). No cache
reset or model refresh occurs.

The nil history has zero yielded steps and returns the identical initial
state. The cons history preserves pair/result order and multiplicity with
`All₂`. Earlier values remain resident through the actual tail extension.
The literal head cell follows from `CompletedMemo.completed_node`; the
tail's actual completed trace preserves that publication and returned
cell. The final `Memoized` evidence therefore refers to the actual final
state, not to each query's earlier intermediate state.

`Receipt.warm` derives an unchanged whole-state repeat in two execution
steps from those final cells. For duplicate cacheable pairs, both ordered
results have the same deterministic repeat at the final state. They must
therefore be literally equal. The owner's history probe verifies this
consequence. For an uncacheable request, `Memoized` is conditional and
makes no publication or unchanged-repeat claim.

## Literal source and remaining transfer

`cfta/src/Data/CFTA/Interned/Operations.hs:480–485` selects the global node
memo with the ordered original domain/left/right keys before the body
dispatch. The closed-domain reset, self case, operand swap, recursive pair,
Mu, union, and reference branches are inside that body (lines 486–520).
Thus the returned-cell observation uses the original request key. It does
not substitute the normalized body request key. The edge family is
separate at lines 564–578.

The physical table implementation is
`cfta/src/Data/CFTA/Interned/FlatMemo.hs`. Its lookup and first-writer insert
are at lines 153–184; `memoFlatTypeableWith` uses
`unsafeDupablePerformIO` at lines 253–264. The reviewed theorems concern
the sequential checked resident model. They do not prove the GHC thunk
publication/demand bridge, concurrent winner behavior, native container
layout, or unrestricted machine identity capacity. The fixed source model
also does not admit later generated intersection results or operands from
a different original inventory automatically. Cross-model warm admission
remains separate. The history receipt does not add a `CostHeap` conclusion.

## Evidence and reviewed bytes

The owner's focused cold-adapter build is terminal success at 1128 jobs in
`cold-history-build-2.log`. Its public signature and axiom probe passes in
`cold-history-probes-1.log`. The owner's history build and probes pass in
`history-build.log` and `history-probe.log`. The recorded aggregate build
passes 2294 jobs and 56040 dependency checks in `full-audit.log`. Only the
permitted foundations and the pre-existing unused-input warning appear.
These are inspected owner artifacts, not additional executions by this
review.

Reviewed source SHA256 values:

```
7c4f83cf02014d7046a46f5099c283f66fa93931660b22d746bbac198648bb6e  SourceCurrentAllocatedNativeInputInventoryModels.lean
3c5f76fd06580132c296be30bf86eed952e224558b6c26488a2d1afdb30a0ce0  SourceCurrentAllocatedNativeColdHistoryExact.lean
383e1ed058095977a47b1eb5c6a2cbb7bd46e7e9d4ba2308238fc4a2cc70f6c0  SourceCurrentAllocatedNativeWarmQuery.lean
eb59b9b5f2f101a72446f42cc56c22e93af173c8e861d2dfa517ff2f2631860a  SourceCurrentAllocatedNativeWarmHistory.lean
f9d1753fe923b3c0c17902d2d34c3f8e723544e454dda4570008a20bd03c2412  SourceCurrentAllocatedNativeCompletedMemo.lean
```
