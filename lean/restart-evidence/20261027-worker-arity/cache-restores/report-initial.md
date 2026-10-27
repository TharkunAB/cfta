# Caller and raw reconstruction arity review

Status: source-only drafts. The two v1 files are immutable. Root has not yet supplied strict or installed-build receipts for these files. No compiler, build, Git, network, or board operation ran in this task. No repository file changed.

## Actual operations and conclusions

`SourcePruningEnumerationCallerArity` has six theorems. `beginNode_heap`, `beginEdge_heap`, `finishNode_heap`, and `finishEdge_heap` specialize actual caller-table updates. These operations retain the entire checked state. They do not require a successful demand or a returned caller-table cell. `advance_node_execute_heap` and `advance_edge_execute_heap` use the literal native query outcome state in the full returned caller. They derive whole edge-record Heap from original physical Good, original Heap, and InputsThrough for that actual query. They cover finite done, yielded, failed, constraint-error, and blocked outcomes through the existing native execution theorem. They have no desired post-Heap premise.

`SourcePruningEnumerationRawRebuildArity` has two theorems. `edge_heap` treats the actual raw makeEdge call. Initial Heap, coherence, and original edge residency give Fits for the original payload count. The actual equal child-count receipt transfers that check to the copied raw guard. `modify_heap` handles both literal modifyNode branches. The identity branch retains the state. The other branch creates a node and does not change the edge-record table. Neither theorem changes an existing runtime or contract.

Draft files:

- v1/SourcePruningEnumerationCallerArity.lean: 79 lines; SHA256 7a4d29d0f1c1d92cf18837234cc76af18f3d9180c0c275283555429c0a53a89b.
- v1/SourcePruningEnumerationRawRebuildArity.lean: 46 lines; SHA256 70eed91fda1a8cb9f7c2851d5952c7217782a21d4ac11d9bbd02424210219c06.

## Source boundaries

PartialState.lean:52-87 defines the full caller and actual begin, advance, and finish operations. Its existing component receipts at 103-138 retain all other caller fields. QueryMemo.lean:102-115 shows that advancePhysical takes the supplied physical heap exactly and keeps the native node/edge tables and domains. This equality is not a proof that an arbitrary supplied heap satisfies Heap.

RawRebuild.lean:29-50 runs raw makeEdge and the ordered-identity modifyNode branch. Its EdgeReceipt at 65-76 carries the actual same child count. PartialNodeRebuild.lean:17-24 either returns the same state or runs makeNode. ArityOrigins.lean:24-43 defines Heap and derives payload Fits from coherent residency; 71-97 proves actual makeEdge, makeNode, and makeUnion preservation. NativeExecutionArity.lean:65-92 supplies the all-outcome native query proof used by CallerArity.

PartialWorker.lean:60-171 shows where these lemmas apply. Caller-table ready/busy/absent branches retain checked state. Node and edge bodies thread the actual returned caller. An inherited-prefix update changes operations while keeping the same constructor heap. A raw edge rebuild follows the actual child walk. A whole-worker theorem must derive its walk length and retain original residency at that intermediate heap. The Mu reconstruction and ParentWorker calls remain separate actual creation obligations.

NativeBranches.lean:21-43 and NativeContinuations.lean:41-71 restore the captured enumeration Cached input for siblings. They advance the native Caller and Queries through the actual head or hook result. The restored enumeration cache does not restore the native heap. OrdinaryContinuations.lean:20-43 only passes its original caller to the entered fold. Recursive.lean:61-76 executes recordTypes on enumeration state. It passes the same caller and queries to its recursive continuation. The recursive continuation can allocate native records and needs its own induction result.

SourceEndpointMemo.lean:122-157 takes a value and memo tables. It has no constructor-heap argument or result. This fact does not cover the whole endpoint gate: EndpointMemoGateTrace.lean:83-91 has a real stored-substitution unfold with a returned constructor heap. That operation needs the existing stored encoding/reconstruction proof at its exact reached state.

NativeCacheGrowth.lean:11-32 transports CacheValid for the same captured enumeration cache through actual Keeps or Post. Keeps preserves old records. It does not restrict new keys. CacheValid and Post do not provide whole edge-record Heap for an arbitrary newly reached heap.

## Integration scope

Arity's ClassPass/RawEdit task owns the ordered schedule induction. SharedEditGraph uses direct makeEdge and makeNode, so it can use ArityOrigins directly with its actual returned child-count equation. This task does not prove SharedTargetLeaf Force plus TargetQuery arity. That leaf needs an actual creation receipt chain.

No theorem here derives initial Heap from Context alone. No theorem assumes a future successful trace, a desired final Heap, a per-history arity certificate, or assignment satisfaction. No theorem proves preservation for an arbitrary hook or an arbitrary caller.advance argument. Full partial-worker, endpoint-unfold, parent/reduction, and recursive-history composition remain open. This is a formal correspondence boundary. No runtime defect is claimed.

## Provenance and review scope

source-pins.json preserves 14 exact whole source copies and 19 literal inspected cuts, with 546 cut lines. Each record gives its original absolute path, whole SHA256, copy path, and exact line spans and cut hashes. Whole copies preserve provenance; the detailed review scope is the listed cuts. The draft additions do not replace, alter, or weaken any original source contract. This folder remains open for Root's actual strict and installed-build receipts.
