# General closed source getPath

Updated: 2026-10-15 04:13 CEST.
Proofs: `587c633a`, `eb094eb9`, and `3dd8ee3b`.
Source: `TharkunAB/cfta`, `origin/main` at `f201deda`.
The retained traversal repair is `61f2c939`. Continue on `formalize`.

## Current scoped native target checkpoint

`69de4363`, `e03f2c4d`, and `e145fe27` derive idle warm native leaf
completion, exact source intersection lists, retained native projection state,
and one target construction/application. Read
[the current note](notes-native-target-fold.md). Full simultaneous edits,
shared target forcing, and independent merger inclusion remain open.
The earlier first-request and intersection-list next-target text is historical.

## Actual closed union

Operations.hs:657 union first checks hasEdges on its operands. Every closed
operand passes this check. The source reads nodeEdges for each operand,
concatenates those rows, and makes one ordinary node. This branch also reads
a singleton Mu or stored union. createUnion has a different request sequence.
The ordinary-only sourceUnion proof does not cover this general branch.

SourceEqualityProjectionRead.Read retains the actual completed cold row read.
complete derives finite execution and all cache invariants. unique uses
actual larger-bound replay. verified therefore applies to every successful
read. exact derives its independent guarded row language from head_exact and
makeNode_exact. Its temporary node request occurs only in the proof.
The worker does not make that temporary node.

SourceEqualityProjectionUnion.ReadAll reads operands in source list order.
Union constructs one node from the concatenated rows. verified derives
semantic heaps, both histories, resident edges, closed results, and exact
union language. Each operand stays available through prior actual cache
growth. No cold table conversion or runtime union replacement is added.
These are ordered logical call graphs; native lazy scheduling is separate.
The open-operand union branch is outside this theorem.

## Complete general signed paths

SourceEqualityProjectionGraph retains the source node, row, and forest
branches. select uses signed indexes and returns none for a negative index.
Each row selects one child or makes no recursive call. The row scan preserves
source order. Each ordinary node step executes the actual closed union.
Mu and stored union inputs first execute actual head normalization.
The empty node remains empty. The empty path on a node returns its input.
Forest root projection executes union. A missing forest position returns
EmptyNode without inspecting any payload.

SourceEqualityProjectionEffects derives every intermediate cache premise
through the common mutual graph recursor. SourceEqualityProjectionComplete
uses finite path length and complete head normalization. It supplies all
node and forest graphs for arbitrary closed available nested Mu/Union inputs.
It assumes no graph acyclicity, callback completion, or whole path-worker law.
Original closed source construction derives the initial premises.

## Independent language

SourceEqualityProjectionLanguage proves that each selected subterm of an
accepted input term belongs to the projected result language. The proof
retains actual row guards, ordered child acceptance, signed lookup, normalized
head language, and exact closed source union. The row law selects an original
accepted child and retains its suffix projection. Ancestor guards disappear
from the projected result. The contract is inclusion, not exact existential
subterm language. Missing-path terms impose no acceptance obligation.

SourceEqualityProjectionAPI.forest_root gives exact independent union
language. forest_included follows the original accepted ordered child forest
at proper paths. source combines original closed construction with finite
stable execution and independent source-expression subterm inclusion.

## Worker agreement

SourceEqualityProjectionWorker keeps worker and row-read proof bounds
separate. It retains pending records, unresolved references, worker exhaustion,
and row-read exhaustion. Bounds are proof parameters, not native API changes.
Successful worker execution gives the exact physical graph. Every finite
graph supplies bounds for every larger pair. Those runs return the identical
value and complete final constructor cache. node_execution_iff and
forest_execution_iff prove both directions. node_unique and forest_unique
follow from the actual stable run equations.

Kernel examples retain root reference priority, proper reference failure,
negative and high missing forest positions, raw self head completion, both
exhausted bounds, root node identity, and singleton closed recursive forest
union. They use cbv, not native evaluation axioms.

## Validation and preservation

The aggregate audit passes 1,671 jobs and 46,049 theorem dependency checks.
Only propext, Classical.choice, and Quot.sound occur. Only the older unused
inputs warning remains. All eleven new modules pass focused builds.
Log: `/tmp/mcfta-projection-20261015-audit.log`.
No Haskell source or formatter input changed. The earlier 645 examples and
format checks apply to the byte-identical tree. They were not rerun.

Snapshot: `/tmp/mcfta-projection-checkpoint-20261015-0413/`.
It retains 2,068 Lean-tree files and four root documents. The only older
proof change is added audit imports. All repros, counterexamples, marked
drafts, stashes, other worktrees, and production source remain.
Weekly allowance was 17% at 04:13 CEST. Stop at 1% or less.

## Next caller obligations

Retain the target's actual cache scope through simultaneous edits. Carry the
full native memo/domain state and checked word ranges at every leaf request.
SourceEqualityNativeLeaf has local immediate-cache laws. The global LeafLaw
still quantifies unrelated caches and is not yet instantiated for captured
native targets. Do not reset native memo tables or supply a whole-worker law.

Derive actual mergeAlternatives inclusion and intersection-list targets from
their source operations. Reuse the general getPath inclusion and finite
execution proved here. Compose original class edits, the ordered class fold,
and empty propagation. Preserve the completed unary ancestor theorem and
its archived draft. getAllAtPath, open contexts, full one-pass correspondence,
repeated fixed-point reduction, native containers, lazy scheduling, and
extraction remain separate obligations. Exact Sized classes, size order,
and both distinct-term rank inverses remain established and unchanged.
