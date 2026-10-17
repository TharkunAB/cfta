# Literal native joint closure and progress

Reviewed: 2026-10-17 04:42 CEST.

No counterexample to joint cap/classifier closure was found. There is a concrete counterexample to strict `pairRank` descent for every recursive call.

## Exact recursive graph

`compileNode` retains the source order Empty, reset, closed self, swap, and repeated pair before Mu, union, reference, and ordinary branches. Ordinary compilation calls `compileRows`, walks the ordered hash-join row pairs, and requests each edge. `compileEdge` checks equal arity first. Its accepted branch walks the literal child zip, requests each node, then performs edge work. Its mismatch branch performs only sentinel edge work. The current checked body additionally loads both original equality fields and rejects before emitting child code. Its accepted `children_eq_compileEdge` adapter retains the literal combined guard; generic compiler execution alone does not model those extra equality operations.

Mu compilation enters the actual extended domain, requests the original stored bodies, then calls actual `maybeMu`. Union compilation walks original members in order, then performs union work. Reference compilation checks the domain name, reads the actual source record, then requests the bound Mu and opposite operand. Reset and swap request again. Empty, self, and repeated return locally.

## Rank and progress

`NonplainRank.zip_pair_lt` is strict for ordinary zipped children when either full parent is nonhereditary. `NativeOccurrenceCompile.row_budget` gives a strict row maximum at positive parent rank, including the empty-zip case. Union-member rank is strict only when the selected union is nonhereditary. A hereditary union with a nonhereditary opposite operand need only be nonincreasing. Swap and reset preserve rank. A hereditary Mu and its body have rank zero; a bound reference and its legitimate annotated bound Mu also have rank zero. Mu exposure in a mixed request can therefore preserve positive rank.

The source-built raw `mu x. x` versus a constrained nullary ordinary value enters a body request with unchanged positive rank and the same sorted numeric pair. The extended domain's repeated-pair guard closes it before dereference. Thus rank alone does not prove global termination. Native busy demand remains blocked and is not a successful intersection.

Existing progress is more precise. `RequestProgress.initial_complete` derives semantic completion from closed original available source inputs. `physical_child_requiredFuel` strictly lowers the least successful semantic request bound for every actual selected child. `compileNode_below` and `compileEdge_below` retain that bound. `Native.code_terminal` combines strong induction on this bound with structural code induction, actual source/history, valid/active memo facts, and explicit `WordRanges`. `cold_node_complete` uses complete semantic heaps and coverage to exclude pending construction. `warm_node_complete` adds valid idle warm tables. These are progress interfaces, not the new joint structural law.

For joint preservation on a supplied completed trace, strong induction on actual trace length is sufficient. Each smaller literal child supplies the cap law and source-indexed classifier to ordered row/child/union helpers. Maintain a single returned context with current validity, semantic and guard heaps, immutable source growth, and issued history. Reset/swap need exact domain and request transport. Repeated results need the source-weight/pair-rank identity. Mu entry needs actual binding extension and complete stored body readback. Optional binder needs the produced joint callback/probe observation before first-writer publication. A losing candidate does not certify an earlier winner. Warm native cells must carry the joint conditional law for their complete captured owner request.

`NativeOccurrenceCompile` already certifies rows, children, and both union directions under recursive local laws. It does not itself supply full native induction or completion. Its `Certified` excludes finish instructions. Actual native lookup publishes and starts its owner before body execution, then finishes the same handle. These owner frames must remain explicit in the supplied-trace proof.

## Constructive checks

`joint-native-probe.lean` contains two no-premise kernels. Each builds original source operands from empty, then runs the literal generic native executor at width 8 and fuel 128. The exact same request then runs with fuel 2 at the actual returned full state.

* Raw `mu x. x` versus a constrained nullary ordinary input returns Empty. The warm repeat preserves its entire native state.
* Raw `mu x. (plainConst | plainStep x)` versus `badStep(plainConst)` returns the exact original nonhereditary ordinary input. Production `GuardDepth.profile` equals `some 1`; the output has `Cap 1` and is not hereditary. The warm repeat preserves the value and entire native state. The cold run uses eight node memo cells and two edge memo cells. Constructor work hits existing records; its node counter stays 9.

These kernels do not assume a completed query, result cap, callback law, or future state. They specialize the generic literal compiler/native worker to Boolean guards, with allowed guard `true` and conjunction `Bool.and`. They do not exercise current checked equality-cache loading or rejection. No Haskell runtime defect or full-library completion follows.

The final public log contains 19 complete axiom/signature pairs. The final kernel log contains two pairs. Both are strict-clean with no `sorryAx`. The executable first attempt passed. Two intermediate proof drafts failed from missing namespace imports; both sources and raw logs remain preserved. All handles are terminal. No production file changed.
