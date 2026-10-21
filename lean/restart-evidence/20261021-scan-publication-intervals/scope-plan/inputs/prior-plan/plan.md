# Actual gate and conjunction publication intervals for Scan

Status: SOURCE-ONLY PLAN. The proposed interval heads are unproved. This package runs zero Lean or canonical commands and changes no official source. The earlier Scan store plan and owner-count plan stay frozen.

Three local heads suffice for the publication intervals: primary class, secondary class, and actual conjunction memo call. Their results are intervals between the exact supplied entry and return heaps. They need no initial publication history, whole-root cap, changed false gate, or future Parent return. A caller composes its genuine initial history with each derived interval.

## Proposed heads

`SourceCurrentGatePublicationHistory.primary` and `.secondary` take the SAME actual class trace, entry SemanticReady, CostHeap, and availability of the literal input forest. They return `Nonempty (NativeMuPublication.History before after)`. They cover BOTH Boolean results, including actual primary TRUE and secondary FALSE. No stored-guard predicate is a premise.

`SourceCurrentConjunctionPublicationHistory.call` takes the SAME `ConjunctionMemo.Call budget memo query before answer after saved`, physical `ConjunctionRowsAllocation.Ready before`, and query availability. It returns `Nonempty (History before.heap after.heap)`. It needs no fourth-memo semantic Correct law because it proves an actual heap interval, not answer soundness. An open query can take the literal no-work branch. A warm hit keeps the exact physical state.

Complete proposed public types are in `proposed-signatures.lean.txt`. No public result predicate or new history framework is needed. The first implementation should be the gate module only. The conjunction module can follow after the gate source review and checks.

## Gate proof from the actual constructors

The primary and secondary logical graphs already retain every actual unfold equation and intermediate heap. Adapt the small mutual node/child/edges induction and ordered path/class proof in `GateGuard`. Replace its guard-heap postcondition with a causal interval. Do not copy its guard executor or add a new tree abstraction.

- `empty/reference/union/finite/endpoint/constrained/closed`, missing lookup, and empty traces have identical entry/return heaps. Use `History.refl`.
- `branches` receives the SAME node's actual child forest through availability.children. Use its indexed EdgesTrace induction.
- `present found` uses the SAME lookup to derive the selected value's availability.
- At `unfold`, retain the literal equation already in the trace constructor. Public `RequiredPublicationHistory.unfold value before semantic.ready available` gives a history to that actual operation's stopping heap. Rewrite with the SAME `.done next middle` equation. Use `OpenOrdinaryHead.unfold_complete` and the actual outcome injectivity to obtain middle SemanticReady/availability. Use actual `unfold_cost_heap` for middle CostHeap. Compose that interval with the SAME recursive tail interval.
- Ordered edge/path/class `next` composes the head interval before the tail interval. Existing actual primary/secondary Effects supply the exact intermediate SemanticReady, CostHeap, Keeps, and availability needed by the tail. They do not stand in for a publication history.
- `stop` returns just the reached head interval. It adds no unexecuted suffix.

The primary and secondary Boolean policies differ at constrained Mu and endpoints. Do not convert a secondary trace into a primary trace. Follow each existing trace type directly. The only heap-changing node constructor in these traces is its recorded unfold; no row collector clone is needed. Estimate 175–220 lines for both public heads and private finite trace helpers. Review the complete draft before the first job. [R1–R4]

## Conjunction proof from the actual resident schedule

Use the precise existing `ConjunctionGuard` chain with interval composition and public Required publication endpoints. This preserves the literal sequential schedule; it does not assert host forcing order.

| Actual constructor | Interval producer and exact intermediate premises |
|---|---|
| `CompletionReads.Exposures.cons first rest` | Call `RequiredPublicationHistory.read first` on the SAME Read. Read effects derive tail SemanticReady/CostHeap and retain the remaining input values. |
| `CompletionReads.Projections.cons first rest` | Call `RequiredPublicationHistory.forest first` for the SAME forest/path. Projection effects derive the next state and retain later job inputs. No all-root cap or closedness is needed by this interval helper. |
| `Requirements.ClassRequirements.cons first rest` | Use the SAME row-major jobs. `jobs_inputs` and `Projections.verified` derive actual intermediate facts. Compose the projections interval before the remaining class interval. Canonicalization changes only the returned value list. |
| `Requirements.run sameArity actual` | Delegate to that SAME ClassRequirements; child-column canonicalization performs no heap operation. |
| `RowsAllocation.Tuple.contradiction` | Equality fold changes only the equality-operation cache. The constructor heap is literally unchanged: use reflexivity. |
| `RowsAllocation.Tuple.live folded classes requirements` | Retain folded/classes equations and use the SAME Requirements heap interval. Equality allocation contributes no constructor heap segment. |
| `Tuples.skip/keep` | Use `Tuple.verified` for actual intermediate Ready and resident/closed old tuples. Compose both actual intervals in order. |
| `Rows.run reads tuples` | Compose actual Exposures before actual allocated Tuples. Existing `ConjunctionTuples.tuples_verified` derives each chosen tuple's resident and closed fields. |
| `Worklist.Run.done/empty/skip` | Reflexivity or the SAME unmodified recursive return; do not add rows for a skipped group. |
| `Run.admit nonempty fresh rows rest` | Actual `EmptinessTable.admitted ... fresh` derives closedness of THIS admitted group. `ConjunctionGuardUniverse.rows_heap` derives returned readiness and available generated requirements. Compose SAME Rows interval before the actual remaining worklist. |
| `Decision.open_input` | Exact unchanged physical state. |
| `Decision.closed closedInput explored grown` | Use the SAME actual Run interval. The finite Boolean table fixed point `grown` changes no heap. |
| `Memo.Call.hit found` | Exact unchanged physical state, even when the original memo payload differs syntactically from the query. No writer identity is needed. |
| `Memo.Call.miss absent actual` | Use the SAME actual Decision interval. Insertion changes only the fourth memo. |

Closedness is local where the resident conjunction graph needs it. Run admission derives it for the current group. The public call does not ask all initial forest roots to be capped or even closed. The physical Ready input already supplies current semantic/cost/field/equality validity. Estimate 170–220 lines using the existing public effect producers and private finite helper chain. There is no semantic obstruction in the inspected constructors. These heads still require proof/checks. [R5–R9]

## Exact Scan composition and remaining closure obligation

At a literal successful Scan step, obtain the actual primary/secondary graphs and exact checked return shape through `AllocatedGateWorker.primary_graph/secondary_graph` and `.primary_done/.secondary_done`. Gate effects and `GateGuard.primary/secondary` give current physical/semantic/arbitrary-guard facts. Those same physical returns keep native node/edge tables unchanged. Use `CurrentNative.advance` and `NativePositiveSupportAdvance.advance` on those actual extensions. Compose INITIAL causal History with the new actual gate interval. `Grows` alone supplies neither history nor old cache laws. [R10]

For primary TRUE / secondary FALSE, `SecondarySeededSupport.class_support` derives an actual retained secondary anchor, same original forest availability, and exact mapped proper-path support. `SecondaryProjectionSupport.Support` is closedness OR a false secondary trace. It is not a Plain cap. Properness is a genuine SAME precheck output in `AllocatedLocalReduction.checked.classes`, not a changed false-primary trace. [R11]

A seeded fold projects its actual head, runs the actual tail, then makes an actual empty-domain native request at the literal tail return. Projection intervals use public `RequiredPublicationHistory.forest`; their native cells remain unchanged. Each CLOSED native leaf can now use checked `NativeCurrentStores.step` to return Current, positive Support, and actual causal History without root caps. This is the checked new 75-line dependency (SHA 48b80476a09c7b4c3f5ce1ef1b35b45cadc6acc6d6f7a401637cadb4f010a728). Its supplied operand closure remains essential. It does not prove result closure. The copied checked append snippet has SHA recorded separately; this package does NOT whole-file live-pin old NativeRequestPositivePositions e62. [R12]

The actual fold's closure/readiness requirement is separate:

1. Genuine `ConjunctionClassScan.Ready` includes Scoped native cells and Idle, in addition to physical Good/SemanticReady/CostHeap. Current/conditional Support/causal History alone do not imply this unconditional scope store.
2. Proper original secondary support plus actual projections derives closed projected operands. Existing `AllocatedSeededQuery.operand_complete/fold_complete` returns both closure and Ready components, under its genuine anchored support and WordRanges inputs. Existing numeric producers derive those ranges under their explicit Frames/resources.
3. For a strictly literal-success Scan theorem that avoids external resource forecasts, a small actual CLOSED native-Trace scope adapter remains to be assembled. Public `AllocatedNativeScopeCompletion.initial_complete` has exactly the needed Scoped/Idle/result-closed conclusion, but takes WordRanges. An actual physically admitted Trace to pure should derive those word ranges: any raw yielded prefix matches a prefix of the SAME deterministic completed trace; its next node/edge is physically checked, or the prefix ends at pure where Words is True. No public theorem for that conversion was found in the inspected trace/bounds APIs. Do not silently assert it or supply a future-callback law.
4. With that range conversion, existing scope completion constructs a scoped return; actual completion uniqueness aligns it to the SAME supplied native result/state. This requires real initial Scoped and Idle, not an all-root cap. It is a local follow-up, not a new support ledger.

The new interval heads do not themselves complete this scope adapter or a whole Scan proof. The actual final physical conjunction call is simpler: its returned native tables are unchanged, so its stores advance through actual Effects/Guard facts; the new conjunction interval composes its history. Existing RequiredPositiveChronology already carries laws through the completed Required/selected-class continuation. No duplicate selected-branch induction is needed. Historical cold/warm Parent writer-entry laws remain a later ledger task. [R13–R15]

## Frozen evidence scope

This package contains the plan/types, exact ROOT source/range snapshots, and the frozen new CurrentStores/append snippets as local dependency inputs. Its verifier checks only those bytes and source ranges. No Lean, Lake, canonical, proof printer, fixture, or Audit command was run. There are zero new public or constructed proof pairs. The checked dependency receipts belong to their owner and are not counted here.

Root can authorize the gate candidate after reading the plan. The complete candidate must be read before any proof job. A later authorized job must use fresh usage and effective 4 GiB max/high, swap 0, and 5-minute caps, preserving all attempts. Gate and conjunction stay separate components.

## Source map

R1: primary/secondary trace constructors and GateGuard mutual/path/class proofs. R2: RequiredPublicationHistory.unfold/read/forest. R3: OpenOrdinaryHead.unfold_complete and actual source unfold cost preservation. R4: primary/secondary child/path Effects. R5: CompletionReads Exposures/Projections. R6: Requirements ClassRequirements/Requirements and tuple_inputs. R7: RowsAllocation Tuple/Tuples/Rows. R8: Worklist.Run and Decision. R9: ConjunctionGuard exact composition templates and Memo.Call. R10: gate graph/return inversion, Current.advance and SupportAdvance, actual conjunction table retention. R11: secondary class_support and precheck properness. R12: actual Seeded Fold/worker and locally pinned checked CurrentStores. R13: Ready and ScopeCache. R14: ScopeCompletion.initial_complete, WordRanges/Words, physical Inputs, raw/physical Trace APIs. R15: RequiredPositiveChronology public pass.

Exact selected line intervals and whole-file hashes appear in `ranges.json` and `source-pins.json`.
