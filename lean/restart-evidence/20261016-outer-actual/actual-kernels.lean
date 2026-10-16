import MicroCFTA.SourceCurrentAllocatedPartialWorkerActual

namespace MicroCFTA.CurrentOuterActualExamples
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialSourceReads
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
  {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

-- Literal root success derives its own strict schedule, physical state, all memo facts, and language iff.
example {f g s r e p h m c n budget identity : Nat} {value result : Node}
    {before after : Caller width} {inventory : Inventory} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints (.live identity []))
    (available : Available before.checked.native.machine.heap value)
    (ranges : SourceCurrentAllocatedPartialWorkerRanges.nodeCall f g s r e p h m c n budget ⟨.live identity [], value⟩ before)
    (done : SourceCurrentAllocatedPartialWorker.nodeCall f g s r e p h m c n budget ⟨.live identity [], value⟩ before = .done result after) :
    ∃ next final, ∃ actual : NodeCall budget ⟨.live identity [], value⟩ before result after,
      NodeCallReads formulas solver actual memos final ∧ Checks (nodeCallTrace actual) ∧
      Post formulas solver next before after final ∧ At formulas solver next after.checked ∧
      InternedFreshOrdinaryProbeHeap.Heap after.checked.native.machine.heap ∧
      SourceCurrentEmptinessMemo.Correct formulas solver after.checked.native.machine.heap after.fourth ∧
      EndpointMemoGateTrace.Valid after.checked.native.machine.heap final ∧
      Extends before.merge after.merge ∧ SourceCurrentEmptinessMemo.Extends before.fourth after.fourth ∧
      ∀ ambient term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term := by
  obtain ⟨next, final, actual, reads, checks, post, _, law⟩ :=
    SourceCurrentAllocatedPartialWorkerActual.root_exact formulas solver initial inherited available ranges done
  exact ⟨next, final, actual, reads, checks, post, post.context.admitted, post.context.probes,
    post.context.correct, post.context.globals, post.retained, post.fourthRetained, law⟩

-- A second literal root uses the FIRST computed Inventory and full warm Context; only its reached ranges and success are new.
example {f g s r e p h m c n F G S R E P H M C N budget identity : Nat}
    {value middleValue result : Node} {before middle after : Caller width} {inventory : Inventory} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints (.live identity []))
    (available : Available before.checked.native.machine.heap value)
    (firstRanges : SourceCurrentAllocatedPartialWorkerRanges.nodeCall f g s r e p h m c n budget ⟨.live identity [], value⟩ before)
    (first : SourceCurrentAllocatedPartialWorker.nodeCall f g s r e p h m c n budget ⟨.live identity [], value⟩ before = .done middleValue middle)
    (secondRanges : SourceCurrentAllocatedPartialWorkerRanges.nodeCall F G S R E P H M C N budget ⟨.live identity [], middleValue⟩ middle)
    (second : SourceCurrentAllocatedPartialWorker.nodeCall F G S R E P H M C N budget ⟨.live identity [], middleValue⟩ middle = .done result after) :
    ∃ firstInventory firstMemos next final,
      Post formulas solver firstInventory before middle firstMemos ∧
      Post formulas solver next middle after final ∧ Post formulas solver next before after final ∧
      ∀ ambient term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term := by
  obtain ⟨firstInventory, firstMemos, _actual, _reads, _checks, firstPost, firstAvailable, firstLaw⟩ :=
    SourceCurrentAllocatedPartialWorkerActual.root_exact formulas solver initial inherited available firstRanges first
  have nextInherited := inherited.grows firstPost.effects.grows.constraint_growth
  obtain ⟨next, final, _actual, _reads, _checks, lastPost, _, lastLaw⟩ :=
    SourceCurrentAllocatedPartialWorkerActual.root_exact formulas solver firstPost.context nextInherited firstAvailable secondRanges second
  exact ⟨firstInventory, firstMemos, next, final, firstPost, lastPost, firstPost.trans lastPost,
    fun ambient term => (lastLaw ambient term).trans (firstLaw ambient term)⟩

-- A zero-bound actual warm node cell yields its semantic receipt at the unchanged WHOLE Caller.
example {request original : NodeRequest} {before : Caller width} {inventory : Inventory} {memos : Memos}
    {handle : Nat} {result : Node}
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (published : before.nodeResults.table request.key = some handle)
    (returned : before.nodeResults.cells handle = some ⟨original, .returned result⟩) :
    SourceCurrentAllocatedPartialWorkerRanges.nodeCall 0 0 0 0 0 0 0 0 0 0 0 request before ∧
      ∃ next final, ∃ actual : NodeCall 0 request before result before,
        NodeCallReads formulas solver actual memos final ∧ Checks (nodeCallTrace actual) ∧
        Post formulas solver next before before final ∧ Available before.checked.native.machine.heap result ∧
        SourceCurrentAllocatedPartialMemoSound.NodeLaw formulas solver request result := by
  have started := beginNode_ready request original before handle result published returned
  have ranges : SourceCurrentAllocatedPartialWorkerRanges.nodeCall 0 0 0 0 0 0 0 0 0 0 0 request before := by
    simp only [SourceCurrentAllocatedPartialWorkerRanges.nodeCall, started]
  have done := SourceCurrentAllocatedPartialWorker.nodeCall_ready 0 0 0 0 0 0 0 0 0 0 0 request before before handle result started
  exact ⟨ranges, SourceCurrentAllocatedPartialWorkerActual.nodeCall_verified formulas solver initial inherited available ranges done⟩

-- Current-state indexed descent is verified from literal head success, with no supplied context at the descent or return.
example {g s r e p h m c n budget : Nat} {combined : EqValue} {index : Nat} {value result : Node}
    {before after : Caller width} {inventory : Inventory} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints combined)
    (available : Available before.checked.native.machine.heap value)
    (headRanges : SourceCurrentAllocatedPartialWorkerRanges.nodeCall 0 g s r e p h m c n budget
      ⟨(descend before combined index).1, value⟩ (descend before combined index).2)
    (head : SourceCurrentAllocatedPartialWorker.nodeCall 0 g s r e p h m c n budget
      ⟨(descend before combined index).1, value⟩ (descend before combined index).2 = .done result after) :
    ∃ next final, ∃ actual : Walk budget combined index [value] before [result] after,
      WalkReads formulas solver actual memos final ∧ Checks (walkTrace actual) ∧
      Post formulas solver next before after final ∧ Available after.checked.native.machine.heap result := by
  have done : SourceCurrentAllocatedPartialWorker.walk 1 g s r e p h m c n budget combined index [value] before = .done [result] after := by
    simp only [SourceCurrentAllocatedPartialWorker.walk, head, SourceCurrentAllocatedPartialWorker.Outcome.bind]
  have ranges : SourceCurrentAllocatedPartialWorkerRanges.walk 1 g s r e p h m c n budget combined index [value] before := by
    simp only [SourceCurrentAllocatedPartialWorkerRanges.walk, head, SourceCurrentAllocatedPartialWorkerRanges.After]
    exact ⟨headRanges, trivial⟩
  have values : Values before.checked.native.machine.heap [value] := by
    intro child member
    exact List.mem_singleton.mp member ▸ available
  obtain ⟨next, final, actual, reads, checks, post, outputs, _law⟩ :=
    SourceCurrentAllocatedPartialWorkerActual.walk_verified formulas solver initial inherited values ranges done
  exact ⟨next, final, actual, reads, checks, post, outputs result List.mem_cons_self⟩

-- A literal row verifies edge-return -> descendants-of-RETURNED-edge -> suffix at the SAME actual states.
example {g s r e p h m c n budget : Nat} {inherited : EqValue} {original narrowed result : Edge}
    {before middle after : Caller width} {inventory : Inventory} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (resident : InternedEdgeResidency.EdgeResident before.checked.native.machine.heap original)
    (edgeRanges : SourceCurrentAllocatedPartialWorkerRanges.edgeCall 0 g s r e p h m c n budget ⟨inherited, original⟩ before)
    (edgeDone : SourceCurrentAllocatedPartialWorker.edgeCall 0 g s r e p h m c n budget ⟨inherited, original⟩ before = .done narrowed middle)
    (childRanges : SourceCurrentAllocatedPartialWorkerRanges.descendants 0 g s r e p h m c n budget inherited narrowed middle)
    (childDone : SourceCurrentAllocatedPartialWorker.descendants 0 g s r e p h m c n budget inherited narrowed middle = .done result after) :
    ∃ next final, ∃ actual : Rows budget inherited [original] before [result] after,
      RowsReads formulas solver actual memos final ∧ Checks (rowsTrace actual) ∧
      Post formulas solver next before after final ∧ InternedEdgeResidency.EdgeResident after.checked.native.machine.heap result := by
  have done : SourceCurrentAllocatedPartialWorker.rows 1 g s r e p h m c n budget inherited [original] before = .done [result] after := by
    simp only [SourceCurrentAllocatedPartialWorker.rows, edgeDone, childDone, SourceCurrentAllocatedPartialWorker.Outcome.bind]
  have ranges : SourceCurrentAllocatedPartialWorkerRanges.rows 1 g s r e p h m c n budget inherited [original] before := by
    simp only [SourceCurrentAllocatedPartialWorkerRanges.rows, edgeDone, childDone, SourceCurrentAllocatedPartialWorkerRanges.After]
    exact ⟨edgeRanges, childRanges, trivial⟩
  have inputs : Edges before.checked.native.machine.heap [original] := by
    intro edge member
    exact List.mem_singleton.mp member ▸ resident
  obtain ⟨next, final, actual, reads, checks, post, outputs, _law⟩ :=
    SourceCurrentAllocatedPartialWorkerActual.rows_verified formulas solver initial inheritedReady inputs ranges done
  exact ⟨next, final, actual, reads, checks, post, outputs result List.mem_cons_self⟩

-- Range checks do not assert completion: a busy cell has a valid empty range predicate but no successful return.
example (request original : NodeRequest) (before : Caller width) (handle : Nat)
    (published : before.nodeResults.table request.key = some handle)
    (running : before.nodeResults.cells handle = some ⟨original, .evaluating⟩) :
    SourceCurrentAllocatedPartialWorkerRanges.nodeCall 0 0 0 0 0 0 0 0 0 0 0 request before ∧
      SourceCurrentAllocatedPartialWorker.nodeCall 0 0 0 0 0 0 0 0 0 0 0 request before = .failed (.nodeMemo handle .busy) before ∧
      ¬ ∃ result after, SourceCurrentAllocatedPartialWorker.nodeCall 0 0 0 0 0 0 0 0 0 0 0 request before = .done result after := by
  have started := beginNode_busy request original before handle published running
  have failed := SourceCurrentAllocatedPartialWorker.nodeCall_busy 0 0 0 0 0 0 0 0 0 0 0 request before before handle started
  refine ⟨?_, failed, ?_⟩
  · simp only [SourceCurrentAllocatedPartialWorkerRanges.nodeCall, started]
  · intro ⟨result, after, done⟩
    rw [failed] at done
    cases done

-- A later checked native query derives its full warm admission from the actual root Post.
example {f g s r e p h m c n budget identity : Nat} {value result left right : Node}
    {before after : Caller width} {inventory : Inventory} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints (.live identity []))
    (available : Available before.checked.native.machine.heap value)
    (leftAvailable : Available before.checked.native.machine.heap left)
    (rightAvailable : Available before.checked.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (ranges : SourceCurrentAllocatedPartialWorkerRanges.nodeCall f g s r e p h m c n budget ⟨.live identity [], value⟩ before)
    (done : SourceCurrentAllocatedPartialWorker.nodeCall f g s r e p h m c n budget ⟨.live identity [], value⟩ before = .done result after)
    (nativeRanges : SourceCurrentAllocatedNativeRequestBounds.WordRanges
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) after.checked) :
    ∃ firstInventory final next output reached,
      Post formulas solver firstInventory before after final ∧
      next.source = after.checked.native.machine.heap ∧ next.roots = firstInventory.roots ++ [left, right] ∧
      SourceCurrentAllocatedTargetQuery.Receipt formulas solver next left right after.checked output reached final := by
  obtain ⟨firstInventory, final, _actual, _reads, _checks, post, _output, _law⟩ :=
    SourceCurrentAllocatedPartialWorkerActual.root_exact formulas solver initial inherited available ranges done
  obtain ⟨next, output, reached, source, roots, receipt⟩ := SourceCurrentAllocatedTargetQuery.finite formulas solver
    firstInventory left right after.checked post.context.ready post.context.admitted
      (post.effects.keeps.available left leftAvailable) (post.effects.keeps.available right rightAvailable)
      leftClosed rightClosed nativeRanges final post.context.globals
  exact ⟨firstInventory, final, next, output, reached, post, source, roots, receipt⟩

end MicroCFTA.CurrentOuterActualExamples
