import MicroCFTA.SourceEqualityNativeDemandNodeShortcut
import MicroCFTA.SourceEqualityNativeDemandChildWalk

/-!
# Actual pure and completed checked node calls

Fresh pure bodies publish, demand, and complete their actual original node
cells. Empty and self branches derive their own body receipts. Completed
hits recover the stored checked receipt without effect replay. Exact traces
and unchanged physical machines supply concrete child-fold cases.
-/
namespace MicroCFTA.SourceEqualityNativeDemandNodeCalls
open Language Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode SourceRecursiveIntersectionControl
open SourceEqualityNativeDemand SourceEqualityNativeDemandProvenance
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Fresh publication and a proved pure body derive actual checked completion without a future validity premise. -/
theorem pure_miss_native_valid [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (request : NodeRequest Symbol Guard) (state : SourceEqualityNativeDemand.State width)
    (valid : SourceEqualityNativeDemandProvenance.Valid holds state.native) (ready : NodeReady state.native.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (key : IntersectionFlatMemoKeyDomain.Triple width)
    (requested : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key)
    (missing : state.native.nodes.table key = none) (value : Value Symbol Guard)
    (pureBody : compileNode request = .pure value)
    (produced : NodeProduced (width := width) holds state.native.machine request value) :
    ∃ after, execute 3 (.code (requestNode request.domain request.left request.right)) state = .done value after ∧
      Steps 2 (.code (requestNode request.domain request.left request.right)) state (.code (.pure value)) after ∧
      SourceEqualityNativeDemandProvenance.Valid holds after.native ∧ after.native.machine = state.native.machine ∧
      after.operations = state.operations ∧ NodeProduced (width := width) holds after.native.machine request value := by
  let handle := state.native.nodes.next
  let chosen := (lookupNode width request state.native).2
  let current := (demandNode handle chosen).2
  have selected : lookupNode width request state.native = (.memoized handle, chosen) := by
    simp [chosen, handle, lookupNode, requested, FlatMemoThunk.lookupOrInsert, missing]
  have demanded : demandNode handle chosen = (.evaluate request, current) := by
    apply Prod.ext
    · simp [chosen, handle, lookupNode, requested, FlatMemoThunk.lookupOrInsert, missing, demandNode, FlatMemoThunk.demand, Cache.put]
    · rfl
  have machine : current.machine = state.native.machine :=
    (SourceRecursiveIntersectionNative.demandNode_machine handle chosen).trans (SourceRecursiveIntersectionNative.lookupNode_machine request state.native)
  have chosenValid := SourceEqualityNativeDemandProvenance.lookupNode_valid state.native valid request ready safe
  have currentValid := SourceEqualityNativeDemandProvenance.demandNode_valid chosen chosenValid handle
  have running := (SourceRecursiveIntersectionNative.demandNode_evaluate handle chosen current request demanded).2
  have currentProduced : NodeProduced (width := width) holds current.machine request value := by rw [machine]; exact produced
  have finished := SourceEqualityNativeDemandProvenance.finishNode_valid current currentValid handle request value running currentProduced
  let after : SourceEqualityNativeDemand.State width := ⟨SourceRecursiveIntersectionThunks.finishNode handle value current, state.operations⟩
  have trace : Steps 2 (.code (requestNode request.domain request.left request.right)) state (.code (.pure value)) after := by
    apply execute_steps 2 _ _ state after
    simp only [SourceEqualityNativeDemand.execute, SourceEqualityNativeDemand.step, requestNode,
      SourceRecursiveIntersectionNative.step, selected, demanded, pureBody, Code.bind, SourceEqualityNativeDemand.lift]
    rfl
  exact ⟨after, trace_done 2 _ state after value trace, trace, finished, machine, rfl, currentProduced⟩

/-- Source self tests derive the actual fresh child call and its complete original result receipt. -/
theorem self_miss [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (request : NodeRequest Symbol Guard) (state : SourceEqualityNativeDemand.State width)
    (valid : SourceEqualityNativeDemandProvenance.Valid holds state.native) (ready : NodeReady state.native.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (key : IntersectionFlatMemoKeyDomain.Triple width)
    (requested : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key)
    (missing : state.native.nodes.table key = none)
    (nonempty : hasEmpty request.left request.right = false)
    (noReset : reset request.domain.key request.left request.right = false) (same : closedSelf request.left request.right = true) :
    ∃ after, execute 3 (.code (requestNode request.domain request.left request.right)) state = .done request.left after ∧
      Steps 2 (.code (requestNode request.domain request.left request.right)) state (.code (.pure request.left)) after ∧
      SourceEqualityNativeDemandProvenance.Valid holds after.native ∧ after.native.machine = state.native.machine ∧
      after.operations = state.operations ∧ NodeProduced (width := width) holds after.native.machine request request.left := by
  have pureBody : compileNode request = .pure request.left := by
    simp only [compileNode, self_first request.domain.key request.left request.right nonempty noReset same]
  exact pure_miss_native_valid holds request state valid ready safe key requested missing request.left pureBody
    (self_body_produced holds request state valid.machine ready nonempty noReset same)

/-- A literal empty operand derives the actual fresh empty child call without a supplied result law. -/
theorem empty_miss [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (request : NodeRequest Symbol Guard) (state : SourceEqualityNativeDemand.State width)
    (valid : SourceEqualityNativeDemandProvenance.Valid holds state.native) (ready : NodeReady state.native.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (key : IntersectionFlatMemoKeyDomain.Triple width)
    (requested : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key)
    (missing : state.native.nodes.table key = none) (empty : request.left = .empty ∨ request.right = .empty) :
    ∃ after, execute 3 (.code (requestNode request.domain request.left request.right)) state = .done .empty after ∧
      Steps 2 (.code (requestNode request.domain request.left request.right)) state (.code (.pure (.empty : Value Symbol Guard))) after ∧
      SourceEqualityNativeDemandProvenance.Valid holds after.native ∧ after.native.machine = state.native.machine ∧
      after.operations = state.operations ∧ NodeProduced (width := width) holds after.native.machine request .empty := by
  have guard : hasEmpty request.left request.right = true := by
    rcases empty with left | right
    · simp only [hasEmpty, left, Value.referenceOf, beq_self_eq_true, Bool.true_or]
    · simp only [hasEmpty, right, Value.referenceOf, beq_self_eq_true, Bool.or_true]
  have pureBody : compileNode request = .pure .empty := by
    simp only [compileNode, empty_first request.domain.key request.left request.right guard]
  exact pure_miss_native_valid holds request state valid ready safe key requested missing .empty pureBody
    (empty_body_produced holds request state ready empty)

/-- A current valid completed node cell gives an actual one-instruction child trace and its original receipt. -/
theorem ready_call [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (request original : NodeRequest Symbol Guard) (state : SourceEqualityNativeDemand.State width)
    (valid : SourceEqualityNativeDemandProvenance.Valid holds state.native) (ready : NodeReady state.native.machine request)
    (key : IntersectionFlatMemoKeyDomain.Triple width) (checked : NodeKey width request key)
    (handle : Nat) (published : state.native.nodes.table key = some handle) (value : Value Symbol Guard)
    (returned : state.native.nodes.cells handle = some ⟨original, .returned value⟩) :
    Steps 1 (.code (requestNode request.domain request.left request.right)) state (.code (.pure value)) state ∧
      execute 2 (.code (requestNode request.domain request.left request.right)) state = .done value state ∧
      NodeProduced (width := width) holds state.native.machine request value := by
  obtain ⟨selected, demanded, produced, _, _⟩ := SourceEqualityNativeDemandProvenance.node_ready_receipt
    state.native valid request original ready key checked handle published value returned
  have trace : Steps 1 (.code (requestNode request.domain request.left request.right)) state (.code (.pure value)) state := by
    apply Steps.cons _ _ (.code (.pure value)) state _ _ 0
    · simp only [SourceEqualityNativeDemand.step, requestNode, SourceRecursiveIntersectionNative.step, selected, demanded, SourceEqualityNativeDemand.lift]
    · exact .refl _ _
  exact ⟨trace, trace_done 1 _ state state value trace, produced⟩

/-- An actual call with no physical effect supplies a complete one-child fold receipt. -/
theorem singleton_walk [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (request : NodeRequest Symbol Guard)
    (state after : SourceEqualityNativeDemand.State width) (fuel : Nat) (value : Value Symbol Guard)
    (ready : SourceEqualityRequiredCache.Ready state.native.machine.heap)
    (trace : Steps fuel (.code (requestNode request.domain request.left request.right)) state (.code (.pure value)) after)
    (machine : after.native.machine = state.native.machine)
    (produced : NodeProduced (width := width) holds after.native.machine request value) :
    SourceEqualityNativeDemandChildWalk.Walk holds request.domain [(request.left, request.right)] state [value] after fuel := by
  have keeps : SourceEqualityRequiredCache.Keeps state.native.machine.heap after.native.machine.heap := by
    rw [machine]
    exact SourceEqualityRequiredCache.pure_keeps _ ready
  have growth : Extension state.native.machine after.native.machine := by rw [machine]; exact .refl _
  simpa only [Nat.add_zero] using SourceEqualityNativeDemandChildWalk.Walk.cons (request.left, request.right) [] state after after
    value [] fuel 0 trace keeps growth produced (SourceEqualityNativeDemandChildWalk.Walk.nil after)

/-- A current completed hit supplies a concrete checked child fold without an answer or replay premise. -/
theorem ready_walk [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (request original : NodeRequest Symbol Guard) (state : SourceEqualityNativeDemand.State width)
    (valid : SourceEqualityNativeDemandProvenance.Valid holds state.native) (ready : NodeReady state.native.machine request)
    (heapReady : SourceEqualityRequiredCache.Ready state.native.machine.heap)
    (key : IntersectionFlatMemoKeyDomain.Triple width) (checked : NodeKey width request key)
    (handle : Nat) (published : state.native.nodes.table key = some handle) (value : Value Symbol Guard)
    (returned : state.native.nodes.cells handle = some ⟨original, .returned value⟩) :
    SourceEqualityNativeDemandChildWalk.Walk holds request.domain [(request.left, request.right)] state [value] state 1 := by
  obtain ⟨trace, _, produced⟩ := ready_call holds request original state valid ready key checked handle published value returned
  exact singleton_walk holds request state state 1 value heapReady trace rfl produced

/-- A fresh physical self branch derives an actual checked child fold and preserves both current states. -/
theorem self_miss_walk [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (request : NodeRequest Symbol Guard) (state : SourceEqualityNativeDemand.State width)
    (valid : SourceEqualityNativeDemandProvenance.Valid holds state.native) (ready : NodeReady state.native.machine request)
    (heapReady : SourceEqualityRequiredCache.Ready state.native.machine.heap)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (key : IntersectionFlatMemoKeyDomain.Triple width)
    (requested : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key)
    (missing : state.native.nodes.table key = none)
    (nonempty : hasEmpty request.left request.right = false)
    (noReset : reset request.domain.key request.left request.right = false) (same : closedSelf request.left request.right = true) :
    ∃ after, SourceEqualityNativeDemandChildWalk.Walk holds request.domain [(request.left, request.right)] state [request.left] after 2 ∧
      SourceEqualityNativeDemandProvenance.Valid holds after.native ∧ after.native.machine = state.native.machine ∧ after.operations = state.operations := by
  obtain ⟨after, _, trace, afterValid, machine, operations, produced⟩ :=
    self_miss holds request state valid ready safe key requested missing nonempty noReset same
  exact ⟨after, singleton_walk holds request state after 2 request.left heapReady trace machine produced, afterValid, machine, operations⟩

end MicroCFTA.SourceEqualityNativeDemandNodeCalls
