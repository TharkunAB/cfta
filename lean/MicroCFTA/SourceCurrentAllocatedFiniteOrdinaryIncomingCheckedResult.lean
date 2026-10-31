import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryIncomingResult

/-! The actual incoming result includes the enabled empty check. -/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryIncomingCheckedResult
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationObservation (PendingRealized)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentAllocatedFiniteOrdinaryStored (Stored)
attribute [local instance] FormulaExecutable.formulaDecidableEq
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "NodeDomain" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
variable {EnumGuard : Type}
local instance resultMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

open scoped Classical in
private theorem finish_slot (before : EnumerationState.State Symbol EnumGuard)
    (target handle : Nat) (incomingScs oldScs : List EnumerationState.Suspended) (replacement : Node)
    (inside : target < before.values.length) (after : EnumerationState.State Symbol EnumGuard)
    (returned : Except.ok ((), after) ∈ ExceptT.run
      (SourcePruningEnumerationIncomingNode.finish target handle incomingScs oldScs replacement before)) :
    after.values[target]? = some (.unenumerated (some handle) (incomingScs ++ oldScs)) := by
  classical
  let written : EnumerationState.State Symbol EnumGuard := {before with
    values := before.values.set target (.unenumerated (some handle) (incomingScs ++ oldScs))
    recursionAncestry := fun other => if other = target then
      (before.expansionAncestry ++ before.recursionAncestry target).eraseDups else before.recursionAncestry other}
  have raw : ExceptT.run
      (SourcePruningEnumerationIncomingNode.finish target handle incomingScs oldScs replacement before) =
      (if replacement = .empty then [] else [.ok ((), written)]) := by
    cases replacement with
    | empty => simp only [↓reduceIte]; rfl
    | reference _name => simp only [reduceCtorEq, ↓reduceIte]; rfl
    | node _entry _edges _depth _free => simp only [reduceCtorEq, ↓reduceIte]; rfl
    | union _entry _members _depth _free => simp only [reduceCtorEq, ↓reduceIte]; rfl
    | mu _entry _body _depth _ordinary => simp only [reduceCtorEq, ↓reduceIte]; rfl
  rw [raw] at returned
  split at returned
  · simp only [List.not_mem_nil] at returned
  · have same : after = written := congrArg Prod.snd (Except.ok.inj (List.mem_singleton.mp returned))
    subst after
    exact List.getElem?_set_self inside

variable [DecidableEq (EdgeKey Symbol Constraint)]

open scoped Classical in
/-- The actual Some/Some native branch classifies its handle and every returned successful slot write. -/
theorem some_some_result (bits : Nat) (profile : Profile)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2)) (before : EnumerationState.State Symbol EnumGuard)
    (checkEmpty : Bool) (r n p h uv oldHandle : Nat) (found : UnionFind.Result) (incoming old : Node)
    (incomingScs oldScs : List EnumerationState.Suspended) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before)
    (available : Available beforeCaller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (incomingDomain : NodeDomain incoming) (oldDomain : NodeDomain old)
    (fits : SourceCurrentConstrainedCapGeneratedQueryResources.Fits profile beforeCaller.checked) (room : Room bits profile)
    (stored : Stored beforeCaller.checked.native)
    (reading : UnionFind.findRoot r before.representatives uv = some found)
    (slot : before.values[found.representative]? = some (.unenumerated (some oldHandle) oldScs))
    (decoded : SourcePruningEnumerationNodes.lookupNode beforeCaller.checked.native.machine.heap oldHandle = some old) :
    let result := SourcePruningEnumerationIncomingNode.run checkEmpty r n p h beforeCaller before uv incoming incomingScs memos.query
    Stored result.2.1.checked.native ∧
      match result.1 with
      | .ok (some rows) =>
          ∃ query handle, NodeDomain query ∧
            MergedOrdinaryHeight.height query ≤ MergedOrdinaryHeight.height incoming ∧
            MergedOrdinaryHeight.height query ≤ MergedOrdinaryHeight.height old ∧
            SourcePruningEnumerationNodes.encodeNode query = some handle ∧
            SourcePruningEnumerationNodes.lookupNode result.2.1.checked.native.machine.heap handle = some query ∧
            ∀ after : EnumerationState.State Symbol EnumGuard, Except.ok ((), after) ∈ rows →
              after.values[found.representative]? = some (.unenumerated (some handle) (incomingScs ++ oldScs))
      | _ => True := by
  classical
  constructor
  · exact SourceCurrentAllocatedNativeStoredIncoming.incoming_run_stored profile checkEmpty r n p h
      beforeCaller before uv incoming incomingScs memos.query initial.ready realized available closed fits room stored
  · obtain ⟨actualOld, oldLookup, oldAvailable, oldClosed⟩ := realized found.representative oldHandle oldScs slot
    have same : actualOld = old := Option.some.inj (oldLookup.symm.trans decoded)
    subst actualOld
    have actualRoom := fits.room room
    have inside : found.representative < before.values.length :=
      (List.getElem?_eq_some_iff.mp slot).elim (fun bound _value => bound)
    simp only [SourcePruningEnumerationIncomingNode.run, reading, slot, decoded]
    cases actual : SourceEqualityNativeDemand.execute n
        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain incoming old))
        beforeCaller.checked <;> try trivial
    case done query queried =>
      dsimp only []
      obtain ⟨next, _source, _roots, receipt, queryPost⟩ := SourceCurrentAllocatedTargetQuery.raw_done_caller_initial
        bits n formulas solver inventory beforeCaller queried incoming old query memos initial
        available oldAvailable closed oldClosed actualRoom.1 actualRoom.2.1 actualRoom.2.2 actual
      obtain ⟨_queriedStored, domain, leftHeight, rightHeight, handle, encoded, looked⟩ :=
        SourceCurrentAllocatedFiniteOrdinaryTargetResult.receipt_result initial.ready stored incomingDomain oldDomain receipt
      generalize phaseEq : (if checkEmpty then
        SourcePruningEnumerationEnabledEmpty.check p h query queried beforeCaller.fourth memos.query
        else (SourceCurrentAllocatedConjunctionWorker.Outcome.done false queried beforeCaller.fourth, memos.query)) = phase
      obtain ⟨outcome, _phaseQueries⟩ := phase
      cases outcome with
      | failed _fault _checkedAfter _saved => trivial
      | done answer checkedAfter saved =>
        have observedPhase := congrArg Prod.fst phaseEq
        have lookedAfter : SourcePruningEnumerationNodes.lookupNode checkedAfter.native.machine.heap handle = some query := by
          cases checkEmpty with
          | false =>
            change SourceCurrentAllocatedConjunctionWorker.Outcome.done false queried beforeCaller.fourth =
              .done answer checkedAfter saved at observedPhase
            cases observedPhase
            exact looked
          | true =>
            change (SourcePruningEnumerationEnabledEmpty.check p h query queried beforeCaller.fourth memos.query).1 =
              .done answer checkedAfter saved at observedPhase
            dsimp only [SourcePruningEnumerationEnabledEmpty.check] at observedPhase
            split at observedPhase
            · obtain ⟨reached, physicalDone, same⟩ := SourceCurrentAllocatedConjunctionWorker.call_done observedPhase
              subst checkedAfter
              have call := SourceCurrentConjunctionWorkerCompletion.call_sound p h 1000 beforeCaller.fourth query
                (SourceCurrentAllocatedNativeEffects.physical queried) answer reached saved physicalDone
              obtain ⟨_final, _reads, post, _sound, _available, _unfolding, _queries⟩ :=
                SourceCurrentAllocatedConjunctionCaller.actual formulas solver
                  (before := SourceCurrentAllocatedPartialState.advance beforeCaller queried beforeCaller.fourth beforeCaller.merge)
                  call queryPost.context receipt.available
              exact SourcePruningEnumerationNodes.lookupNode_keeps _ _ post.effects.keeps handle query looked
            · cases observedPhase
              exact looked
        cases answer with
        | false =>
          simp only [reduceCtorEq, ↓reduceIte, encoded]
          refine ⟨query, handle, domain, leftHeight, rightHeight, encoded, lookedAfter, ?_⟩
          intro after returned
          exact finish_slot {before with representatives := found.forest} found.representative handle
            incomingScs oldScs query inside after returned
        | true =>
          simp only [↓reduceIte, SourcePruningEnumerationNodes.encodeNode]
          refine ⟨.empty, 0, .empty, Nat.zero_le _, Nat.zero_le _, rfl, rfl, ?_⟩
          intro after returned
          exact finish_slot {before with representatives := found.forest} found.representative 0
            incomingScs oldScs .empty inside after returned

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryIncomingCheckedResult
