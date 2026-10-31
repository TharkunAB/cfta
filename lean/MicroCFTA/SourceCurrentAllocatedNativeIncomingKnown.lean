import MicroCFTA.SourceSizedPrefixKnownOrdinaryHeap
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTargetResult
import MicroCFTA.SourceCurrentAllocatedTargetCallerObserved
import MicroCFTA.SourceCurrentAllocatedNativeStoredIncoming

/-! Actual successful incoming rows retain the whole known ordinary cache. -/
namespace MicroCFTA.SourceCurrentAllocatedNativeIncomingKnown
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationObservation (PendingRealized)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentAllocatedFiniteOrdinaryStored (Stored)
open SourceSizedPrefixKnownOrdinary (KnownOrdinary)
attribute [local instance] FormulaExecutable.formulaDecidableEq
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "NodeDomain" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local instance incomingKnownMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

open scoped Classical in
private theorem finish_known (bound : Nat) (heap : State Symbol Constraint) (before : Cached)
    (target handle : Nat) (incomingScs oldScs : List EnumerationState.Suspended) (replacement : Node)
    (known : KnownOrdinary bound heap before)
    (newKnown : ∃ value, SourcePruningEnumerationNodes.lookupNode heap handle = some value ∧
      NodeDomain value ∧ MergedOrdinaryHeight.height value ≤ bound)
    (after : Core) (returned : Except.ok ((), after) ∈ ExceptT.run
      (SourcePruningEnumerationIncomingNode.finish target handle incomingScs oldScs replacement before.core)) :
    KnownOrdinary bound heap {before with core := after} := by
  classical
  let written : Core := {before.core with
    values := before.core.values.set target (.unenumerated (some handle) (incomingScs ++ oldScs))
    recursionAncestry := fun other => if other = target then
      (before.core.expansionAncestry ++ before.core.recursionAncestry target).eraseDups else before.core.recursionAncestry other}
  have raw : ExceptT.run
      (SourcePruningEnumerationIncomingNode.finish target handle incomingScs oldScs replacement before.core) =
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
    intro current scs member
    change EnumerationState.UVarValue.unenumerated (some current) scs ∈
      before.core.values.set target (.unenumerated (some handle) (incomingScs ++ oldScs)) at member
    rcases List.mem_or_eq_of_mem_set member with old | same
    · exact known current scs old
    · have handleSame : current = handle := Option.some.inj (EnumerationState.UVarValue.unenumerated.inj same).1
      subst current
      exact newKnown

variable [DecidableEq (EdgeKey Symbol Constraint)]

open scoped Classical in
/-- Every actual returned successful Core retains all known ordinary handles within the same bound. -/
theorem run_known (bits bound : Nat) (profile : Profile)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2)) (before : Cached)
    (checkEmpty : Bool) (r n p h uv : Nat) (incoming : Node)
    (incomingScs : List EnumerationState.Suspended) (memos : Memos) (queries : SourceEndpointMemo.Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (available : Available beforeCaller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (incomingDomain : NodeDomain incoming) (incomingHeight : MergedOrdinaryHeight.height incoming ≤ bound)
    (known : KnownOrdinary bound beforeCaller.checked.native.machine.heap before)
    (fits : SourceCurrentConstrainedCapGeneratedQueryResources.Fits profile beforeCaller.checked) (room : Room bits profile)
    (stored : Stored beforeCaller.checked.native) :
    let result := SourcePruningEnumerationIncomingNode.run checkEmpty r n p h beforeCaller before.core uv incoming incomingScs queries
    Stored result.2.1.checked.native ∧
      match result.1 with
      | .ok (some rows) => ∀ after : Core, Except.ok ((), after) ∈ rows →
          KnownOrdinary bound result.2.1.checked.native.machine.heap {before with core := after}
      | _ => True := by
  classical
  constructor
  · exact SourceCurrentAllocatedNativeStoredIncoming.incoming_run_stored profile checkEmpty r n p h
      beforeCaller before.core uv incoming incomingScs queries initial.ready realized available closed fits room stored
  · cases reading : UnionFind.findRoot r before.core.representatives uv with
    | none => simp [SourcePruningEnumerationIncomingNode.run, reading]
    | some found =>
      simp only [SourcePruningEnumerationIncomingNode.run, reading]
      cases slot : before.core.values[found.representative]? with
      | none => simp
      | some value =>
        cases value with
        | enumerated _fragment => simp
        | eliminated => simp
        | unenumerated oldNode oldScs =>
          dsimp only []
          let read : Cached := {before with core := {before.core with representatives := found.forest}}
          have readKnown : KnownOrdinary bound beforeCaller.checked.native.machine.heap read := by
            intro handle scs member
            exact known handle scs member
          cases oldNode with
          | none =>
            obtain ⟨handle, encoded, looked⟩ := SourcePruningEnumerationNodes.available_readback
              beforeCaller.checked.native.machine.heap incoming
              initial.ready.semantic.ready.semantic.1.normal.facts.coherent available closed
            simp only [encoded]
            intro after returned
            exact finish_known bound _ read found.representative handle incomingScs oldScs incoming readKnown
              ⟨incoming, looked, incomingDomain, incomingHeight⟩ after returned
          | some oldHandle =>
            obtain ⟨old, decoded, oldAvailable, oldClosed⟩ := realized found.representative oldHandle oldScs slot
            obtain ⟨knownOld, knownLookup, oldDomain, _oldHeight⟩ :=
              known oldHandle oldScs (List.mem_of_getElem? slot)
            have same : knownOld = old := Option.some.inj (knownLookup.symm.trans decoded)
            subst knownOld
            have actualRoom := fits.room room
            simp only [decoded]
            cases actual : SourceEqualityNativeDemand.execute n
                (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain incoming old))
                beforeCaller.checked <;> try trivial
            case done query queried =>
              dsimp only []
              obtain ⟨next, _source, _roots, receipt, queryPost⟩ := SourceCurrentAllocatedTargetQuery.raw_done_caller_initial
                bits n formulas solver inventory beforeCaller queried incoming old query memos initial
                available oldAvailable closed oldClosed actualRoom.1 actualRoom.2.1 actualRoom.2.2 actual
              obtain ⟨_stored, domain, leftHeight, _rightHeight, handle, encoded, looked⟩ :=
                SourceCurrentAllocatedFiniteOrdinaryTargetResult.receipt_result initial.ready stored incomingDomain oldDomain receipt
              have queryKnown := SourceSizedPrefixKnownOrdinaryHeap.query_known receipt readKnown
              generalize phaseEq : (if checkEmpty then
                SourcePruningEnumerationEnabledEmpty.check p h query queried beforeCaller.fourth queries
                else (SourceCurrentAllocatedConjunctionWorker.Outcome.done false queried beforeCaller.fourth, queries)) = phase
              obtain ⟨outcome, _phaseQueries⟩ := phase
              cases outcome with
              | failed _fault _checkedAfter _saved => trivial
              | done answer checkedAfter saved =>
                have observedPhase := congrArg Prod.fst phaseEq
                have reached : KnownOrdinary bound checkedAfter.native.machine.heap read ∧
                    SourcePruningEnumerationNodes.lookupNode checkedAfter.native.machine.heap handle = some query := by
                  cases checkEmpty with
                  | false =>
                    change SourceCurrentAllocatedConjunctionWorker.Outcome.done false queried beforeCaller.fourth =
                      .done answer checkedAfter saved at observedPhase
                    cases observedPhase
                    exact ⟨queryKnown, looked⟩
                  | true =>
                    change (SourcePruningEnumerationEnabledEmpty.check p h query queried beforeCaller.fourth queries).1 =
                      .done answer checkedAfter saved at observedPhase
                    dsimp only [SourcePruningEnumerationEnabledEmpty.check] at observedPhase
                    split at observedPhase
                    · obtain ⟨physicalAfter, physicalDone, same⟩ := SourceCurrentAllocatedConjunctionWorker.call_done observedPhase
                      subst checkedAfter
                      have call := SourceCurrentConjunctionWorkerCompletion.call_sound p h 1000 beforeCaller.fourth query
                        (SourceCurrentAllocatedNativeEffects.physical queried) answer physicalAfter saved physicalDone
                      obtain ⟨_final, _reads, post, _sound, _available, _unfolding, _queries⟩ :=
                        SourceCurrentAllocatedConjunctionCaller.actual formulas solver
                          (before := SourceCurrentAllocatedPartialState.advance beforeCaller queried beforeCaller.fourth beforeCaller.merge)
                          call queryPost.context receipt.available
                      exact ⟨SourceSizedPrefixKnownOrdinaryHeap.post_known post queryKnown,
                        SourcePruningEnumerationNodes.lookupNode_keeps _ _ post.effects.keeps handle query looked⟩
                    · cases observedPhase
                      exact ⟨queryKnown, looked⟩
                cases answer with
                | false =>
                  simp only [reduceCtorEq, ↓reduceIte, encoded]
                  intro after returned
                  exact finish_known bound _ read found.representative handle incomingScs oldScs query reached.1
                    ⟨query, reached.2, domain, Nat.le_trans leftHeight incomingHeight⟩ after returned
                | true =>
                  simp only [↓reduceIte, SourcePruningEnumerationNodes.encodeNode]
                  intro after returned
                  exact finish_known bound _ read found.representative 0 incomingScs oldScs .empty reached.1
                    ⟨.empty, rfl, .empty, Nat.zero_le _⟩ after returned

end MicroCFTA.SourceCurrentAllocatedNativeIncomingKnown
