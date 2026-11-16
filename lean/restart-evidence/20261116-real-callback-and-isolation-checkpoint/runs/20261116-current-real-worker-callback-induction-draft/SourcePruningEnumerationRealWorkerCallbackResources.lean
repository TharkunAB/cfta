import MicroCFTA.SourcePruningEnumerationSharedEagerReservation
import MicroCFTA.SourcePruningEnumerationSharedPreparedCallbackResources
import MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy
import MicroCFTA.SourcePruningEnumerationSharedPreparedLiveRoot
import MicroCFTA.SourcePruningCallbackExact

set_option autoImplicit false
namespace MicroCFTA.SourcePruningEnumerationRealWorkerCallbackResources
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame EnumerationDriver
open InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure OutputResources OutcomeResources emitted)
open SourcePruningEnumerationSharedPreparedRecursiveChildPolicy (runEagerWithNarrow runWithNarrow resumeWithNarrow)
open SourcePruningEnumerationSharedEagerReservation (eagerFinal eagerReserved eagerFinal_ge)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {Typing Key : Type} {width bits : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]
/-- An actual callback return derives its current packet at the original work budget. -/
theorem recorded_callback_current_at_original_budget
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller width) (memos : Memos) (before : Cached) (seed : Seed)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (allocated : FragmentBound before.core.counter fragment)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (workFuel : Nat) (result : Bool × Metadata Typing) (observed : Core)
    (actual : Success (SourcePruningRecordTypes.recordTypes graph templates workFuel metadata uv (.inl fragment))
      before.core result observed) :
    Packet formulas solver inventory caller memos result.2 (EnumerationExpandableIndex.frame observed before) ∧
      RenderStable before.core observed ∧ Frame before.core observed ∧
      result.2.types = SourcePruningRecordTypes.updatedTypes metadata uv (.inl fragment) ∧
      result.2.openHoles = metadata.openHoles ∧ result.2.typing = metadata.typing ∧
      Fits seed.2 caller.checked ∧ Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap
 := by
  obtain ⟨bound, returned, after, current, stable, frame, types, holes, typing, fitted, alphabet, checkpoint⟩ :=
    SourcePruningEnumerationSharedPreparedRecursive.callback_complete_resources formulas solver inventory graph templates
      metadata uv fragment caller memos before seed packet allocated bounded known
  have retained := SourcePruningRecordTypes.recordTypes_moreFuel graph templates workFuel bound metadata uv
    (.inl fragment) before.core result observed actual
  have exactActual := SourcePruningCallbackExact.recordTypes_exact graph templates (workFuel + bound)
    metadata uv (.inl fragment) before.core observed result retained
  have actualAtBound : ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates (bound + workFuel)
      metadata uv (.inl fragment) before.core) = [.ok (result, observed)] := by
    simpa only [Nat.add_comm bound workFuel] using exactActual
  have exactCheckpoint := (checkpoint workFuel).2.1
  have same := Except.ok.inj (List.cons.inj (actualAtBound.symm.trans exactCheckpoint)).1
  have sameResult : result = returned := congrArg Prod.fst same
  have sameState : observed = after := congrArg Prod.snd same
  cases sameResult
  cases sameState
  exact ⟨current, stable, frame, types, holes, typing, fitted, alphabet⟩

/-- The real Left callback uses the genuine smaller-depth worker at the same work budget. -/
theorem real_callback_resources_of_depth_induction
    [DecidableEq Symbol] [DecidableEq Node]
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (recursiveDepth : Nat)
    (workerIH : ∀ (nextInventory : Inventory) (nextCaller : Caller (bits + 2)) (nextMemos : Memos)
        (nextBefore : Cached) (nextMetadata : Metadata Typing) (nextSeed : Seed) (nextCeiling : Nat),
      Packet formulas solver nextInventory nextCaller nextMemos nextMetadata nextBefore →
      Fits nextSeed.2 nextCaller.checked →
      Heap (fun guard => guard ∈ nextSeed.1) nextCaller.checked.native.machine.heap →
      (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
      (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
      SourcePruningEnumerationPrefixAdmission.suspendedBound nextBefore.core ≤ nextCeiling →
      eagerReserved bits recursiveDepth nextSeed nextCeiling →
      ∀ sameWorkFuel,
        let outcome := runEagerWithNarrow (SourcePruningOuterNarrow.narrow holeKey fits admits)
          graph templates checkEmpty edgesOf stop order sameWorkFuel recursiveDepth
          nextMetadata nextCaller nextMemos.query nextBefore
        (∀ output ∈ emitted outcome,
          OutputResources formulas solver nextCaller (eagerFinal recursiveDepth nextSeed nextCeiling) output) ∧
        match outcome with
        | .complete _ _ _ => OutcomeResources formulas solver nextCaller
            (eagerFinal recursiveDepth nextSeed nextCeiling) outcome
        | .stopped _ _ _ => True)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos)
    (before : Cached) (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (allocated : FragmentBound before.core.counter fragment)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : eagerReserved bits recursiveDepth seed ceiling) (workFuel : Nat) :
    let outcome := SourcePruningEnumerationSharedPreparedRecursive.continueWith
      (resumeWithNarrow
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
          workFuel workFuel workFuel workFuel workFuel edgesOf)
        (SourcePruningOuterNarrow.narrow holeKey fits admits)
        graph templates checkEmpty edgesOf stop order workFuel recursiveDepth)
      graph templates stop order workFuel metadata uv fragment caller memos.query before
    (∀ output ∈ emitted outcome,
      OutputResources formulas solver caller (eagerFinal recursiveDepth seed ceiling) output) ∧
      match outcome with
      | .complete _ _ _ => OutcomeResources formulas solver caller (eagerFinal recursiveDepth seed ceiling) outcome
      | .stopped _ _ _ => True
 := by
  classical
  let recur := resumeWithNarrow (Typing := Typing) (width := bits + 2)
    (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
      workFuel workFuel workFuel workFuel workFuel edgesOf)
    (SourcePruningOuterNarrow.narrow holeKey fits admits)
    graph templates checkEmpty edgesOf stop order workFuel recursiveDepth
  change let outcome := SourcePruningEnumerationSharedPreparedRecursive.continueWith
      recur graph templates stop order workFuel metadata uv fragment caller memos.query before
    (∀ output ∈ emitted outcome,
      OutputResources formulas solver caller (eagerFinal recursiveDepth seed ceiling) output) ∧
      match outcome with
      | .complete _ _ _ => OutcomeResources formulas solver caller (eagerFinal recursiveDepth seed ceiling) outcome
      | .stopped _ _ _ => True
  let raw := ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates workFuel metadata uv
    (.inl fragment) before.core)
  by_cases successful : ∃ (flag : Bool) (updated : Metadata Typing) (observed : Core),
      raw = [.ok ((flag, updated), observed)]
  · obtain ⟨flag, updated, observed, recorded⟩ := successful
    have actual : Success (SourcePruningRecordTypes.recordTypes graph templates workFuel metadata uv (.inl fragment))
        before.core (flag, updated) observed := by
      rw [Success, recorded]
      exact List.mem_singleton_self _
    obtain ⟨current, _stable, frame, _types, _holes, _typing, fitted, alphabet⟩ :=
      recorded_callback_current_at_original_budget formulas solver inventory graph templates metadata uv fragment
        caller memos before seed packet allocated bounded known workFuel (flag, updated) observed actual
    cases flag with
    | true =>
        have completed : OutcomeResources (Typing := Typing) formulas solver caller seed
            (.complete [] caller memos.query) := by
          refine ⟨caller, inventory, memos, Post.refl packet.context, bounded, known, rfl, rfl, ?_⟩
          intro output member
          exact (List.not_mem_nil member).elim
        have growth := eagerFinal_ge recursiveDepth seed ceiling
        have padded := completed.mono growth.1 growth.2
        rw [SourcePruningEnumerationSharedPreparedRecursive.continue_rejected recur graph templates stop order
          workFuel metadata updated uv fragment caller memos.query before observed recorded]
        constructor
        · intro output member
          exact (List.not_mem_nil member).elim
        · exact padded
    | false =>
        have massAfter : SourcePruningEnumerationPrefixAdmission.suspendedBound
            (EnumerationExpandableIndex.frame observed before).core ≤ ceiling := by
          change SourcePruningEnumerationPrefixAdmission.suspendedBound observed ≤ ceiling
          rw [SourcePruningEnumerationPrefixAdmission.suspendedBound_values before.core observed frame.values]
          exact mass
        have inherited := workerIH inventory caller memos (EnumerationExpandableIndex.frame observed before)
          updated seed ceiling current fitted alphabet selectionMembers selectionLength massAfter reserved workFuel
        rw [SourcePruningEnumerationSharedPreparedRecursive.continue_recorded recur graph templates stop order
          workFuel metadata updated uv fragment caller memos.query before observed recorded]
        simpa only [runEagerWithNarrow, runWithNarrow, recur] using inherited
  · have stopped : SourcePruningEnumerationSharedPreparedRecursive.continueWith recur graph templates stop order
        workFuel metadata uv fragment caller memos.query before =
        .stopped [] (.callback uv raw) (some (caller, memos.query)) := by
      unfold SourcePruningEnumerationSharedPreparedRecursive.continueWith
      dsimp only
      split
      · exact (successful ⟨true, _, _, by assumption⟩).elim
      · exact (successful ⟨false, _, _, by assumption⟩).elim
      · rfl
    rw [stopped]
    constructor
    · intro output member
      exact (List.not_mem_nil member).elim
    · trivial

end MicroCFTA.SourcePruningEnumerationRealWorkerCallbackResources
