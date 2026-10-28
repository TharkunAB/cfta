import MicroCFTA.SourcePruningEnumerationInitialProper
import MicroCFTA.SourcePruningEnumerationRecursive
import MicroCFTA.SourcePruningEnumerationRendering
import MicroCFTA.EnumerationRenderability

/-!
# Native done and the discharged rendering boundary

Done removes expandable work. It can retain a recursive boundary handle.
The literal native startup gives such a reached output without an expansion.
The native renderer maps that handle to its explicit recursion marker.
-/
namespace MicroCFTA.SourcePruningEnumerationRestart
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationProgress
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Metadata" => SourcePruningRecordTypes.Metadata
variable {Typing : Type} {width : Nat}

private theorem pick_done (preference : List Nat → Option Nat) (offered : Option (List Nat)) :
    pickNext preference offered = .done ↔ offered = none := by
  cases offered with
  | none => simp [pickNext]
  | some offered =>
      cases offered with
      | nil => simp [pickNext]
      | cons first rest =>
          cases chosen : preference (first :: rest) with
          | none => simp [pickNext, chosen]
          | some uv =>
              by_cases member : uv ∈ first :: rest <;> simp [pickNext, chosen, member]

/-- A restart without a stop rule reports done exactly when its candidate list is empty. -/
theorem done_iff_candidates_nil
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing) (before : Cached) :
    decision none order metadata before = some .done ↔
      EnumerationIndexSelection.candidates before = [] := by
  simp only [decision, Option.some.injEq, EnumerationPureSelection.next, pick_done]
  unfold EnumerationPureSelection.find
  by_cases empty : EnumerationIndexSelection.candidates before = [] <;> simp [empty]

/-- A done native cache can retain only recursive boundaries in its graph-bearing pending slots. -/
theorem done_pending_boundary
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (caller : Caller width) (before : Cached)
    (valid : SourcePruningEnumerationNativeBranchCompletion.CacheValid caller before)
    (done : decision none order metadata before = some .done)
    (uv handle : Nat) (scs : List Suspended)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs)) :
    ∃ value,
      lookupNode caller.checked.native.machine.heap handle = some value ∧
      InternedProbeProvenance.Available caller.checked.native.machine.heap value ∧ value.free = [] ∧
      MergedOrdinaryHeight.recursiveBoundary value = true ∧ scs = [] := by
  obtain ⟨_roots, _paths, storage, realized, _counts, flags⟩ := valid
  have noCandidates := (done_iff_candidates_nil order metadata before).mp done
  have inside : uv < before.core.counter := by
    rw [storage.aligned]
    exact (List.getElem?_eq_some_iff.mp stored).1
  have flag : before.expandable uv = false := by
    by_cases present : before.expandable uv = true
    · have member : uv ∈ EnumerationIndexSelection.candidates before :=
        List.mem_filter.mpr ⟨List.mem_range.mpr inside, present⟩
      rw [noCandidates] at member
      exact False.elim (List.not_mem_nil member)
    · simpa using present
  obtain ⟨value, decoded, available, closed⟩ := realized uv handle scs stored
  have classified := flags uv
  rw [stored, Option.getD_some, flag] at classified
  have frontier : MergedOrdinaryHeight.recursiveBoundary value = true ∧ scs = [] := by
    simpa [SourcePruningEnumerationNativeIndex.candidate, decoded] using classified
  exact ⟨value, decoded, available, closed, frontier⟩

/-- Done discharges proper storage when every retained native pending value is nonrecursive. -/
theorem done_discharged_of_nonrecursive_pending
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (caller : Caller width) (before : Cached)
    (valid : SourcePruningEnumerationNativeBranchCompletion.CacheValid caller before)
    (proper : ProperState before.core)
    (nonrecursive : ∀ uv handle scs,
      before.core.values[uv]? = some (.unenumerated (some handle) scs) →
      ∀ value, lookupNode caller.checked.native.machine.heap handle = some value →
        MergedOrdinaryHeight.recursiveBoundary value = false)
    (done : decision none order metadata before = some .done) :
    SourcePruningEnumerationRendering.Discharged before.core := by
  intro uv node scs stored
  cases node with
  | none => exact ⟨rfl, proper _ (List.mem_of_getElem? stored)⟩
  | some handle =>
      obtain ⟨value, decoded, _available, _closed, boundary, _empty⟩ :=
        done_pending_boundary order metadata caller before valid done uv handle scs stored
      have ordinary := nonrecursive uv handle scs stored value decoded
      rw [boundary] at ordinary
      cases ordinary

end MicroCFTA.SourcePruningEnumerationRestart

namespace MicroCFTA.SourcePruningEnumerationRendering
open Language EnumerationState EnumerationCorrectness EnumerationSchedule
open SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {NativeGuard EnumGuard : Type}

/-- The actual initial recursive root renders as the source marker at zero fragment fuel. -/
theorem initial_boundary_render
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (handle : Nat) (value : InternedConstructorTemplates.Value Symbol NativeGuard) (marker : Symbol)
    (decoded : lookupNode heap handle = some value)
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true) :
    Success (render (EnumGuard := EnumGuard) heap marker 0 0)
      (EnumerationState.initial handle) (.node marker [], []) (EnumerationState.initial handle) := by
  let before : EnumerationState.State Symbol EnumGuard := EnumerationState.initial handle
  have read : Success (getValue 1 0) before (.unenumerated (some handle) []) before := by
    apply (getValue_success 1 0 before before (.unenumerated (some handle) [])).mpr
    exact ⟨⟨0, 1, before.representatives⟩,
      by simp [before, EnumerationState.initial, UnionFind.findRoot, UnionFind.withInitialValues],
      rfl, rfl⟩
  have root : Success (expandUVar heap marker 0 0) before (.node marker []) before := by
    unfold expandUVar
    apply (success_bind _ _ _ _ _).mpr
    refine ⟨.unenumerated (some handle) [], before, read, ?_⟩
    simp only [decoded, boundary, ↓reduceIte]
    exact (success_pure (.node marker []) (.node marker []) before before).mpr ⟨rfl, rfl⟩
  unfold render
  apply (success_bind _ _ _ _ _).mpr
  refine ⟨.node marker [], before, root, ?_⟩
  change Success (pure (.node marker [], [])) before (.node marker [], []) before
  exact (success_pure (.node marker [], []) (.node marker [], []) before before).mpr ⟨rfl, rfl⟩

end MicroCFTA.SourcePruningEnumerationRendering

namespace MicroCFTA.SourcePruningEnumerationRecursive
open EnumerationState EnumerationCorrectness InternedConstructorTemplates
open SourcePruningEnumerationNodes
open InternedProbeProvenance (Available)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Original native startup at a recursive boundary emits its own undischarged root through done. -/
theorem initial_boundary_done
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (metadata : Metadata Typing) (value : Node)
    (context : Context formulas solver inventory caller memos)
    (available : Available caller.checked.native.machine.heap value)
    (closed : value.free = []) (emptyPending : metadata.pending = [])
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true) :
    ∃ handle,
      encodeNode value = some handle ∧
      lookupNode caller.checked.native.machine.heap handle = some value ∧
      let startup : Cached :=
        ⟨EnumerationState.initial handle,
          fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary value else false,
          fun _ => none⟩
      ((Packet formulas solver inventory caller memos metadata startup ∧
        EnumerationValidity.Canonical startup.core ∧
        startup.core.values[0]? = some (.unenumerated (some handle) []) ∧
        SourcePruningEnumerationPrefixAdmission.suspendedBound startup.core = 0 ∧
        EnumerationCanonicalWaiting.Correct (fun uv => uv) startup.core.values startup.waiting ∧
        ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
          ((startup.core.values[slot]?).getD .eliminated) = some (startup.expandable slot)) ∧
        EnumerationProgress.ProperState startup.core) ∧
      EnumerationGraphReferences.ReferencesCarry startup.core ∧
      EnumerationCarriers.CarriesGraph startup.core 0 ∧
      ¬ SourcePruningEnumerationRendering.Discharged startup.core ∧
      EnumerationIndexSelection.candidates startup = [] ∧
      (∀ marker, Success (SourcePruningEnumerationRendering.render
          caller.checked.native.machine.heap marker 0 0)
        startup.core (.node marker [], []) startup.core) ∧
      ∀ (order : Metadata Typing → List Nat → Option Nat),
        SourcePruningEnumerationRestart.decision none order metadata startup = some .done ∧
        ∀ workFuel recursiveFuel,
          run holeKey fits admits graph templates checkEmpty edgesOf none order workFuel recursiveFuel
            metadata caller memos.query startup =
          SourcePruningEnumerationNativeContinuations.HookResult.complete
            [⟨none, startup, caller, memos.query⟩] caller memos.query := by
  obtain ⟨handle, encoded, decoded, original, proper⟩ :=
    initial_packet_proper formulas solver inventory caller memos metadata value context available closed emptyPending
  let startup : Cached :=
    ⟨EnumerationState.initial handle,
      fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary value else false,
      fun _ => none⟩
  have noCandidates : EnumerationIndexSelection.candidates startup = [] := by
    simp [EnumerationIndexSelection.candidates, startup, EnumerationState.initial, boundary]
  refine ⟨handle, encoded, decoded, ⟨original, proper⟩,
    EnumerationRenderability.initial_references handle, ?_, ?_, noCandidates, ?_, ?_⟩
  · exact EnumerationCarriers.carries_self startup.core (initial_storage handle).total 0
      (.unenumerated (some handle) []) rfl trivial
  · intro discharged
    have impossible := discharged 0 (some handle) [] (by rfl)
    cases impossible.1
  · intro marker
    exact SourcePruningEnumerationRendering.initial_boundary_render
      caller.checked.native.machine.heap handle value marker decoded boundary
  · intro order
    have done := (SourcePruningEnumerationRestart.done_iff_candidates_nil order metadata startup).mpr noCandidates
    refine ⟨done, ?_⟩
    intro workFuel recursiveFuel
    simp only [run, done, resume]

end MicroCFTA.SourcePruningEnumerationRecursive
