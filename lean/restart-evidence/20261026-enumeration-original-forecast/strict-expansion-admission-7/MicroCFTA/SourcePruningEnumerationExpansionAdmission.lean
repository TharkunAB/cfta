import MicroCFTA.SourcePruningEnumerationPrefixAdmission
import MicroCFTA.SourcePruningEnumerationOriginalForecast

namespace MicroCFTA.SourcePruningEnumerationExpansionAdmission
open EnumerationState EnumerationCorrectness EnumerationSchedule InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourcePruningEnumerationIncomingReservation (Seed)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceCurrentConstrainedCapEditForecast (headProfile)
open SourcePruningEnumerationSelectedStep (Result PrefixValid finish runPrefix)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationNodes (lookupNode)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Reserve the ordinary scan after the original narrowing read and rebuild forecast. -/
def narrowSeed (seed : Seed) : Seed := (seed.1, headProfile seed.2)

/-- Fix the complete scan count before the narrowed caller and rows exist. -/
noncomputable def count (seed : Seed) (before : Core) : Nat :=
  SourcePruningEnumerationOriginalForecast.count (narrowSeed seed)
    (SourcePruningEnumerationPrefixAdmission.suspendedBound before)

/-- The original reservation supplies ordinary admission at each actual retained prefix cache. -/
theorem narrowed_ordinary_reservation
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (fuel uv : Nat) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv))
    (seed : Seed)
    (bounded : Fits seed.2 caller.checked) (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selected : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectedLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (reserved : SourcePruningEnumerationIncomingReservation.Reserved bits (narrowSeed seed) (count seed before.core))
    (observed : Result (bits + 2) Typing)
    (valid : PrefixValid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
      formulas solver inventory fuel uv caller before memos observed) :
    match observed with
    | .narrowed _ _ reached queries _ (some after) _ _ =>
        ∃ (handle : Nat) (scs : List Suspended) (value : Node) (final : Memos),
          (Post formulas solver inventory caller reached final ∧ final.query = queries ∧
          Packet formulas solver inventory reached final metadata after ∧
          EnumerationDriver.Ready uv after.core ∧
          after.core.values[uv]? = some (.unenumerated (some handle) scs) ∧
          lookupNode reached.checked.native.machine.heap handle = some value ∧
          Available reached.checked.native.machine.heap value ∧ value.free = [] ∧
          EnumerationReferences.IncomingAvoid uv after.core ∧
          EnumerationDependencies.InputsPending after.core scs ∧
          (∀ sc ∈ scs, sc.var < before.core.counter) ∧
          scs.length ≤ SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ∧
          after.core.counter = before.core.counter ∧ after.waiting = before.waiting ∧
          Fits (headProfile seed.2) reached.checked ∧ Heap (fun guard => guard ∈ seed.1) reached.checked.native.machine.heap) ∧
          ∀ entry rows depth free, value = .node entry rows depth free →
            SourcePruningEnumerationNativeBranchCompletion.cost scs after.core.counter
                (edgesOf (.node entry rows depth free)) ≤ count seed before.core ∧
            SourcePruningEnumerationIncomingReservation.Reserved bits (narrowSeed seed)
              (SourcePruningEnumerationNativeBranchCompletion.cost scs after.core.counter
                (edgesOf (.node entry rows depth free)))
    | _ => True := by
  have admission := SourcePruningEnumerationPrefixAdmission.narrowed_admission
    holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
    fuel uv caller memos before packet chosen seed.2 (fun guard => guard ∈ seed.1) bounded known observed valid
  cases observed with
  | stopped _ _ | parked _ _ _ => trivial
  | narrowed checked prepared reached queries action candidate right ordinary =>
      cases candidate with
      | none => trivial
      | some after =>
          obtain ⟨handle, scs, value, final, full⟩ := admission
          obtain ⟨post, saved, returned, ready, stored, decoded, available, closed, incoming, pending,
            ids, lengths, counter, waiting, afterFits, afterKnown⟩ := full
          refine ⟨handle, scs, value, final,
            ⟨post, saved, returned, ready, stored, decoded, available, closed, incoming, pending,
              ids, lengths, counter, waiting, afterFits, afterKnown⟩, ?_⟩
          intro entry rows depth free same
          subst value
          have heapFits : SourceCurrentConstrainedCapRequiredResources.HeapFits
              (headProfile seed.2) reached.checked.native.machine.heap :=
            ⟨afterFits.nodes, afterFits.edges, afterFits.stored⟩
          have exactCost := SourcePruningEnumerationOriginalForecast.cost_le (seed.1, headProfile seed.2)
            (SourcePruningEnumerationPrefixAdmission.suspendedBound before.core)
            reached.checked.native.machine.heap heapFits afterKnown
            returned.context.ready.semantic.ready.semantic.1.normal.facts.linked
            entry rows (edgesOf (.node entry rows depth free)) depth free available
            (selected entry rows depth free) (selectedLength entry rows depth free)
            scs after.core.counter lengths
          have costBound : SourcePruningEnumerationNativeBranchCompletion.cost scs after.core.counter
              (edgesOf (.node entry rows depth free)) ≤ count seed before.core := by
            simpa only [count, narrowSeed] using exactCost
          exact ⟨costBound, reserved.prefix costBound⟩

/-- A current packet derives all earlier prefix outputs and the original scan reservation. -/
theorem packet_prefix_complete_reservation
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (seed : Seed)
    (bounded : Fits seed.2 caller.checked) (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (reserved : SourcePruningEnumerationIncomingReservation.Reserved bits (narrowSeed seed) (count seed before.core)) :
    ∃ bound, ∀ extra selected,
      SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand selected) →
      let observed := runPrefix holeKey fits admits graph templates stop order metadata
        (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
        selected caller before memos.query
      (PrefixValid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
        formulas solver inventory (bound + extra) selected caller before memos observed ∧
      SourcePruningEnumerationSelectedStep.Resources seed.2 (fun guard => guard ∈ seed.1) caller observed ∧
      match observed with
      | .parked _ (some after) _ => Packet formulas solver inventory caller memos metadata after
      | .narrowed _ _ reached queries _ (some after) _ _ =>
          ∃ final, Post formulas solver inventory caller reached final ∧ final.query = queries ∧
            Packet formulas solver inventory reached final metadata after
      | _ => True) ∧
      (match observed with
    | .narrowed _ _ reached queries _ (some after) _ _ =>
        ∃ (handle : Nat) (scs : List Suspended) (value : Node) (final : Memos),
          (Post formulas solver inventory caller reached final ∧ final.query = queries ∧
          Packet formulas solver inventory reached final metadata after ∧
          EnumerationDriver.Ready selected after.core ∧
          after.core.values[selected]? = some (.unenumerated (some handle) scs) ∧
          lookupNode reached.checked.native.machine.heap handle = some value ∧
          Available reached.checked.native.machine.heap value ∧ value.free = [] ∧
          EnumerationReferences.IncomingAvoid selected after.core ∧
          EnumerationDependencies.InputsPending after.core scs ∧
          (∀ sc ∈ scs, sc.var < before.core.counter) ∧
          scs.length ≤ SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ∧
          after.core.counter = before.core.counter ∧ after.waiting = before.waiting ∧
          Fits (headProfile seed.2) reached.checked ∧ Heap (fun guard => guard ∈ seed.1) reached.checked.native.machine.heap) ∧
          ∀ entry rows depth free, value = .node entry rows depth free →
            SourcePruningEnumerationNativeBranchCompletion.cost scs after.core.counter
                (edgesOf (.node entry rows depth free)) ≤ count seed before.core ∧
            SourcePruningEnumerationIncomingReservation.Reserved bits (narrowSeed seed)
              (SourcePruningEnumerationNativeBranchCompletion.cost scs after.core.counter
                (edgesOf (.node entry rows depth free)))
    | _ => True) := by
  obtain ⟨bound, complete⟩ := SourcePruningEnumerationRecursive.packet_prefix_complete_resources
    holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
    caller memos before packet seed.2 (fun guard => guard ∈ seed.1) bounded known
  refine ⟨bound, ?_⟩
  intro extra selected chosen
  dsimp only
  refine ⟨complete extra selected chosen, ?_⟩
  exact narrowed_ordinary_reservation holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
    formulas solver inventory (bound + extra) selected caller memos before packet chosen seed bounded known
    selectionMembers selectionLength reserved _ (complete extra selected chosen).1

end MicroCFTA.SourcePruningEnumerationExpansionAdmission
