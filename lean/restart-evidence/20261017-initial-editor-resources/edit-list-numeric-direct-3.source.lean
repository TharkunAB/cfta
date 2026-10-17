import MicroCFTA.SourceCurrentConstrainedCapEditNumeric

/-!
# Complete shared forest edits from initial numeric reservations

The literal forest length fixes the outer child scan. Every selected node
uses the proved finite-trie producer. The source root-leaf branch makes
no call. Compiled edits retain their original signed paths and callbacks.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapEditListNumeric
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityEdits SourceCurrentEditDomains
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentAllocatedSharedEditGraph
open SourceCurrentAllocatedSharedEditEffects (ChildrenReceipt ListSafe)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile Le Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
namespace Forecast
export SourceCurrentConstrainedCapEditForecast (planProfile scan stageFuel)
end Forecast
namespace Worker
export SourceCurrentAllocatedSharedEditWorker (edit editList editAll Outcome)
end Worker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Stored" => SourceCurrentConstrainedCapMixedShared.Stored
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Cap" => SourceCurrentConstrainedCap.Cap Plain
local notation "outputDepth" => SourceCurrentConstrainedCapMixedEdit.outputDepth
variable {bits : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- The source root branch and original forest length determine the complete return forecast. -/
noncomputable def finalProfile (record : SourceEqualityClassOrder.Record) (count : Nat)
    (edits : Edits EqualityNormalize.Path) (length : Nat) (profile : Profile) : Profile :=
  match edits with
  | .editAt _ => profile
  | .editBelow _ => Forecast.scan (Forecast.planProfile record count (sizeOf edits)) length profile

/-- An ignored root callback needs no query room. -/
noncomputable def Reserved (bits : Nat) (record : SourceEqualityClassOrder.Record) (count : Nat)
    (edits : Edits EqualityNormalize.Path) (length : Nat) (profile : Profile) : Prop :=
  match edits with
  | .editAt _ => True
  | .editBelow _ => Room bits (finalProfile record count edits length profile)

/-- One initial ceiling covers all six worker arguments in the literal forest branch. -/
noncomputable def fuel (record : SourceEqualityClassOrder.Record) (count : Nat)
    (edits : Edits EqualityNormalize.Path) (length : Nat) (profile : Profile) : Nat :=
  match edits with
  | .editAt _ => 0
  | .editBelow _ => max (SourceCurrentConstrainedCapEditScans.editFuel (sizeOf edits))
      (Forecast.stageFuel record count (finalProfile record count edits length profile))

/-- Initial class support and one pure reservation construct the complete forest edit. -/
theorem complete (capturedDepth inputDepth : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
    (base : Heap) (before : SharedState (bits + 2)) (profile : Profile)
    (ready : Ready formulas solver inventory record originals base before)
    (frame : Frame formulas solver inventory before.checked) (fits : Fits profile before.checked)
    (known : Values base originals)
    (domains : ∀ path ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) originals)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (edits : Edits EqualityNormalize.Path) (populated : Populated edits) (allowed : Allowed record edits)
    (values : List (Value Symbol Guard)) (available : Values before.checked.native.machine.heap values)
    (safe : ListSafe edits values) (inputCaps : ∀ value ∈ values, Cap inputDepth value)
    (memos : Memos) (valid : Valid before.checked.native.machine.heap memos)
    (stored : Stored record originals before) (capturedCaps : ∀ original ∈ originals, Cap capturedDepth original)
    (reserved : Reserved bits record originals.length edits values.length profile) :
    ∃ results after next final, ∃ actual : EditList record originals edits values before results after,
      ListReads formulas solver base actual memos final ∧
      ChildrenReceipt formulas solver next record originals base values before results after memos final ∧
      Frame formulas solver next after.checked ∧
      Fits (finalProfile record originals.length edits values.length profile) after.checked ∧
      Stored record originals after ∧ (∀ value ∈ results, Cap (outputDepth capturedDepth inputDepth edits) value) ∧
      Worker.editList (Worker.edit record originals
        (fuel record originals.length edits values.length profile) (fuel record originals.length edits values.length profile)
        (fuel record originals.length edits values.length profile) (fuel record originals.length edits values.length profile)
        (fuel record originals.length edits values.length profile) (fuel record originals.length edits values.length profile))
        edits values before = .done results after := by
  cases edits with
  | editAt target =>
      have reads : ListReads formulas solver base (EditList.leaf (record := record) (originals := originals)
          (target := target) (values := values) (state := before)) memos memos := .leaf
      obtain ⟨_inventory, receipt⟩ := SourceCurrentAllocatedSharedEditEffects.list_effects reads populated allowed
        ready available safe valid
      have bounded := SourceCurrentConstrainedCapMixedEdit.list reads inventory capturedDepth inputDepth populated allowed
        ready available safe valid known domains stored capturedCaps inputCaps
      exact ⟨values, before, inventory, memos, .leaf, reads,
        SourceCurrentConstrainedCapEditReceipt.children_receipt receipt frame, frame, fits, bounded.1, bounded.2, rfl⟩
  | editBelow entries =>
      let level := sizeOf (Edits.editBelow entries : Edits EqualityNormalize.Path)
      let ceiling := finalProfile record originals.length (.editBelow entries) values.length profile
      have sizes : ∀ index child, (index, child) ∈ entries → sizeOf child ≤ level := by
        intro index child member
        have smaller := List.sizeOf_lt_of_mem member
        simp only [Prod.mk.sizeOf_spec] at smaller
        dsimp only [level]
        simp only [Edits.editBelow.sizeOf_spec]
        omega
      have node := SourceCurrentConstrainedCapEditNumeric.node_complete (bits := bits) capturedDepth inputDepth level
        formulas solver record originals base known domains coherent active capturedCaps
      obtain ⟨results, after, next, final, children, reads, receipt, returned, finalFits, finalStored, done⟩ :=
        SourceCurrentConstrainedCapEditScans.children formulas solver record originals base inputDepth level
          node entries sizes 0 values before inventory profile ceiling populated allowed ready frame fits available safe inputCaps
          stored memos valid (Le.refl _) reserved
      have allReads : ListReads formulas solver base (.children children) memos final := .children reads
      have bounded := SourceCurrentConstrainedCapMixedEdit.list allReads inventory capturedDepth inputDepth populated allowed
        ready available safe valid known domains stored capturedCaps inputCaps
      have editEnough : SourceCurrentConstrainedCapEditScans.editFuel level ≤
          fuel record originals.length (.editBelow entries) values.length profile := Nat.le_max_left _ _
      have stageEnough : Forecast.stageFuel record originals.length ceiling ≤
          fuel record originals.length (.editBelow entries) values.length profile := Nat.le_max_right _ _
      have lifted := SourceCurrentAllocatedSharedEditWorkerStability.children_edit_done_stable done
        editEnough stageEnough stageEnough stageEnough stageEnough stageEnough
      refine ⟨results, after, next, final, .children children, allReads, receipt, returned,
        finalFits, finalStored, bounded.2, ?_⟩
      simpa only [Worker.editList] using lifted

/-- The literal signed source compiler constructs its complete forest execution at the same initial ceiling. -/
theorem compiled (capturedDepth inputDepth : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
    (base : Heap) (before : SharedState (bits + 2)) (profile : Profile)
    (ready : Ready formulas solver inventory record originals base before)
    (frame : Frame formulas solver inventory before.checked) (fits : Fits profile before.checked)
    (known : Values base originals)
    (domains : ∀ path ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) originals)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (pairs : List (Path × EqualityNormalize.Path))
    (callbacks : ∀ path target, (path, target) ∈ pairs → target ∈ record.paths)
    (values : List (Value Symbol Guard)) (available : Values before.checked.native.machine.heap values)
    (safe : ListSafe (build pairs) values) (inputCaps : ∀ value ∈ values, Cap inputDepth value)
    (memos : Memos) (valid : Valid before.checked.native.machine.heap memos)
    (stored : Stored record originals before) (capturedCaps : ∀ original ∈ originals, Cap capturedDepth original)
    (reserved : Reserved bits record originals.length (build pairs) values.length profile) :
    ∃ results after next final, ∃ actual : EditList record originals (build pairs) values before results after,
      ListReads formulas solver base actual memos final ∧
      ChildrenReceipt formulas solver next record originals base values before results after memos final ∧
      Frame formulas solver next after.checked ∧
      Fits (finalProfile record originals.length (build pairs) values.length profile) after.checked ∧
      Stored record originals after ∧ (∀ value ∈ results, Cap (outputDepth capturedDepth inputDepth (build pairs)) value) ∧
      Worker.editAll record originals
        (fuel record originals.length (build pairs) values.length profile)
        (fuel record originals.length (build pairs) values.length profile)
        (fuel record originals.length (build pairs) values.length profile)
        (fuel record originals.length (build pairs) values.length profile)
        (fuel record originals.length (build pairs) values.length profile)
        (fuel record originals.length (build pairs) values.length profile) pairs values before = .done results after := by
  have allowed : Allowed record (build pairs) :=
    SourceEqualityEdits.build_all (fun target => target ∈ record.paths) pairs callbacks
  obtain ⟨results, after, next, final, actual, reads, receipt, returned, finalFits, finalStored, caps, done⟩ :=
    complete capturedDepth inputDepth formulas solver inventory record originals base before profile ready frame fits
      known domains coherent active (build pairs) (build_populated pairs) allowed values available safe inputCaps
      memos valid stored capturedCaps reserved
  exact ⟨results, after, next, final, actual, reads, receipt, returned, finalFits, finalStored, caps,
    by simpa only [Worker.editAll] using done⟩

end MicroCFTA.SourceCurrentConstrainedCapEditListNumeric
