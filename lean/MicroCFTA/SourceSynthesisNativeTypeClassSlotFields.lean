import MicroCFTA.SourceSynthesisNativeTypeClassPass
import MicroCFTA.SourceSynthesisTypeRouteProgramFields
import MicroCFTA.SourceCurrentAllocatedClassWorkerCompletion
import MicroCFTA.SourceCurrentClassPositionalFootprints
import MicroCFTA.SourceCurrentActualEditRowOrigins

/-!
# Mixed slot fields through the actual class pass

Typed slots retain their root annotations. Program slots retain the route
to their first Type field. The actual selected edit returns an ordinary
value at each Program slot. No output shape or annotation is an input.

The class fold executes its tail first. Each head receives that exact
returned state and forest. Final propagation retains the forest or replaces
every value with Empty. These successful graph laws do not prove progress,
failure-state preservation, all reached roles, or a global resource bound.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeClassSlotFields
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceSynthesisTypePathRoles (AnnotationFields)
open SourceEqualityProjectionGraph (select)
open SourceCurrentHereditaryTypePaths (ForestPath)
open SourceCurrentHereditaryTypeRouteConstructors (ForestRoutes route_nil)
open SourceCurrentAllocatedSharedTargetState (initial)
open SourceCurrentAllocatedClassEdits (Class)
open SourceCurrentAllocatedClassPass (Fold Pass)
open SourceCurrentClassPositionalFootprints (Unselected)
open SourceCurrentLowerOperationInvariants (SharedGood)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Ready" => SourceSynthesisNativeTypeSharedState.Ready
local notation "Worker" => SourceCurrentAllocatedSharedEditWorker.edit
variable {width : Nat}

private theorem slots_of_routes (valid : Guard → Prop) (assigned : Nat → Prop)
    {values results : List Node} (retained : ForestRoutes valid values results)
    (ordinary : ∀ index value, results[index]? = some value → assigned index → SourceEqualityRequiredCache.Ordinary value)
    (typed : ∀ index value, values[index]? = some value → ¬ assigned index → Annotated valid value)
    (fields : ∀ index value, values[index]? = some value → assigned index → AnnotationFields valid value) :
    ∀ index value, results[index]? = some value →
      (assigned index → AnnotationFields valid value) ∧ (¬ assigned index → Annotated valid value) := by
  intro index value selected
  constructor
  · intro program
    have source : ForestPath valid [(index : Int), 0] values := by
      intro original found
      exact SourceSynthesisTypeRouteProgramFields.to_route
        (fields index original (by simpa [select] using found) program)
    exact SourceSynthesisTypeRouteProgramFields.of_route (ordinary index value selected program)
      (retained [(index : Int), 0] source value (by simpa [select] using selected))
  · intro typeSlot
    have source : ForestPath valid [(index : Int)] values := by
      intro original found
      exact .annotated [] original (typed index original (by simpa [select] using found) typeSlot)
    exact route_nil (retained [(index : Int)] source value (by simpa [select] using selected))

private theorem propagate_slots (valid : Guard → Prop) (assigned : Nat → Prop) {values : List Node}
    (slots : ∀ index value, values[index]? = some value →
      (assigned index → AnnotationFields valid value) ∧ (¬ assigned index → Annotated valid value)) :
    ∀ index value, (EqualityLeafProjectionRuntimeEmpty.propagate values)[index]? = some value →
      (assigned index → AnnotationFields valid value) ∧ (¬ assigned index → Annotated valid value) := by
  intro index value found
  by_cases erased : values.any (fun value => value.referenceOf == .empty) = true
  · have member : value ∈ EqualityLeafProjectionRuntimeEmpty.propagate values := List.mem_of_getElem? found
    simp only [EqualityLeafProjectionRuntimeEmpty.propagate, erased, ite_true,
      EqualityLeafProjectionRuntimeEmpty.erase] at member
    obtain ⟨_original, _included, same⟩ := List.mem_map.mp member
    cases same
    exact ⟨fun _ => .empty, fun _ => .empty⟩
  · have selected := found
    simp only [EqualityLeafProjectionRuntimeEmpty.propagate, erased] at selected
    exact slots index value selected

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem class_ordinary (lib : Library) (assigned : Nat → Prop)
    {record values results} {before after : Checked width} {memo saved : Memo}
    (actual : Class record values before memo results after saved)
    (ready : Ready lib (initial before memo)) (available : Values before.native.machine.heap values)
    (coherent : SourceEqualityClassOrder.Coherent record)
    (footprints : ∀ index, assigned index → Unselected record index 1)
    (fields : ∀ index value, values[index]? = some value → assigned index → AnnotationFields (Origin lib) value) :
    ∀ index value, results[index]? = some value → assigned index → SourceEqualityRequiredCache.Ordinary value := by
  obtain ⟨e, p, h, m, s, n, completed⟩ := SourceCurrentAllocatedClassWorkerCompletion.class_complete actual
  have done := completed e p h m s n (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
  have good := SourceCurrentNativeOperationHeap.Good.of_native
    (SourceCurrentNativeOperationInvariants.Good.of_checked ready.checked.good)
    ready.checked.semantic ready.costs
  intro index value selected program
  obtain ⟨entries, shared, start, finish, original, _built, _sameState, _sameMemo,
      found, earlier, _later, dispatch⟩ :=
    SourceCurrentClassPositionalFootprints.class_dispatch done coherent index 1 (footprints index program) selected
  have inputFields := fields index original found program
  rcases dispatch with ⟨_absent, rfl, _same⟩ | ⟨childEntries, _selected, _absent, called⟩
  · cases inputFields <;> trivial
  · have earlierCall : SourceCurrentAllocatedSharedEditWorker.editList (Worker record values e p h m s n)
        (.editBelow entries) (values.take index) (initial before memo) =
        .done (results.take index) start := earlier
    obtain ⟨effect, current, _known⟩ := SourceCurrentLowerOperationInvariants.edit_list earlierCall
      (SharedGood.initial good ready.physicalMemo) available
      (fun value member => available value (List.mem_of_mem_take member))
    have originalsAvailable := fun value member => effect.keeps.available value (available value member)
    have inputAvailable := effect.keeps.available original (available original (List.mem_of_getElem? found))
    cases inputFields with
    | empty =>
        cases e with
        | zero => cases called
        | succ e =>
            simp only [SourceCurrentAllocatedSharedEditWorker.edit] at called
            cases called
            trivial
    | node entry rows depth free typed =>
        exact SourceCurrentActualEditRowOrigins.edit_node_ordinary called current originalsAvailable inputAvailable

/-- One actual class retains every mixed slot classification. -/
theorem class_slots (lib : Library) (assigned : Nat → Prop)
    {record values results} {before after : Checked width} {memo saved : Memo}
    (actual : Class record values before memo results after saved)
    (ready : Ready lib (initial before memo)) (available : Values before.native.machine.heap values)
    (closed : ClosedValues values) (coherent : SourceEqualityClassOrder.Coherent record)
    (routes : ∀ path ∈ record.paths, ForestPath (Origin lib) (path.map Int.ofNat) values)
    (footprints : ∀ index, assigned index → Unselected record index 1)
    (typed : ∀ index value, values[index]? = some value → ¬ assigned index → Annotated (Origin lib) value)
    (fields : ∀ index value, values[index]? = some value → assigned index → AnnotationFields (Origin lib) value) :
    ∀ index value, results[index]? = some value →
      (assigned index → AnnotationFields (Origin lib) value) ∧ (¬ assigned index → Annotated (Origin lib) value) := by
  obtain ⟨_next, _extension, _available, _closed, retained⟩ :=
    SourceSynthesisNativeTypeClassPass.class_edit lib actual ready available closed coherent routes
  exact slots_of_routes (Origin lib) assigned retained
    (class_ordinary lib assigned actual ready available coherent footprints fields) typed fields

/-- The literal right fold supplies each head with its tail's retained mixed fields. -/
theorem fold_slots (lib : Library) (assigned : Nat → Prop)
    {records values results} {before after : Checked width} {memo saved : Memo}
    (actual : Fold records values before memo results after saved)
    (ready : Ready lib (initial before memo)) (available : Values before.native.machine.heap values)
    (closed : ClosedValues values)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (routes : ∀ record ∈ records, ∀ path ∈ record.paths,
      ForestPath (Origin lib) (path.map Int.ofNat) values)
    (footprints : ∀ record ∈ records, ∀ index, assigned index → Unselected record index 1)
    (typed : ∀ index value, values[index]? = some value → ¬ assigned index → Annotated (Origin lib) value)
    (fields : ∀ index value, values[index]? = some value → assigned index → AnnotationFields (Origin lib) value) :
    ∀ index value, results[index]? = some value →
      (assigned index → AnnotationFields (Origin lib) value) ∧ (¬ assigned index → Annotated (Origin lib) value) := by
  revert ready available closed coherent routes footprints typed fields
  induction actual with
  | nil =>
      intro _ready _available _closed _coherent _routes _footprints typed fields index value found
      exact ⟨fields index value found, typed index value found⟩
  | cons tail head ih =>
      intro ready available closed coherent routes footprints typed fields
      have tailCoherent := fun record member => coherent record (List.mem_cons_of_mem _ member)
      have tailSourceRoutes := fun record member => routes record (List.mem_cons_of_mem _ member)
      have tailFootprints := fun record member => footprints record (List.mem_cons_of_mem _ member)
      have middleSlots := ih ready available closed tailCoherent tailSourceRoutes tailFootprints typed fields
      obtain ⟨middleReady, _extension, middleAvailable, middleClosed, retained⟩ :=
        SourceSynthesisNativeTypeClassPass.fold lib tail ready available closed tailCoherent tailSourceRoutes
      exact class_slots lib assigned head middleReady middleAvailable middleClosed
        (coherent _ List.mem_cons_self)
        (fun path member => retained (path.map Int.ofNat) (routes _ List.mem_cons_self path member))
        (footprints _ List.mem_cons_self)
        (fun index value found => (middleSlots index value found).2)
        (fun index value found => (middleSlots index value found).1)

/-- Actual final propagation preserves mixed fields or supplies Empty at every slot. -/
theorem pass_slots (lib : Library) (assigned : Nat → Prop)
    {records values results} {before after : Checked width} {memo saved : Memo}
    (actual : Pass records values before memo results after saved)
    (ready : Ready lib (initial before memo)) (available : Values before.native.machine.heap values)
    (closed : ClosedValues values)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (routes : ∀ record ∈ records, ∀ path ∈ record.paths,
      ForestPath (Origin lib) (path.map Int.ofNat) values)
    (footprints : ∀ record ∈ records, ∀ index, assigned index → Unselected record index 1)
    (typed : ∀ index value, values[index]? = some value → ¬ assigned index → Annotated (Origin lib) value)
    (fields : ∀ index value, values[index]? = some value → assigned index → AnnotationFields (Origin lib) value) :
    ∀ index value, results[index]? = some value →
      (assigned index → AnnotationFields (Origin lib) value) ∧ (¬ assigned index → Annotated (Origin lib) value) := by
  cases actual with
  | done actual =>
      exact propagate_slots (Origin lib) assigned
        (fold_slots lib assigned actual ready available closed coherent routes footprints typed fields)

end MicroCFTA.SourceSynthesisNativeTypeClassSlotFields
