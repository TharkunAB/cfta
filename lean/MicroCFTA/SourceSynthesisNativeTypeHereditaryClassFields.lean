import MicroCFTA.SourceSynthesisNativeTypeHereditaryEditFields
import MicroCFTA.SourceSynthesisNativeTypeClassPass
import MicroCFTA.SourceCurrentClassPositionalFootprints

/-!
# Recursive Program fields through the actual class pass

Source footprints exclude every nonzero child of each Program operand.
Its Type annotation can change. Its recursive Program children retain
their literal values. Each selected head supplies the actual suffix state.
The class fold executes its tail first. Final propagation retains the
forest or supplies Empty at every slot.

These laws concern completed current graphs and initial certificates.
They do not prove failed-prefix fields, completion, all reached source
roles, finite-word bounds or native lazy demand order.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeHereditaryClassFields
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceSynthesisHereditaryProgramFields (ValueFields)
open SourceEqualityProjectionGraph (select)
open SourceEqualityEdits (Edits)
open SourceEqualityNeededMap (lookup)
open SourceCurrentHereditaryTypePaths (ForestPath)
open SourceCurrentHereditaryTypeEditPlan
open SourceCurrentHereditaryTypeRouteConstructors (route_nil)
open SourceCurrentEditDomains (Populated)
open SourceCurrentAllocatedSharedEditGraph (EditList EditChildren)
open SourceCurrentAllocatedSharedTargetState (initial)
open SourceCurrentAllocatedClassEditPlan (compiled compiled_populated)
open SourceCurrentAllocatedClassEdits (Class)
open SourceCurrentAllocatedClassPass (Fold Pass)
open SourceCurrentClassPositionalFootprints (Unselected)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Ready" => SourceSynthesisNativeTypeSharedState.Ready
variable {width : Nat}

private theorem propagate_fields (valid : Guard → Prop) (literal : String → Symbol)
    (assigned : Nat → Prop) {values : List Node}
    (slots : ∀ index value, values[index]? = some value →
      (assigned index → ValueFields valid literal value) ∧ (¬ assigned index → Annotated valid value)) :
    ∀ index value, (EqualityLeafProjectionRuntimeEmpty.propagate values)[index]? = some value →
      (assigned index → ValueFields valid literal value) ∧ (¬ assigned index → Annotated valid value) := by
  intro index value found
  by_cases erased : values.any (fun value => value.referenceOf == .empty) = true
  · have member := List.mem_of_getElem? found
    simp only [EqualityLeafProjectionRuntimeEmpty.propagate, erased, ite_true,
      EqualityLeafProjectionRuntimeEmpty.erase] at member
    obtain ⟨_original, _included, same⟩ := List.mem_map.mp member
    cases same
    exact ⟨fun _ => .empty, fun _ => .empty⟩
  · have selected := found
    simp only [EqualityLeafProjectionRuntimeEmpty.propagate, erased] at selected
    exact slots index value selected

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem children_fields (lib : Library) (literal : String → Symbol) (assigned : Nat → Prop)
    {record originals entries offset inputs before outputs after}
    (actual : EditChildren (width := width) record originals entries offset inputs before outputs after)
    (ready : Ready lib before) (originalAvailable : Values before.checked.native.machine.heap originals)
    (originalClosed : ClosedValues originals)
    (originalRoutes : ∀ own ∈ record.paths, ForestPath (Origin lib) (own.map Int.ofNat) originals)
    (populated : Populated (.editBelow entries))
    (available : Values before.checked.native.machine.heap inputs) (closed : ClosedValues inputs)
    (paths : ChildrenPaths (Origin lib) entries offset inputs)
    (protectedChildren : ∀ index, assigned index → ∀ childIndex : Nat, childIndex ≠ 0 →
      lookup (index : Int) entries = none ∨ ∃ childEntries,
        lookup (index : Int) entries = some (.editBelow childEntries) ∧ lookup (childIndex : Int) childEntries = none)
    (typed : ∀ index value, inputs[index]? = some value → ¬ assigned (offset + index) → Annotated (Origin lib) value)
    (fields : ∀ index value, inputs[index]? = some value → assigned (offset + index) → ValueFields (Origin lib) literal value) :
    ∀ index value, outputs[index]? = some value →
      (assigned (offset + index) → ValueFields (Origin lib) literal value) ∧
        (¬ assigned (offset + index) → Annotated (Origin lib) value) := by
  let sourceInputs := inputs
  let returnedValues := outputs
  cases actual with
  | nil => intro index value found; cases found
  | unselected offset absent rest =>
      have tailTyped : ∀ (index : Nat) (value : Node), sourceInputs.tail[index]? = some value →
          ¬ assigned (offset + 1 + index) → Annotated (Origin lib) value := by
        intro index value found notProgram
        apply typed (index + 1) value found
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using notProgram
      have tailFields : ∀ (index : Nat) (value : Node), sourceInputs.tail[index]? = some value →
          assigned (offset + 1 + index) → ValueFields (Origin lib) literal value := by
        intro index value found program
        apply fields (index + 1) value found
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using program
      have later := children_fields lib literal assigned rest ready originalAvailable originalClosed originalRoutes
        populated (fun value member => available value (List.mem_cons_of_mem _ member))
        (fun value member => closed value (List.mem_cons_of_mem _ member))
        (children_tail paths) protectedChildren tailTyped tailFields
      intro index value found
      cases index with
      | zero =>
          cases Option.some.inj found
          exact ⟨fields 0 _ rfl, typed 0 _ rfl⟩
      | succ index =>
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using later index value found
  | selected offset found first rest =>
      have selectedPaths := children_selected paths found
      have selectedPopulated := selected_populated populated found
      obtain ⟨middleReady, extension, ownAvailable, ownClosed, retained⟩ :=
        SourceSynthesisNativeTypeSharedEdit.node lib first ready originalAvailable originalClosed originalRoutes
          selectedPopulated.1 selectedPopulated.2 (available _ List.mem_cons_self)
          (closed _ List.mem_cons_self) selectedPaths
      have ownFields : assigned offset → ValueFields (Origin lib) literal (returnedValues.headD .empty) := by
        intro program
        rcases protectedChildren offset program 1 (by decide) with absent | ⟨childEntries, selected, _absent⟩
        · rw [found] at absent; cases absent
        · have same := Option.some.inj (found.symm.trans selected)
          have only : ∀ childIndex : Nat, childIndex ≠ 0 → lookup (childIndex : Int) childEntries = none := by
            intro childIndex nonzero
            rcases protectedChildren offset program childIndex nonzero with absent | ⟨otherEntries, otherSelected, otherAbsent⟩
            · rw [found] at absent; cases absent
            · have entriesEq := Edits.editBelow.inj (Option.some.inj (selected.symm.trans otherSelected))
              simpa only [entriesEq] using otherAbsent
          obtain ⟨_next, _extension, _available, _closed, _retained, resultFields⟩ :=
            SourceSynthesisNativeTypeHereditaryEditFields.below_fields lib literal
              (by simpa only [same] using first) ready originalAvailable originalClosed originalRoutes
              (by simpa only [same] using selectedPopulated.1)
              (by simpa only [same] using selectedPopulated.2)
              (available _ List.mem_cons_self) (closed _ List.mem_cons_self)
              (by simpa only [same] using selectedPaths) (fields 0 _ rfl (by simpa using program)) only
          exact resultFields
      have ownTyped : ¬ assigned offset → Annotated (Origin lib) (returnedValues.headD .empty) := by
        intro notProgram
        exact route_nil (retained [] (.annotated [] _ (typed 0 _ rfl (by simpa using notProgram))))
      have tailTyped : ∀ (index : Nat) (value : Node), sourceInputs.tail[index]? = some value →
          ¬ assigned (offset + 1 + index) → Annotated (Origin lib) value := by
        intro index value present notProgram
        apply typed (index + 1) value present
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using notProgram
      have tailFields : ∀ (index : Nat) (value : Node), sourceInputs.tail[index]? = some value →
          assigned (offset + 1 + index) → ValueFields (Origin lib) literal value := by
        intro index value present program
        apply fields (index + 1) value present
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using program
      have later := children_fields lib literal assigned rest middleReady
        (fun value member => extension.available value (originalAvailable value member)) originalClosed originalRoutes
        populated (fun value member => extension.available value (available value (List.mem_cons_of_mem _ member)))
        (fun value member => closed value (List.mem_cons_of_mem _ member))
        (children_tail paths) protectedChildren tailTyped tailFields
      intro index value present
      cases index with
      | zero =>
          cases Option.some.inj present
          simpa only [Nat.add_zero, returnedValues, List.headD_cons] using And.intro ownFields ownTyped
      | succ index =>
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using later index value present
termination_by inputs.length

/-- Each actual class retains recursive Program fields and all other Type slots. -/
theorem class_fields (lib : Library) (literal : String → Symbol) (assigned : Nat → Prop)
    {record values results} {before after : Checked width} {memo saved : Memo}
    (actual : Class record values before memo results after saved)
    (ready : Ready lib (initial before memo)) (available : Values before.native.machine.heap values)
    (closed : ClosedValues values) (coherent : SourceEqualityClassOrder.Coherent record)
    (routes : ∀ path ∈ record.paths, ForestPath (Origin lib) (path.map Int.ofNat) values)
    (footprints : ∀ index, assigned index → ∀ childIndex, childIndex ≠ 0 → Unselected record index childIndex)
    (typed : ∀ index value, values[index]? = some value → ¬ assigned index → Annotated (Origin lib) value)
    (fields : ∀ index value, values[index]? = some value → assigned index → ValueFields (Origin lib) literal value) :
    ∀ index value, results[index]? = some value →
      (assigned index → ValueFields (Origin lib) literal value) ∧ (¬ assigned index → Annotated (Origin lib) value) := by
  cases actual with
  | edit lower =>
      cases built : compiled record with
      | editAt target =>
          rw [built] at lower
          cases lower
          intro index value found
          exact ⟨fields index value found, typed index value found⟩
      | editBelow entries =>
          have populated := compiled_populated record
          rw [built] at populated lower
          have compiledPaths := compiled_forest_paths (Origin lib) record coherent values routes
          rw [built] at compiledPaths
          cases lower with
          | children trace =>
              have protectedChildren : ∀ index, assigned index → ∀ childIndex : Nat, childIndex ≠ 0 →
                  lookup (index : Int) entries = none ∨ ∃ childEntries,
                    lookup (index : Int) entries = some (.editBelow childEntries) ∧
                    lookup (childIndex : Int) childEntries = none := by
                intro index program childIndex nonzero
                obtain ⟨otherEntries, otherBuilt, dispatch⟩ :=
                  SourceCurrentClassPositionalFootprints.compiled_unselected record coherent index childIndex
                    (footprints index program childIndex nonzero)
                have entriesEq := Edits.editBelow.inj (built.symm.trans otherBuilt)
                simpa only [← entriesEq, Int.ofNat_eq_natCast] using dispatch
              simpa only [Nat.zero_add] using children_fields lib literal assigned trace ready available closed routes populated available closed
                (forest_to_children compiledPaths) protectedChildren
                  (by simpa only [Nat.zero_add] using typed) (by simpa only [Nat.zero_add] using fields)

/-- The literal right fold supplies each head with its tail's recursive fields. -/
theorem fold_fields (lib : Library) (literal : String → Symbol) (assigned : Nat → Prop)
    {records values results} {before after : Checked width} {memo saved : Memo}
    (actual : Fold records values before memo results after saved)
    (ready : Ready lib (initial before memo)) (available : Values before.native.machine.heap values)
    (closed : ClosedValues values)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (routes : ∀ record ∈ records, ∀ path ∈ record.paths,
      ForestPath (Origin lib) (path.map Int.ofNat) values)
    (footprints : ∀ record ∈ records, ∀ index, assigned index →
      ∀ childIndex, childIndex ≠ 0 → Unselected record index childIndex)
    (typed : ∀ index value, values[index]? = some value → ¬ assigned index → Annotated (Origin lib) value)
    (fields : ∀ index value, values[index]? = some value → assigned index → ValueFields (Origin lib) literal value) :
    ∀ index value, results[index]? = some value →
      (assigned index → ValueFields (Origin lib) literal value) ∧ (¬ assigned index → Annotated (Origin lib) value) := by
  revert ready available closed coherent routes footprints typed fields
  induction actual with
  | nil =>
      intro _ready _available _closed _coherent _routes _footprints typed fields index value found
      exact ⟨fields index value found, typed index value found⟩
  | cons tail head ih =>
      intro ready available closed coherent routes footprints typed fields
      have tailCoherent := fun record member => coherent record (List.mem_cons_of_mem _ member)
      have tailRoutes := fun record member => routes record (List.mem_cons_of_mem _ member)
      have tailFootprints := fun record member => footprints record (List.mem_cons_of_mem _ member)
      have middleFields := ih ready available closed tailCoherent tailRoutes tailFootprints typed fields
      obtain ⟨middleReady, _extension, middleAvailable, middleClosed, retained⟩ :=
        SourceSynthesisNativeTypeClassPass.fold lib tail ready available closed tailCoherent tailRoutes
      exact class_fields lib literal assigned head middleReady middleAvailable middleClosed
        (coherent _ List.mem_cons_self)
        (fun path member => retained (path.map Int.ofNat) (routes _ List.mem_cons_self path member))
        (footprints _ List.mem_cons_self)
        (fun index value found => (middleFields index value found).2)
        (fun index value found => (middleFields index value found).1)

/-- Final actual propagation retains the recursive fields or supplies Empty. -/
theorem pass_fields (lib : Library) (literal : String → Symbol) (assigned : Nat → Prop)
    {records values results} {before after : Checked width} {memo saved : Memo}
    (actual : Pass records values before memo results after saved)
    (ready : Ready lib (initial before memo)) (available : Values before.native.machine.heap values)
    (closed : ClosedValues values)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (routes : ∀ record ∈ records, ∀ path ∈ record.paths,
      ForestPath (Origin lib) (path.map Int.ofNat) values)
    (footprints : ∀ record ∈ records, ∀ index, assigned index →
      ∀ childIndex, childIndex ≠ 0 → Unselected record index childIndex)
    (typed : ∀ index value, values[index]? = some value → ¬ assigned index → Annotated (Origin lib) value)
    (fields : ∀ index value, values[index]? = some value → assigned index → ValueFields (Origin lib) literal value) :
    ∀ index value, results[index]? = some value →
      (assigned index → ValueFields (Origin lib) literal value) ∧ (¬ assigned index → Annotated (Origin lib) value) := by
  cases actual with
  | done actual =>
      exact propagate_fields (Origin lib) literal assigned
        (fold_fields lib literal assigned actual ready available closed coherent routes footprints typed fields)

end MicroCFTA.SourceSynthesisNativeTypeHereditaryClassFields
