import MicroCFTA.SourceSynthesisRequiredFootprints
import MicroCFTA.SourceCurrentAllocatedPrecheck
import MicroCFTA.SourceCurrentConjunctionSelectedRecords

/-!
# Program annotation demands from actual Parent selection

The actual precheck orders its own records. The current scan retains only
those records. Source occurrence equations derive their endpoint regions.
Each selected program child therefore requires only its annotation field.
This result does not assert a region for an arbitrary inherited payload.
-/
namespace MicroCFTA.SourceSynthesisSelectedProgramFootprints
open EqualityNormalize InternedConstructorTemplates SourceEqualityClassOrder
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression application ofType)
open SourceSynthesisGuardRegions SourceSynthesisRequiredFootprints
open SourceEqualityNeeded (Needed)
open SourceCurrentAllocatedPrecheck (Receipt)
open SourceCurrentConjunctionClassScan (Scan)
open SourceCurrentConjunctionSelectedRecords (Retained)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source

variable {width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
variable {loaded : Allocated} {inherited own : EqValue} {before scanned : Checked width}
variable {records kept : List Record} {budget : Nat} {values : List Node}
variable {fourth savedFourth : SourceCurrentEmptinessMemo.Memo}
variable {outcome : Option Class} {selected : Constraints}
variable {scan : Scan budget source reaches values (records.map Record.paths)
  (SourceCurrentAllocatedPrecheck.state before loaded inherited) fourth outcome selected scanned savedFourth}

private theorem retained_within {guard : Guard}
    (receipt : Receipt formulas solver inventory guard loaded inherited before own (.classes records))
    (retained : Retained scan records kept) (region : Path → Prop)
    (endpoints : ∀ path ∈ members ((SourceCompactGuards.sourceEqualities guard).getD []), region path) :
    ∀ path ∈ members (kept.map Record.paths), region path := by
  obtain ⟨_, originals, _, classes, ordered, _⟩ := receipt.classes records rfl
  intro path member
  obtain ⟨paths, present, contained⟩ := (mem_members _ _).mp member
  obtain ⟨record, included, same⟩ := List.mem_map.mp present
  subst paths
  have orderedMember : record ∈ SourceEqualityClassOrder.ordered originals := by
    simpa only [ordered] using retained.fields.1.subset included
  have originalMember : record ∈ originals := (ordered_perm originals).mem_iff.mp orderedMember
  have originalPath : path ∈ members (originals.map Record.paths) :=
    (mem_members _ _).mpr ⟨record.paths, List.mem_map.mpr ⟨record, originalMember, rfl⟩, contained⟩
  apply endpoints path
  simpa only [classes, Option.getD] using originalPath

/-- Actual application selection leaves only child zero selected inside each program child. -/
theorem application_annotation_only (types function argument : Expression)
    (sourceName : String) (guard : Guard) (sourceChildren : List Expression)
    (occurrence : application types function argument = .node [.mk sourceName guard sourceChildren])
    (receipt : Receipt formulas solver inventory guard loaded inherited before own (.classes records))
    (retained : Retained scan records kept) {entries childEntries : List (Int × Needed)}
    (built : SourceEqualityNeeded.build
      (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) = .node entries)
    (forestIndex : Nat) (programSlot : forestIndex = 2 ∨ forestIndex = 3)
    (found : SourceEqualityNeededMap.lookup (forestIndex : Int) entries = some (.node childEntries)) :
    ∀ index : Nat, index ≠ 0 → SourceEqualityNeededMap.lookup (index : Int) childEntries = none := by
  have within := retained_within receipt retained applicationRegion
    (application_guard_endpoints types function argument sourceName guard sourceChildren occurrence).2
  intro index nonzero
  have excluded := application_unselected (kept.map Record.paths) within index nonzero built
  rcases programSlot with rfl | rfl
  · exact excluded.1 (.node childEntries) found childEntries rfl
  · exact excluded.2 (.node childEntries) found childEntries rfl

/-- Actual filter selection leaves only child zero selected inside its program child. -/
theorem filter_annotation_only (candidates goal : Expression)
    (sourceName : String) (guard : Guard) (sourceChildren : List Expression)
    (occurrence : ofType candidates goal = .node [.mk sourceName guard sourceChildren])
    (receipt : Receipt formulas solver inventory guard loaded inherited before own (.classes records))
    (retained : Retained scan records kept) {entries childEntries : List (Int × Needed)}
    (built : SourceEqualityNeeded.build
      (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) = .node entries)
    (found : SourceEqualityNeededMap.lookup (1 : Int) entries = some (.node childEntries)) :
    ∀ index : Nat, index ≠ 0 → SourceEqualityNeededMap.lookup (index : Int) childEntries = none := by
  have within := retained_within receipt retained filterRegion
    (filter_guard_endpoints candidates goal sourceName guard sourceChildren occurrence).2
  intro index nonzero
  exact filter_unselected (kept.map Record.paths) within index nonzero built
    (.node childEntries) found childEntries rfl

end MicroCFTA.SourceSynthesisSelectedProgramFootprints
