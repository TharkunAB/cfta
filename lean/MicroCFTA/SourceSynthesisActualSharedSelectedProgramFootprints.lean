import MicroCFTA.SourceCurrentSharedScanCallerNumeric
import MicroCFTA.SourceSynthesisActualSelectedProgramFootprints
import MicroCFTA.SourceCurrentClassPositionalFootprints
import MicroCFTA.SourceSynthesisSelectedProgramFootprints

/-!
# Program footprints from actual shared scan reads

The precheck supplies coherent original records. Actual shared scan reads
select only those records. Source occurrence equations place their paths
inside Type fields. No retained-record certificate or future role is supplied.
These laws do not prove scan completion or failure-prefix preservation.
-/
namespace MicroCFTA.SourceSynthesisActualSharedSelectedProgramFootprints
open EqualityNormalize InternedConstructorTemplates SourceEqualityClassOrder
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression application ofType)
open SourceSynthesisGuardRegions SourceSynthesisRequiredFootprints
open SourceEqualityNeeded (Needed)
open SourceCurrentAllocatedPrecheck (Receipt)
open SourceSynthesisActualSelectedProgramFootprints (precheck_regions)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value

variable {width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
variable {guard : Guard} {loaded : Allocated} {inherited own : EqValue} {before : Checked width}
variable {records : List Record}

variable [DecidableEq Node]
variable {budget : Nat} {values : List Node} {kept : List Record}
variable {fourth savedFourth : SourceCurrentEmptinessMemo.Memo}
variable {outcome : Option Class} {scanned : Checked width}
variable {memos final : EndpointMemoGateTrace.Memos}

private theorem scan_sublist {start finish : Checked width}
    {initialMemo finalMemo : SourceCurrentEmptinessMemo.Memo}
    {initialMemos finalMemos : EndpointMemoGateTrace.Memos}
    (actual : SourceCurrentSharedScanCallerNumeric.ScanReads budget values records
      start initialMemo outcome kept finish finalMemo initialMemos finalMemos) :
    kept.Sublist records := by
  induction actual with
  | nil => exact .slnil
  | selected first tail ih => exact .cons_cons _ ih
  | skipped first second tail ih => exact .cons _ ih
  | continued first second seeded called callRead tail ih => exact .cons _ ih
  | stopped => exact List.nil_sublist _

/-- Every record returned by the actual scan retains its original coherent paths. -/
theorem selected_regions
    (receipt : Receipt formulas solver inventory guard loaded inherited before own (.classes records))
    (actual : SourceCurrentSharedScanCallerNumeric.ScanReads budget values records
      (SourceCurrentAllocatedPrecheck.state before loaded inherited) fourth
      outcome kept scanned savedFourth memos final)
    (region : Path → Prop)
    (endpoints : ∀ path ∈ members ((SourceCompactGuards.sourceEqualities guard).getD []), region path) :
    ∀ record ∈ kept, Coherent record ∧ ∀ path ∈ record.paths, region path := by
  intro record member
  exact precheck_regions receipt region endpoints record
    ((scan_sublist actual).subset member)

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] in
private theorem source_signed_disjoint (path target : Path)
    (excluded : ¬ path.IsPrefix target ∧ ¬ target.IsPrefix path) :
    SourceEqualityEditCompiledPaths.Disjoint (path.map Int.ofNat) (target.map Int.ofNat) :=
  ⟨fun initial => excluded.1 ((SourceEqualityClassEdits.signed_prefix path target).mp initial),
    fun initial => excluded.2 ((SourceEqualityClassEdits.signed_prefix target path).mp initial)⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] in
private theorem members_within (region : Path → Prop)
    (inputs : ∀ record ∈ kept, Coherent record ∧ ∀ path ∈ record.paths, region path) :
    ∀ path ∈ members (kept.map Record.paths), region path := by
  intro path member
  obtain ⟨paths, present, included⟩ := (mem_members _ _).mp member
  obtain ⟨record, retained, rfl⟩ := List.mem_map.mp present
  exact (inputs record retained).2 path included

/-- An actual application scan leaves each non-annotation program child unselected. -/
theorem application_footprint (types function argument : Expression)
    (sourceName : String) (sourceChildren : List Expression)
    (occurrence : application types function argument = .node [.mk sourceName guard sourceChildren])
    (receipt : Receipt formulas solver inventory guard loaded inherited before own (.classes records))
    (actual : SourceCurrentSharedScanCallerNumeric.ScanReads budget values records
      (SourceCurrentAllocatedPrecheck.state before loaded inherited) fourth
      outcome kept scanned savedFourth memos final)
    {record : Record} (member : record ∈ kept)
    (forestIndex : Nat) (programSlot : forestIndex = 2 ∨ forestIndex = 3) :
    Coherent record ∧ ∀ childIndex, childIndex ≠ 0 →
      SourceCurrentClassPositionalFootprints.Unselected record forestIndex childIndex := by
  obtain ⟨coherent, paths⟩ := selected_regions receipt actual applicationRegion
    (application_guard_endpoints types function argument sourceName guard sourceChildren occurrence).2 record member
  refine ⟨coherent, ?_⟩
  intro childIndex nonzero path included
  have opposite : 0 ≠ childIndex := Ne.symm nonzero
  apply source_signed_disjoint path [forestIndex, childIndex]
  have inside := paths path included
  rcases programSlot with rfl | rfl
  · rcases inside with ⟨suffix, rfl⟩ | ⟨suffix, rfl⟩ | ⟨suffix, rfl⟩ | ⟨suffix, rfl⟩ <;>
      simp_all [List.cons_prefix_cons]
  · rcases inside with ⟨suffix, rfl⟩ | ⟨suffix, rfl⟩ | ⟨suffix, rfl⟩ | ⟨suffix, rfl⟩ <;>
      simp_all [List.cons_prefix_cons]

/-- An actual filter scan leaves each non-annotation program child unselected. -/
theorem filter_footprint (candidates goal : Expression)
    (sourceName : String) (sourceChildren : List Expression)
    (occurrence : ofType candidates goal = .node [.mk sourceName guard sourceChildren])
    (receipt : Receipt formulas solver inventory guard loaded inherited before own (.classes records))
    (actual : SourceCurrentSharedScanCallerNumeric.ScanReads budget values records
      (SourceCurrentAllocatedPrecheck.state before loaded inherited) fourth
      outcome kept scanned savedFourth memos final)
    {record : Record} (member : record ∈ kept) :
    Coherent record ∧ ∀ childIndex, childIndex ≠ 0 →
      SourceCurrentClassPositionalFootprints.Unselected record 1 childIndex := by
  obtain ⟨coherent, paths⟩ := selected_regions receipt actual filterRegion
    (filter_guard_endpoints candidates goal sourceName guard sourceChildren occurrence).2 record member
  refine ⟨coherent, ?_⟩
  intro childIndex nonzero path included
  have opposite : 0 ≠ childIndex := Ne.symm nonzero
  apply source_signed_disjoint path [1, childIndex]
  have inside := paths path included
  rcases inside with ⟨suffix, rfl⟩ | ⟨suffix, rfl⟩ <;> simp_all [List.cons_prefix_cons]

/-- An actual application scan compiles only annotation demands within each program slot. -/
theorem application_annotation_only (types function argument : Expression)
    (sourceName : String) (sourceChildren : List Expression)
    (occurrence : application types function argument = .node [.mk sourceName guard sourceChildren])
    (receipt : Receipt formulas solver inventory guard loaded inherited before own (.classes records))
    (actual : SourceCurrentSharedScanCallerNumeric.ScanReads budget values records
      (SourceCurrentAllocatedPrecheck.state before loaded inherited) fourth
      outcome kept scanned savedFourth memos final)
    {entries childEntries : List (Int × Needed)}
    (built : SourceEqualityNeeded.build
      (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) = .node entries)
    (forestIndex : Nat) (programSlot : forestIndex = 2 ∨ forestIndex = 3)
    (found : SourceEqualityNeededMap.lookup (forestIndex : Int) entries = some (.node childEntries)) :
    ∀ index : Nat, index ≠ 0 → SourceEqualityNeededMap.lookup (index : Int) childEntries = none := by
  have within := members_within applicationRegion (selected_regions receipt actual applicationRegion
    (application_guard_endpoints types function argument sourceName guard sourceChildren occurrence).2)
  intro index nonzero
  have excluded := application_unselected (kept.map Record.paths) within index nonzero built
  rcases programSlot with rfl | rfl
  · exact excluded.1 (.node childEntries) found childEntries rfl
  · exact excluded.2 (.node childEntries) found childEntries rfl

/-- An actual filter scan compiles only annotation demands within its program slot. -/
theorem filter_annotation_only (candidates goal : Expression)
    (sourceName : String) (sourceChildren : List Expression)
    (occurrence : ofType candidates goal = .node [.mk sourceName guard sourceChildren])
    (receipt : Receipt formulas solver inventory guard loaded inherited before own (.classes records))
    (actual : SourceCurrentSharedScanCallerNumeric.ScanReads budget values records
      (SourceCurrentAllocatedPrecheck.state before loaded inherited) fourth
      outcome kept scanned savedFourth memos final)
    {entries childEntries : List (Int × Needed)}
    (built : SourceEqualityNeeded.build
      (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) = .node entries)
    (found : SourceEqualityNeededMap.lookup (1 : Int) entries = some (.node childEntries)) :
    ∀ index : Nat, index ≠ 0 → SourceEqualityNeededMap.lookup (index : Int) childEntries = none := by
  have within := members_within filterRegion (selected_regions receipt actual filterRegion
    (filter_guard_endpoints candidates goal sourceName guard sourceChildren occurrence).2)
  intro index nonzero
  exact filter_unselected (kept.map Record.paths) within index nonzero built
    (.node childEntries) found childEntries rfl

end MicroCFTA.SourceSynthesisActualSharedSelectedProgramFootprints
