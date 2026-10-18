import MicroCFTA.SourceCurrentRequiredPathFootprints
set_option linter.all true
set_option maxHeartbeats 1000000

namespace MicroCFTA.RequiredFootprintCheck
open SourceEqualityNeeded SourceEqualityNeededMap
private def first : SourceEqualityClassOrder.Record :=
  (SourceEqualityClassOrder.recordOf [[1,0],[0,0],[1,0]]).getD ⟨.empty,[]⟩
private def second : SourceEqualityClassOrder.Record :=
  (SourceEqualityClassOrder.recordOf [[1,2],[0,2]]).getD ⟨.empty,[]⟩
private def records := [first,second,first]
private def selectedPaths := SourceEqualitySelectedRequired.paths (records.map SourceEqualityClassOrder.Record.paths)
private def children : List (Int × Needed) := [(0,.node []),(2,.node [])]
private def entries : List (Int × Needed) := [(0,.node children),(1,.node children)]
private theorem first_paths : first.paths = [[0,0],[1,0]] := by cbv
private theorem second_paths : second.paths = [[0,2],[1,2]] := by cbv
private theorem first_unselected : SourceCurrentClassPositionalFootprints.Unselected first 1 1 := by
  intro path member
  rw [first_paths] at member
  rcases List.mem_cons.mp member with rfl | member
  · unfold SourceEqualityEditCompiledPaths.Disjoint; decide
  · rcases List.mem_cons.mp member with rfl | member
    · unfold SourceEqualityEditCompiledPaths.Disjoint; decide
    · cases member
private theorem second_unselected : SourceCurrentClassPositionalFootprints.Unselected second 1 1 := by
  intro path member
  rw [second_paths] at member
  rcases List.mem_cons.mp member with rfl | member
  · unfold SourceEqualityEditCompiledPaths.Disjoint; decide
  · rcases List.mem_cons.mp member with rfl | member
    · unfold SourceEqualityEditCompiledPaths.Disjoint; decide
    · cases member
private theorem all_unselected : ∀ record ∈ records,
    SourceCurrentClassPositionalFootprints.Unselected record 1 1 := by
  intro record member
  simp only [records,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact first_unselected
  · exact second_unselected
  · exact first_unselected
private theorem built : build selectedPaths = .node entries := by cbv
private theorem selected_unselected : SourceCurrentActualRequiredRowOrigins.Unselected entries 1 1 :=
  SourceCurrentRequiredPathFootprints.selected_records records 1 1 all_unselected built
private theorem selected_witness :
    records.length = 3 ∧ (records.map SourceEqualityClassOrder.Record.paths).flatten.length = 6 ∧
    selectedPaths = [[0,0],[0,2],[1,0],[1,2]] ∧ build selectedPaths = .node entries ∧
    SourceCurrentActualRequiredRowOrigins.Unselected entries 1 1 ∧
    lookup 1 entries = some (.node children) ∧ lookup 1 children = none ∧
    (lookup 0 children).isSome = true ∧ (lookup 2 children).isSome = true := by
  exact ⟨by cbv,by cbv,by cbv,built,selected_unselected,by rfl,by rfl,by rfl,by rfl⟩

/-- Duplicate selected records retain other live children and leave the excluded second child absent. -/
theorem duplicate_selected_child :
    records.length = 3 ∧ (records.map SourceEqualityClassOrder.Record.paths).flatten.length = 6 ∧
    selectedPaths = [[0,0],[0,2],[1,0],[1,2]] ∧ build selectedPaths = .node entries ∧
    SourceCurrentActualRequiredRowOrigins.Unselected entries 1 1 ∧
    lookup 1 entries = some (.node children) ∧ lookup 1 children = none ∧
    (lookup 0 children).isSome = true ∧ (lookup 2 children).isSome = true := selected_witness

private theorem first_absent : ∀ path ∈ first.paths, ¬ [Int.ofNat 2].IsPrefix (path.map Int.ofNat) := by
  intro path member
  rw [first_paths] at member
  rcases List.mem_cons.mp member with rfl | member
  · decide
  · rcases List.mem_cons.mp member with rfl | member
    · decide
    · cases member
private theorem second_absent : ∀ path ∈ second.paths, ¬ [Int.ofNat 2].IsPrefix (path.map Int.ofNat) := by
  intro path member
  rw [second_paths] at member
  rcases List.mem_cons.mp member with rfl | member
  · decide
  · rcases List.mem_cons.mp member with rfl | member
    · decide
    · cases member
private theorem all_absent : ∀ record ∈ records, ∀ path ∈ record.paths,
    ¬ [Int.ofNat 2].IsPrefix (path.map Int.ofNat) := by
  intro record member
  simp only [records,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact first_absent
  · exact second_absent
  · exact first_absent
private def rawPaths : List Path := [[-1,7],[0,2],[0],[0,2]]
private def rawEntries : List (Int × Needed) := [(-1,.node [(7,.node [])]),(0,.node [(2,.node [])])]
private theorem raw_built : build rawPaths = .node rawEntries := by cbv
private theorem raw_absent : lookup (2 : Int) rawEntries = none := by
  apply SourceCurrentRequiredPathFootprints.build_absent rawPaths 2 _ raw_built
  intro path member
  simp only [rawPaths,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> decide
private theorem raw_unselected : SourceCurrentActualRequiredRowOrigins.Unselected rawEntries 0 1 := by
  apply SourceCurrentRequiredPathFootprints.build_unselected rawPaths 0 1 _ raw_built
  intro path member
  simp only [rawPaths,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> decide
private theorem absent_witness :
    lookup (2 : Int) entries = none ∧ build rawPaths = .node rawEntries ∧
    lookup (2 : Int) rawEntries = none ∧
    SourceCurrentActualRequiredRowOrigins.Unselected rawEntries 0 1 ∧
    lookup (-1) rawEntries = some (.node [(7,.node [])]) := by
  exact ⟨SourceCurrentRequiredPathFootprints.selected_records_absent records 2 all_absent built,
    raw_built,raw_absent,raw_unselected,rfl⟩

/-- Root absence follows from source exclusions while negative keys and deeper ancestor requirements remain literal. -/
theorem absent_roots_with_signed_paths :
    lookup (2 : Int) entries = none ∧ build rawPaths = .node rawEntries ∧
    lookup (2 : Int) rawEntries = none ∧
    SourceCurrentActualRequiredRowOrigins.Unselected rawEntries 0 1 ∧
    lookup (-1) rawEntries = some (.node [(7,.node [])]) := absent_witness

end MicroCFTA.RequiredFootprintCheck

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.RequiredFootprintCheck.duplicate_selected_child
#print MicroCFTA.RequiredFootprintCheck.duplicate_selected_child
#print axioms MicroCFTA.RequiredFootprintCheck.duplicate_selected_child

#check @MicroCFTA.RequiredFootprintCheck.absent_roots_with_signed_paths
#print MicroCFTA.RequiredFootprintCheck.absent_roots_with_signed_paths
#print axioms MicroCFTA.RequiredFootprintCheck.absent_roots_with_signed_paths

