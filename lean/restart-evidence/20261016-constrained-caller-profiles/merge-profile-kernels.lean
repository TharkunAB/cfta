import MicroCFTA.SourceCurrentAllocatedMergeGraph
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeProfileSelection

namespace MergeProfileKernels
open MicroCFTA Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentMemoMergeGraph
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile
open SourceCurrentAllocatedFiniteOrdinaryMergeProfileBounds
open SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache
open MergedOrdinaryHeight (height edgesHeight ordinaryUnion)
variable {Symbol Guard : Type}

/-- A reentrant loser needs no certificate when the first completion already exists. -/
theorem first_winner_rejects_invalid_candidate (input : Value Symbol Guard) :
    let first := remember empty input .empty
    Stored first ∧
    remember first input (.reference (.uninterned 0)) = first ∧
    winner first input (.reference (.uninterned 0)) = ⟨input, .empty⟩ ∧
    ¬ Certificate (Value.empty : Value Symbol Guard) (.reference (.uninterned 0)) := by
  dsimp only
  have stored := remember_stored empty_stored input .empty (empty_certificate input)
  have found := (remember_absent empty input .empty rfl).1
  have preserved := winner_existing_certificate stored input (.reference (.uninterned 0)) ⟨input, .empty⟩ found
  refine ⟨stored, preserved.1, preserved.2.1, ?_⟩
  intro invalid
  have impossible := (invalid 0 0 0 True.intro (Nat.le_refl _)).1
  exact impossible

/-- A real warm hit uses its captured original and returns the identical heap and memo. -/
theorem warm_hit_profile [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (top : Guard) (heap : State Symbol Guard)
    (memo : Memo Symbol Guard) (input : Value Symbol Guard) (entry : Entry Symbol Guard)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady heap)
    (available : Available heap input) (physical : SourceCurrentMemoMergeEffects.Stored heap memo)
    (stored : Stored memo) (found : memo input.referenceOf = some entry)
    (rows arity bound : Nat) (profile : NodeShape rows arity input) (bounded : height input ≤ bound) :
    Call clear top input heap memo entry.result heap memo ∧ entry.original = input ∧
      NodeShape (envelope rows bound) arity entry.result ∧ height entry.result ≤ height input ∧
      SourceCurrentAllocatedFiniteOrdinaryMergeCache.Stored memo := by
  have result := hit_profile semantic available physical stored found rows arity bound profile bounded
  exact ⟨.hit found, result.1, result.2.1, result.2.2, stored.domain⟩

/-- The actual column union fits the parent envelope and strictly lowers ordinary height. -/
theorem column_actual_parent_bound [DecidableEq (EdgeKey Symbol Guard)]
    (edges : List (EdgeValue Symbol Guard)) (count rows arity : Nat)
    (profile : RowsShape rows arity edges) (length : edges.length ≤ rows)
    (heap : State Symbol Guard) (coherent : InternedRecordCoherence.Coherent heap)
    (linked : InternedEdgeResidency.Linked heap) (cached : InternedProbeProvenance.Cached heap)
    (resident : ∀ edge ∈ edges, InternedEdgeResidency.EdgeResident heap edge)
    (column : List (Value Symbol Guard))
    (member : column ∈ MergedAlternativesGroups.columns (edges.map EdgeValue.children) count)
    (entry : Interned InternedBinderProtocol.NodeKey) (depth : Nat)
    (free : List InternedBinderProtocol.Reference) :
    NodeShape (envelope rows (height (.node entry edges depth free))) arity
      (run (ordinaryUnion column) heap).1 ∧
      height (run (ordinaryUnion column) heap).1 < height (.node entry edges depth free) := by
  have actual := column_union edges count rows arity profile length heap coherent linked cached resident column member
  have envelopeBound := Nat.le_trans (rows_le_envelope (rows * rows) (edgesHeight edges))
    (column_envelope rows (edgesHeight edges))
  refine ⟨NodeShape.mono _ actual.1 (by simpa only [height] using envelopeBound) (Nat.le_refl _), ?_⟩
  simp only [height]
  exact Nat.lt_succ_of_le actual.2

/-- Actual selection keeps its source profile and excludes the recursive union branch. -/
theorem selection_then_retained_column [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (fuel : Nat) (inputs values : List (Value Symbol Guard))
    (before after : State Symbol Guard)
    (done : SourceMergedSelection.select clear fuel inputs before = .done values after)
    (rows arity : Nat) (profile : ChildrenShape rows arity inputs) :
    ChildrenShape rows arity values ∧ values.length ≤ inputs.length ∧
      retainedColumn values = match values with
        | [single] => .pure single
        | others => .bind (.work (ordinaryUnion others)) Code.request := by
  have selected := SourceCurrentAllocatedFiniteOrdinaryMergeProfileSelection.selected_profile
    clear fuel inputs values before after done rows arity profile
  refine ⟨selected.1, selected.2, ?_⟩
  have rule := SourceCurrentAllocatedFiniteOrdinaryMergeProfileSelection.retained_column values rows arity selected.1
  cases values with
  | nil => exact rule
  | cons first rest => cases rest with
    | nil => exact rule
    | cons second tail => exact rule

/-- The allocated group keeps its actual heap and memo when the count theorem is applied. -/
theorem allocated_group_multiplicity
    [DecidableEq (EdgeKey (SourceObservations.Label FullSyntax.Formula) (SourceSymbolicIndex.Constraint FullSyntax.Formula))]
    {clear : SourceSymbolicIndex.Constraint FullSyntax.Formula → Bool}
    {edges values : List (EdgeValue (SourceObservations.Label FullSyntax.Formula)
      (SourceSymbolicIndex.Constraint FullSyntax.Formula))}
    {before after : SourceCurrentAllocatedMergeGraph.State} {memo saved : SourceCurrentAllocatedMergeGraph.Memo}
    (actual : SourceCurrentAllocatedMergeGraph.Run clear (SourceCurrentAllocatedMergeGraph.group edges)
      before memo values after saved) :
    Run clear SourceCurrentAllocatedMergeGraph.top (group SourceCurrentAllocatedMergeGraph.top edges)
      before.heap memo values after.heap saved ∧ values.length ≤ edges.length := by
  have raw := actual.graph
  rw [SourceCurrentAllocatedMergeGraph.erase_group] at raw
  exact ⟨raw, SourceCurrentAllocatedFiniteOrdinaryMergeProfileSelection.group_length raw⟩

/-- Ordered allocated groups retain the source alternative bound before final node construction. -/
theorem allocated_groups_multiplicity
    [DecidableEq (EdgeKey (SourceObservations.Label FullSyntax.Formula) (SourceSymbolicIndex.Constraint FullSyntax.Formula))]
    {clear : SourceSymbolicIndex.Constraint FullSyntax.Formula → Bool}
    {groups values : List (List (EdgeValue (SourceObservations.Label FullSyntax.Formula)
      (SourceSymbolicIndex.Constraint FullSyntax.Formula)))}
    {before after : SourceCurrentAllocatedMergeGraph.State} {memo saved : SourceCurrentAllocatedMergeGraph.Memo}
    (actual : SourceCurrentAllocatedMergeGraph.Run clear
      (SourceCurrentAllocatedMergeGraph.map SourceCurrentAllocatedMergeGraph.group groups)
      before memo values after saved) (rows : Nat) (sourceBound : groups.flatten.length ≤ rows) :
    values.length = groups.length ∧ values.flatten.length ≤ rows := by
  have raw := actual.graph
  simp only [SourceCurrentAllocatedMergeGraph.erase_map, SourceCurrentAllocatedMergeGraph.erase_group] at raw
  exact ⟨SourceCurrentAllocatedFiniteOrdinaryMergeProfileSelection.map_length raw,
    Nat.le_trans (SourceCurrentAllocatedFiniteOrdinaryMergeProfileSelection.groups_length raw) sourceBound⟩

end MergeProfileKernels

#check @MergeProfileKernels.first_winner_rejects_invalid_candidate
#print axioms MergeProfileKernels.first_winner_rejects_invalid_candidate
#check @MergeProfileKernels.warm_hit_profile
#print axioms MergeProfileKernels.warm_hit_profile
#check @MergeProfileKernels.column_actual_parent_bound
#print axioms MergeProfileKernels.column_actual_parent_bound
#check @MergeProfileKernels.selection_then_retained_column
#print axioms MergeProfileKernels.selection_then_retained_column
#check @MergeProfileKernels.allocated_group_multiplicity
#print axioms MergeProfileKernels.allocated_group_multiplicity
#check @MergeProfileKernels.allocated_groups_multiplicity
#print axioms MergeProfileKernels.allocated_groups_multiplicity
