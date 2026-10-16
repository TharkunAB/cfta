import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeBudgetBody
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeBudgetProducer

namespace MergeBudgetBodyChecks
open MicroCFTA Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Edges)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentMemoMergeGraph
open SourceCurrentMemoMergeEffects (EdgeReady)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile
open SourceCurrentAllocatedFiniteOrdinaryMergeBudgetCode
open SourceCurrentAllocatedFiniteOrdinaryMergeBudgetNumbers (nodeBudget edgeBudget)
open MergedOrdinaryHeight (height edgeHeight edgesHeight childrenHeight)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

def fiveRows (first second third fourth fifth : Interned (EdgeKey Symbol Guard))
    (values : List (Value Symbol Guard)) : List (EdgeValue Symbol Guard) :=
  [.mk first values, .mk second values, .mk third values, .mk fourth values, .mk fifth values]

/-- Five rows choose two column requests before the literal Top-row constructor. -/
theorem five_row_columns (clear : Guard → Bool) (top : Guard)
    (first second third fourth fifth : Interned (EdgeKey Symbol Guard)) (values : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before (fiveRows first second third fourth fifth values))
    (profile : ChildrenShape 5 2 values) (count : values.length = 2) (bounded : childrenHeight values ≤ 1) :
    Certified clear (group top (fiveRows first second third fourth fifth values)) before
      (fun after outputs => Budget before after 104 51 ∧ ∀ edge ∈ outputs, EdgeReady after edge) := by
  have profiled : RowsShape 5 2 (fiveRows first second third fourth fifth values) := by
    simp only [fiveRows, RowsShape, EdgeShape]
    exact ⟨⟨Nat.le_of_eq count, profile⟩, ⟨Nat.le_of_eq count, profile⟩, ⟨Nat.le_of_eq count, profile⟩,
      ⟨Nat.le_of_eq count, profile⟩, ⟨Nat.le_of_eq count, profile⟩, True.intro⟩
  have heightBound : edgesHeight (fiveRows first second third fourth fifth values) ≤ 1 := by
    simp only [fiveRows, edgesHeight, edgeHeight]
    exact Nat.max_le.mpr ⟨bounded, Nat.max_le.mpr ⟨bounded, Nat.max_le.mpr ⟨bounded,
      Nat.max_le.mpr ⟨bounded, Nat.max_le.mpr ⟨bounded, Nat.zero_le _⟩⟩⟩⟩⟩
  have checked : Certified clear (large top (.mk first values)
      [.mk second values, .mk third values, .mk fourth values, .mk fifth values]) before
      (fun after edge => Budget before after (2 * (1 + nodeBudget 25 2 1)) (1 + 2 * edgeBudget 25 2 1) ∧ EdgeReady after edge) :=
    SourceCurrentAllocatedFiniteOrdinaryMergeBudgetBody.large_certified clear top (.mk first values)
      [.mk second values, .mk third values, .mk fourth values, .mk fifth values] before semantic costs resident
      5 2 1 profiled (by simp) heightBound
  have source : group top (fiveRows first second third fourth fifth values) =
      .bind (large top (.mk first values) [.mk second values, .mk third values, .mk fourth values, .mk fifth values])
        (fun edge => .pure [edge]) := by simp [group, fiveRows]
  rw [source]
  apply bind_certified clear _ _ before (fun after edge => Budget before after 104 51 ∧ EdgeReady after edge) _
  · exact checked.mono (fun _ _ result => ⟨by simpa only [nodeBudget, edgeBudget] using result.1, result.2⟩)
  · intro edge _ _ ready
    exact ⟨ready.1, fun value member => (List.mem_singleton.mp member) ▸ ready.2⟩

/-- Ordinary selection has zero constructor cost at comparison fuel zero. -/
theorem ordinary_select_zero (clear : Guard → Bool) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (rows arity : Nat) (profile : ChildrenShape rows arity inputs) :
    SourceMergedSelection.select clear 0 inputs before = .done (distinctNodes inputs) before ∧ Budget before before 0 0 :=
  ⟨SourceCurrentAllocatedFiniteOrdinaryMergeSelection.select clear 0 inputs before profile, Budget.refl before⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
/-- The input-only recurrence includes both root construction and squared lower row limits. -/
theorem two_layer_numbers (rows arity : Nat) :
    nodeBudget rows arity 1 = 1 + rows * arity ∧ edgeBudget rows arity 1 = rows ∧
      nodeBudget 5 2 2 = 521 ∧ edgeBudget 5 2 2 = 255 := by
  simp [nodeBudget, edgeBudget]

/-- The same actual five-row body derives its Work trace and both final supplies. -/
theorem same_actual_body (clear : Guard → Bool) (top : Guard)
    (entry : Interned InternedBinderProtocol.NodeKey)
    (first second third fourth fifth : Interned (EdgeKey Symbol Guard)) (values : List (Value Symbol Guard))
    (before after : State Symbol Guard) (memo saved : Memo Symbol Guard) (output : Value Symbol Guard)
    (actual : Run clear top (body top (.node entry (fiveRows first second third fourth fifth values) 0 []))
      before memo output after saved)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (physical : SourceCurrentMemoMergeEffects.Stored before memo)
    (profiles : SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored memo)
    (available : Available before (.node entry (fiveRows first second third fourth fifth values) 0 []))
    (profile : ChildrenShape 5 2 values) (count : values.length = 2) (bounded : childrenHeight values ≤ 1) :
    SourceCurrentMemoMergeEffects.Effect before after ∧
      SourceCurrentMemoMergeEffects.Stored after saved ∧
      SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored saved ∧
      Budget before after 521 255 ∧ after.nodes.next ≤ before.nodes.next + 521 ∧ after.edges.next ≤ before.edges.next + 255 := by
  have profiled : NodeShape 5 2 (.node entry (fiveRows first second third fourth fifth values) 0 []) := by
    simp only [NodeShape, fiveRows, List.length_cons, List.length_nil, RowsShape, EdgeShape]
    exact ⟨Nat.le_refl _, ⟨Nat.le_of_eq count, profile⟩, ⟨Nat.le_of_eq count, profile⟩,
      ⟨Nat.le_of_eq count, profile⟩, ⟨Nat.le_of_eq count, profile⟩, ⟨Nat.le_of_eq count, profile⟩, True.intro⟩
  have heightBound : height (.node entry (fiveRows first second third fourth fifth values) 0 []) ≤ 2 := by
    simp only [height, fiveRows, edgesHeight, edgeHeight]
    apply Nat.succ_le_succ
    exact Nat.max_le.mpr ⟨bounded, Nat.max_le.mpr ⟨bounded, Nat.max_le.mpr ⟨bounded,
      Nat.max_le.mpr ⟨bounded, Nat.max_le.mpr ⟨bounded, Nat.zero_le _⟩⟩⟩⟩⟩
  obtain ⟨effect, physicalAfter, profilesAfter, budget⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryMergeBudgetProducer.run_budget actual _ semantic costs physical profiles
      (SourceCurrentAllocatedFiniteOrdinaryMergeBudgetBody.body_certified clear top _ before semantic costs available 5 2 profiled)
  have finalBudget : Budget before after 521 255 := by
    simpa only [nodeBudget, edgeBudget] using budget.mono
      (SourceCurrentAllocatedFiniteOrdinaryMergeBudgetNumbers.node_mono 5 2 heightBound)
      (SourceCurrentAllocatedFiniteOrdinaryMergeBudgetNumbers.edge_mono 5 2 heightBound)
  exact ⟨effect, physicalAfter, profilesAfter, finalBudget, finalBudget.next_le⟩

#print axioms five_row_columns
#check @five_row_columns
#print axioms ordinary_select_zero
#check @ordinary_select_zero
#print axioms two_layer_numbers
#check @two_layer_numbers
#print axioms same_actual_body
#check @same_actual_body
end MergeBudgetBodyChecks
