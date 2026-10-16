import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeProfileBody
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeProfileProducer

namespace MergeProfileBodyChecks
open MicroCFTA Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentMemoMergeGraph
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile
open SourceCurrentAllocatedFiniteOrdinaryMergeProfileBounds (envelope)
open SourceCurrentAllocatedFiniteOrdinaryMergeProfileCode
open MergedOrdinaryHeight (height edgeHeight edgesHeight childrenHeight)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

def fiveRows (first second third fourth fifth : Interned (EdgeKey Symbol Guard))
    (values : List (Value Symbol Guard)) : List (EdgeValue Symbol Guard) :=
  [.mk first values, .mk second values, .mk third values, .mk fourth values, .mk fifth values]

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
/-- Five literal rows choose the column branch before the singleton result is returned. -/
theorem five_row_threshold (top : Guard) (first second third fourth fifth : Interned (EdgeKey Symbol Guard))
    (values : List (Value Symbol Guard)) :
    group top (fiveRows first second third fourth fifth values) =
      .bind (large top (.mk first values)
        [.mk second values, .mk third values, .mk fourth values, .mk fifth values])
        (fun edge => .pure [edge]) := by
  simp [group, fiveRows]

/-- Arbitrary full guards and repeated child positions retain a fixed five-row column profile. -/
theorem five_row_columns (clear : Guard → Bool) (top : Guard)
    (first second third fourth fifth : Interned (EdgeKey Symbol Guard)) (values : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before (fiveRows first second third fourth fifth values))
    (arity bound : Nat) (profile : ChildrenShape 5 arity values)
    (count : values.length ≤ arity) (bounded : childrenHeight values ≤ bound) :
    Certified clear (group top (fiveRows first second third fourth fifth values)) before
      (fun heap outputs => outputs.length ≤ 5 ∧ ∀ edge ∈ outputs,
        EdgeResident heap edge ∧ EdgeShape (envelope 5 (bound + 1)) arity edge ∧ edgeHeight edge ≤ bound) := by
  have profiled : RowsShape 5 arity (fiveRows first second third fourth fifth values) := by
    simp only [fiveRows, RowsShape, EdgeShape]
    exact ⟨⟨count, profile⟩, ⟨count, profile⟩, ⟨count, profile⟩, ⟨count, profile⟩, ⟨count, profile⟩, True.intro⟩
  have heightBound : edgesHeight (fiveRows first second third fourth fifth values) ≤ bound := by
    simp only [fiveRows, edgesHeight, edgeHeight]
    exact Nat.max_le.mpr ⟨bounded, Nat.max_le.mpr ⟨bounded, Nat.max_le.mpr ⟨bounded,
      Nat.max_le.mpr ⟨bounded, Nat.max_le.mpr ⟨bounded, Nat.zero_le _⟩⟩⟩⟩⟩
  exact (SourceCurrentAllocatedFiniteOrdinaryMergeProfileBody.group_certified clear top
    (fiveRows first second third fourth fifth values) before semantic costs resident 5 arity bound profiled
    (by simp [fiveRows]) heightBound).mono (fun _ _ result =>
      ⟨by simpa only [fiveRows, List.length_cons, List.length_nil] using result.1,
        fun edge member => ⟨(result.2 edge member).1, (result.2 edge member).2⟩⟩)

/-- The full ordinary body derives its profile from the resident five-row input, without a body result. -/
theorem five_row_body (clear : Guard → Bool) (top : Guard)
    (entry : Interned InternedBinderProtocol.NodeKey)
    (first second third fourth fifth : Interned (EdgeKey Symbol Guard)) (values : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Available before (.node entry (fiveRows first second third fourth fifth values) 0 []))
    (arity bound : Nat) (profile : ChildrenShape 5 arity values)
    (count : values.length ≤ arity) (bounded : childrenHeight values ≤ bound) :
    Certified clear (body top (.node entry (fiveRows first second third fourth fifth values) 0 [])) before
      (fun _ output => NodeShape (envelope 5 (bound + 1)) arity output ∧ height output ≤ bound + 1) := by
  have profiled : NodeShape 5 arity (.node entry (fiveRows first second third fourth fifth values) 0 []) := by
    simp only [NodeShape, fiveRows, List.length_cons, List.length_nil, RowsShape, EdgeShape]
    exact ⟨Nat.le_refl _, ⟨count, profile⟩, ⟨count, profile⟩, ⟨count, profile⟩,
      ⟨count, profile⟩, ⟨count, profile⟩, True.intro⟩
  have heightBound : height (.node entry (fiveRows first second third fourth fifth values) 0 []) ≤ bound + 1 := by
    simp only [height, fiveRows, edgesHeight, edgeHeight]
    apply Nat.succ_le_succ
    exact Nat.max_le.mpr ⟨bounded, Nat.max_le.mpr ⟨bounded, Nat.max_le.mpr ⟨bounded,
      Nat.max_le.mpr ⟨bounded, Nat.max_le.mpr ⟨bounded, Nat.zero_le _⟩⟩⟩⟩⟩
  exact (SourceCurrentAllocatedFiniteOrdinaryMergeProfileBody.body_certified clear top _ before
    semantic costs available 5 arity profiled).mono (fun _ output result =>
      ⟨NodeShape.mono output result.1 (SourceCurrentAllocatedFiniteOrdinaryMergeProfileBounds.envelope_height_mono 5 heightBound)
        (Nat.le_refl _), Nat.le_trans result.2 heightBound⟩)

/-- Ordered recursive requests retain every original position and each child-relative height. -/
theorem ordered_children (clear : Guard → Bool) (values : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before values) (rows arity bound : Nat)
    (profile : ChildrenShape rows arity values) (bounded : childrenHeight values ≤ bound) :
    Certified clear (map Code.request values) before
      (fun heap outputs => Language.All₂ (fun original output => Available heap output ∧
        NodeShape (envelope rows bound) arity output ∧ height output ≤ height original) values outputs ∧
        outputs.length = values.length) := by
  have checked := map_certified clear Code.request (fun heap value => Available heap value)
    (fun heap original output => Available heap output ∧ NodeShape (envelope rows bound) arity output ∧ height output ≤ height original)
    (fun _ _ effect value ready => effect.keeps.available value ready)
    (fun _ _ effect _ output ready => ⟨effect.keeps.available output ready.1, ready.2⟩) values
    (fun value member heap _ _ ready => (request_certified clear value heap ready).mono
      (fun _ _ returned => ⟨returned.1.1,
        returned.2 rows arity bound (ChildrenShape.member values profile value member)
          ((MergedOrdinaryHeight.childrenHeight_le values bound).mp bounded value member)⟩))
    before semantic costs available
  exact checked.mono (fun _ _ related => ⟨related, related.length_eq.symm⟩)

/-- The empty selected-column case retains the actual ordinary union and request instructions. -/
theorem empty_column (clear : Guard → Bool) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) :
    retainedColumn ([] : List (Value Symbol Guard)) = .bind (.work (MergedOrdinaryHeight.ordinaryUnion [])) Code.request ∧
      Certified clear (column []) before
        (fun heap output => Available heap output ∧ NodeShape (envelope 0 1) 0 output ∧ height output ≤ 0) := by
  exact ⟨by rfl, SourceCurrentAllocatedFiniteOrdinaryMergeProfileBody.column_certified clear [] before semantic costs
    (fun _ member => by cases member) 0 0 0 True.intro (Nat.le_refl _) (Nat.le_refl _)⟩

/-- The same completed five-row body installs its own profile after all recursive calls are discharged. -/
theorem five_row_actual (clear : Guard → Bool) (top : Guard)
    (entry : Interned InternedBinderProtocol.NodeKey)
    (first second third fourth fifth : Interned (EdgeKey Symbol Guard)) (values : List (Value Symbol Guard))
    (before after : State Symbol Guard) (memo saved : Memo Symbol Guard) (output : Value Symbol Guard)
    (actual : Run clear top (body top (.node entry (fiveRows first second third fourth fifth values) 0 []))
      before memo output after saved)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (physical : SourceCurrentMemoMergeEffects.Stored before memo)
    (profiles : SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored memo)
    (available : Available before (.node entry (fiveRows first second third fourth fifth values) 0 []))
    (arity bound : Nat) (profile : ChildrenShape 5 arity values)
    (count : values.length ≤ arity) (bounded : childrenHeight values ≤ bound) :
    SourceCurrentMemoMergeEffects.Effect before after ∧
      SourceCurrentMemoMergeEffects.Stored after saved ∧
      SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored saved ∧
      NodeShape (envelope 5 (bound + 1)) arity output ∧ height output ≤ bound + 1 := by
  exact SourceCurrentAllocatedFiniteOrdinaryMergeProfileProducer.run_profile actual _ semantic costs physical profiles
    (five_row_body clear top entry first second third fourth fifth values before semantic costs available arity bound profile count bounded)

#print axioms five_row_threshold
#check @five_row_threshold
#print axioms five_row_columns
#check @five_row_columns
#print axioms five_row_body
#check @five_row_body
#print axioms ordered_children
#check @ordered_children
#print axioms empty_column
#check @empty_column
#print axioms five_row_actual
#check @five_row_actual
end MergeProfileBodyChecks
