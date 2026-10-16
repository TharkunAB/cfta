import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOutputConstructors
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeCode

/-!
# Height-indexed profile bounds for merge columns

A column union can contain rows from every original group member.
The envelope permits this larger recursive input at the next lower height.
The constructor laws refer to the actual returned records and heap.
These laws do not assert a completed recursive merge call.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeProfileBounds
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open MergedOrdinaryHeight (height edgeHeight edgesHeight childrenHeight ordinaryUnion)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile
variable {Symbol Guard : Type}

/-- Each lower column level permits the square of the previous row limit. -/
def envelope (rows : Nat) : Nat → Nat
  | 0 => rows
  | bound + 1 => max rows (envelope (rows * rows) bound)

/-- The output envelope always contains the original row limit. -/
theorem rows_le_envelope (rows bound : Nat) : rows ≤ envelope rows bound := by
  cases bound with
  | zero => exact Nat.le_refl _
  | succ bound => exact Nat.le_max_left _ _

/-- Increasing the original row limit increases every height-indexed envelope. -/
theorem envelope_rows_mono (bound : Nat) {first last : Nat} (enough : first ≤ last) :
    envelope first bound ≤ envelope last bound := by
  induction bound generalizing first last with
  | zero => exact enough
  | succ bound ih => exact Nat.max_le.mpr ⟨Nat.le_trans enough (Nat.le_max_left _ _),
      Nat.le_trans (ih (Nat.mul_le_mul enough enough)) (Nat.le_max_right _ _)⟩

/-- One more layer permits all previous recursive row envelopes. -/
theorem envelope_succ (rows bound : Nat) : envelope rows bound ≤ envelope rows (bound + 1) :=
  Nat.le_trans (envelope_rows_mono bound (Nat.le_mul_self rows)) (Nat.le_max_right _ _)

/-- Increasing the height limit retains every earlier output envelope. -/
theorem envelope_height_mono (rows : Nat) {first last : Nat} (enough : first ≤ last) :
    envelope rows first ≤ envelope rows last := by
  induction enough with
  | refl => exact Nat.le_refl _
  | @step last _ ih => exact Nat.le_trans ih (envelope_succ rows last)

/-- A recursively merged column with squared input rows fits the parent envelope. -/
theorem column_envelope (rows bound : Nat) :
    envelope (rows * rows) bound ≤ envelope rows (bound + 1) := Nat.le_max_right _ _

/-- Flattening original ordinary alternatives preserves every complete row profile. -/
theorem union_rows (values : List (Value Symbol Guard)) (rows arity : Nat)
    (profile : ChildrenShape rows arity values) :
    RowsShape rows arity (values.flatMap nodeEdges) := by
  apply SourceCurrentAllocatedFiniteOrdinaryOutputConstructors.rows_of_members
  intro edge member
  obtain ⟨value, present, included⟩ := List.mem_flatMap.mp member
  exact RowsShape.member _ (NodeShape.nodeEdges value (ChildrenShape.member values profile value present)) edge included

/-- An ordinary union has at most one input row limit per original operand. -/
theorem union_rows_length (values : List (Value Symbol Guard)) (rows arity : Nat)
    (profile : ChildrenShape rows arity values) :
    (values.flatMap nodeEdges).length ≤ values.length * rows := by
  induction values with
  | nil => simp
  | cons first rest ih =>
      simpa only [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm] using
        Nat.add_le_add (NodeShape.length first profile.1) (ih profile.2)

/-- The actual ordinary union retains arity and bounds its rows and height from its inputs. -/
theorem ordinary_union [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) (heap : State Symbol Guard)
    (coherent : InternedRecordCoherence.Coherent heap) (linked : InternedEdgeResidency.Linked heap)
    (available : ∀ value ∈ values, Available heap value) (rows arity : Nat)
    (profile : ChildrenShape rows arity values) :
    NodeShape (values.length * rows) arity (run (ordinaryUnion values) heap).1 ∧
      height (run (ordinaryUnion values) heap).1 ≤ childrenHeight values := by
  refine ⟨?_, MergedOrdinaryHeight.ordinaryUnion_bound values heap coherent linked
    (fun value member => (available value member).resident) (childrenHeight values)
    ((MergedOrdinaryHeight.childrenHeight_le values _).mp (Nat.le_refl _))⟩
  cases values with
  | nil => simp [ordinaryUnion, InternedConstructorTemplates.makeNode, surviving, canonicalEdges,
      EnumerationBuilderCaches.canonicalIds, run, NodeShape]
  | cons first rest =>
      apply SourceCurrentAllocatedFiniteOrdinaryOutputConstructors.makeNode _ heap coherent linked
      · intro edge member
        obtain ⟨value, present, included⟩ := List.mem_flatMap.mp member
        exact resident_edges heap linked value (available value present).resident edge included
      · exact RowsShape.mono _ (union_rows (first :: rest) rows arity profile)
          (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right rows (by simp : 1 ≤ (first :: rest).length)) (Nat.le_refl _)
      · exact union_rows_length (first :: rest) rows arity profile

/-- Every literal column contains at most one value from each source row. -/
theorem column_length (values : List (List Input)) (arity : Nat) (column : List Input)
    (member : column ∈ MergedAlternativesGroups.columns values arity) : column.length ≤ values.length := by
  induction arity generalizing values with
  | zero => cases member
  | succ arity ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact List.length_filterMap_le _ _
      · simpa only [List.length_map] using ih (values.map List.tail) later

/-- Column membership retains both its original profiles and its original multiplicity bound. -/
theorem column_inputs (edges : List (EdgeValue Symbol Guard)) (count rows arity : Nat)
    (profile : RowsShape rows arity edges) (column : List (Value Symbol Guard))
    (member : column ∈ MergedAlternativesGroups.columns (edges.map EdgeValue.children) count) :
    ChildrenShape rows arity column ∧ column.length ≤ edges.length := by
  refine ⟨SourceCurrentAllocatedFiniteOrdinaryOutputConstructors.children_of_members column ?_, ?_⟩
  · intro value included
    obtain ⟨children, present, inside⟩ := MergedPhysicalGroupEdges.columns_member _ _ column member value included
    obtain ⟨edge, original, rfl⟩ := List.mem_map.mp present
    exact ChildrenShape.member _ (EdgeShape.children edge (RowsShape.member edges profile edge original)) value inside
  · simpa only [List.length_map] using column_length (edges.map EdgeValue.children) count column member

/-- The actual union for a bounded source group has squared rows and no larger child height. -/
theorem column_union [DecidableEq (EdgeKey Symbol Guard)]
    (edges : List (EdgeValue Symbol Guard)) (count rows arity : Nat)
    (profile : RowsShape rows arity edges) (length : edges.length ≤ rows)
    (heap : State Symbol Guard) (coherent : InternedRecordCoherence.Coherent heap)
    (linked : InternedEdgeResidency.Linked heap) (cached : Cached heap)
    (resident : ∀ edge ∈ edges, EdgeResident heap edge) (column : List (Value Symbol Guard))
    (member : column ∈ MergedAlternativesGroups.columns (edges.map EdgeValue.children) count) :
    NodeShape (rows * rows) arity (run (ordinaryUnion column) heap).1 ∧
      height (run (ordinaryUnion column) heap).1 ≤ edgesHeight edges := by
  have inputs := column_inputs edges count rows arity profile column member
  have original (value : Value Symbol Guard) (included : value ∈ column) :
      ∃ edge ∈ edges, value ∈ edge.children := by
    obtain ⟨children, present, inside⟩ := MergedPhysicalGroupEdges.columns_member _ _ column member value included
    obtain ⟨edge, original, rfl⟩ := List.mem_map.mp present
    exact ⟨edge, original, inside⟩
  have available : ∀ value ∈ column, Available heap value := by
    intro value included
    obtain ⟨edge, present, inside⟩ := original value included
    exact cached.edges edge.entry.key edge (resident edge present) value inside
  have actual := ordinary_union column heap coherent linked available rows arity inputs.1
  refine ⟨NodeShape.mono _ actual.1 (Nat.mul_le_mul_right rows (Nat.le_trans inputs.2 length)) (Nat.le_refl _),
    Nat.le_trans actual.2 ?_⟩
  apply (MergedOrdinaryHeight.childrenHeight_le column _).mpr
  intro value included
  obtain ⟨edge, present, inside⟩ := original value included
  exact Nat.le_trans (SourceCurrentAllocatedFiniteOrdinaryDomain.child_le_edge edge value inside)
    ((MergedOrdinaryHeight.edgesHeight_le edges _).mp (Nat.le_refl _) edge present)

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeProfileBounds
