import MicroCFTA.InternedValueMassHeap
import MicroCFTA.MergedNodeRowBounds

/-!
# Actual constructor mass bounds

Literal constructor inputs bound each new candidate. The causal store law
bounds every earlier winner. Row canonicalization and union normalization
do not increase the input list mass. Root self-reference filtering retains
the same store bound when its input already fits that bound.
-/
namespace MicroCFTA.InternedValueMassConstructors
open Cache InternedConstructorTemplates InternedValueMassHeap
variable {Symbol Guard : Type} {bound : Nat}

private theorem subset_sum {Item : Type} (measure : Item → Nat) (first last : List Item)
    (distinct : first.Nodup) (included : ∀ item ∈ first, item ∈ last) :
    (first.map measure).sum ≤ (last.map measure).sum := by
  induction first generalizing last with
  | nil => simp
  | cons head rest ih =>
    obtain ⟨earlier, suffix, rfl⟩ := List.mem_iff_append.mp (included head List.mem_cons_self)
    obtain ⟨absent, tailDistinct⟩ := List.nodup_cons.mp distinct
    have tailIncluded : ∀ item ∈ rest, item ∈ earlier ++ suffix := by
      intro item member
      have present := included item (List.mem_cons_of_mem head member)
      rcases List.mem_append.mp present with before | later
      · exact List.mem_append.mpr (.inl before)
      · rcases List.mem_cons.mp later with rfl | after
        · exact False.elim (absent member)
        · exact List.mem_append.mpr (.inr after)
    have lower := ih (earlier ++ suffix) tailDistinct tailIncluded
    simp only [List.map_cons, List.sum_cons, List.map_append, List.sum_append] at lower ⊢
    omega

/-- Sorting and identity deduplication cannot increase the literal row mass. -/
theorem canonical_edges_le (rows : List (EdgeValue Symbol Guard)) :
    InternedValueMass.edges (canonicalEdges rows) ≤ InternedValueMass.edges rows := by
  have distinct := MergedNodeRowBounds.canonical_nodup rows
  have included := InternedProbeProvenance.canonicalEdges_member rows
  have length := List.Nodup.length_le_of_subset distinct included
  have mass := subset_sum InternedValueMass.edge _ _ distinct included
  rw [InternedValueMass.edges_eq_length_sum, InternedValueMass.edges_eq_length_sum]
  omega

/-- Empty-child removal and canonical ordering cannot increase the literal row mass. -/
theorem normalized_edges_le (rows : List (EdgeValue Symbol Guard)) :
    InternedValueMass.edges (canonicalEdges (surviving rows)) ≤ InternedValueMass.edges rows :=
  Nat.le_trans (canonical_edges_le (surviving rows)) (InternedValueMass.edges_filter _ rows)

/-- Flattening explicit union alternatives cannot increase the containing list mass. -/
theorem flattened_values_le (nodes : List (Value Symbol Guard)) :
    InternedValueMass.values (nodes.flatMap unionMembers) ≤ InternedValueMass.values nodes := by
  induction nodes with
  | nil => exact Nat.le_refl _
  | cons first rest ih =>
    have own : InternedValueMass.values (unionMembers first) ≤ 1 + InternedValueMass.value first := by
      cases first <;> simp only [unionMembers, InternedValueMass.values, InternedValueMass.value] <;> omega
    simp only [List.flatMap_cons, InternedValueMass.values_append, InternedValueMass.values]
    omega

/-- First-identity selection removes occurrences without increasing list mass. -/
theorem distinct_values_le (nodes : List (Value Symbol Guard)) :
    InternedValueMass.values (distinctNodes nodes) ≤ InternedValueMass.values nodes := by
  cases nodes with
  | nil => simp only [distinctNodes, InternedValueMass.values]; omega
  | cons first rest =>
    have lower := distinct_values_le (rest.filter (fun other => other.referenceOf != first.referenceOf))
    have removed := InternedValueMass.values_filter (fun other => other.referenceOf != first.referenceOf) rest
    simp only [distinctNodes, InternedValueMass.values]
    omega
termination_by nodes.length
decreasing_by
  have lower := List.length_filter_le (fun other => other.referenceOf != first.referenceOf) rest
  simp_wf
  omega

/-- The ordinary union path copies only the original row payloads. -/
theorem ordinary_edges_le (nodes : List (Value Symbol Guard)) (rows : List (EdgeValue Symbol Guard))
    (selected : ordinaryEdges nodes = some rows) :
    InternedValueMass.edges rows ≤ InternedValueMass.values nodes := by
  induction nodes generalizing rows with
  | nil => simp only [ordinaryEdges, Option.some.injEq] at selected; subst rows; simp only [InternedValueMass.values, InternedValueMass.edges]; omega
  | cons first rest ih =>
    cases first <;> simp only [ordinaryEdges] at selected <;> try contradiction
    rename_i entry firstRows level free
    cases found : ordinaryEdges rest with
    | none => simp only [found, Option.map_none] at selected; contradiction
    | some lastRows =>
      simp only [found, Option.map_some, Option.some.injEq] at selected
      subst rows
      have lower := ih lastRows found
      simp only [InternedValueMass.edges_append, InternedValueMass.values, InternedValueMass.value]
      omega

/-- Actual edge construction bounds its candidate and the exact keep-first result. -/
theorem edge [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (guard : Guard)
    (children : List (Value Symbol Guard)) (state : State Symbol Guard) (stored : Stored bound state) :
    Stored (max bound (1 + InternedValueMass.values children)) (run (makeEdge symbol guard children) state).2 ∧
      InternedValueMass.edge (run (makeEdge symbol guard children) state).1 ≤
        max bound (1 + InternedValueMass.values children) := by
  simpa only [makeEdge, run, InternedValueMass.edge] using
    edge_step ⟨symbol, children.map Value.referenceOf, guard⟩ (fun entry => .mk entry children) state stored
      (1 + InternedValueMass.values children) (fun _ => by simp only [InternedValueMass.edge]; omega)

/-- Actual node construction includes dead-row removal and canonical readback. -/
theorem node [DecidableEq (EdgeKey Symbol Guard)] (rows : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (stored : Stored bound state) :
    Stored (max bound (1 + InternedValueMass.edges rows)) (run (makeNode rows) state).2 ∧
      InternedValueMass.value (run (makeNode rows) state).1 ≤ max bound (1 + InternedValueMass.edges rows) := by
  have normalized := normalized_edges_le rows
  unfold makeNode
  dsimp only
  split
  · exact ⟨stored.mono (Nat.le_max_left _ _), by
      simp only [run, InternedValueMass.value]
      exact Nat.le_trans stored.positive (Nat.le_max_left _ _)⟩
  · rename_i first rest selected
    have bounded := node_step (.node ((first :: rest).map (fun edge => edge.entry.identity)))
      (identifyNode (first :: rest)) state stored (1 + InternedValueMass.edges rows) (by
        intro entry
        simp only [identifyNode, InternedValueMass.value]
        rw [selected] at normalized
        omega)
    exact bounded

/-- Actual union construction bounds flattening, deduplication, and both constructor paths. -/
theorem union [DecidableEq (EdgeKey Symbol Guard)] (nodes : List (Value Symbol Guard))
    (state : State Symbol Guard) (stored : Stored bound state) :
    Stored (max bound (1 + InternedValueMass.values nodes)) (run (makeUnion nodes) state).2 ∧
      InternedValueMass.value (run (makeUnion nodes) state).1 ≤ max bound (1 + InternedValueMass.values nodes) := by
  have selectedBound := Nat.le_trans (distinct_values_le (nodes.flatMap unionMembers)) (flattened_values_le nodes)
  unfold makeUnion
  generalize selected : distinctNodes (nodes.flatMap unionMembers) = members at *
  cases members with
  | nil =>
    exact ⟨stored.mono (Nat.le_max_left _ _), by
      simp only [run, InternedValueMass.value]
      exact Nat.le_trans stored.positive (Nat.le_max_left _ _)⟩
  | cons first rest =>
    cases rest with
    | nil =>
      simp only [InternedValueMass.values] at selectedBound
      refine ⟨stored.mono (Nat.le_max_left _ _), ?_⟩
      simp only [run]
      exact Nat.le_trans (by omega) (Nat.le_max_right _ _)
    | cons second tail =>
      dsimp only
      split
      · rename_i rows ordinary
        have rowsBound := Nat.le_trans (ordinary_edges_le (first :: second :: tail) rows ordinary) selectedBound
        have made := node rows state stored
        have increase : max bound (1 + InternedValueMass.edges rows) ≤
            max bound (1 + InternedValueMass.values nodes) := Nat.max_le_max (Nat.le_refl _) (by omega)
        exact ⟨made.1.mono increase, Nat.le_trans made.2 increase⟩
      · exact node_step (.union ((first :: second :: tail).map Value.referenceOf))
          (fun entry => .union entry (first :: second :: tail)
            (maximumDepth (first :: second :: tail)) (childFree (first :: second :: tail))) state stored
          (1 + InternedValueMass.values nodes) (fun _ => by simp only [InternedValueMass.value]; omega)

/-- Pure smart cleanup can only remove payload constructors. -/
theorem cleanup_le (node : Value Symbol Guard) : InternedValueMass.value (cleanup node) ≤ InternedValueMass.value node := by
  cases node <;> simp only [cleanup] <;> try exact Nat.le_refl _
  case mu entry body depth ordinary =>
    split
    · simp only [InternedValueMass.value]; omega
    · split
      · simp only [InternedValueMass.value]; omega
      · exact Nat.le_refl _

/-- Root self-reference filtering retains the same bound as its actual input. -/
theorem filter [DecidableEq (EdgeKey Symbol Guard)] (name : InternedBinderProtocol.Reference)
    (node : Value Symbol Guard) (state : State Symbol Guard) (stored : Stored bound state)
    (input : InternedValueMass.value node ≤ bound) :
    Stored bound (run (withoutSelfReference name node) state).2 ∧
      InternedValueMass.value (run (withoutSelfReference name node) state).1 ≤ bound := by
  cases node <;> simp only [withoutSelfReference] <;> try exact ⟨stored, input⟩
  case union entry members level free =>
    split
    · have removed := InternedValueMass.values_filter (fun member => member.referenceOf != .ref name) members
      have candidate : 1 + InternedValueMass.values (members.filter (fun member => member.referenceOf != .ref name)) ≤ bound := by
        simp only [InternedValueMass.value] at input
        omega
      have actual := union (members.filter (fun member => member.referenceOf != .ref name)) state stored
      simpa only [Nat.max_eq_left candidate] using actual
    · exact ⟨stored, input⟩

end MicroCFTA.InternedValueMassConstructors
