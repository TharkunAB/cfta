import MicroCFTA.SourceSynthesisHereditaryProgramFields

/-!
# Height at the source Program positions

The physical source layouts select the recursive Program positions.
An application uses children two and three. A filter uses child one.
A singleton annotation has no Program child. The measure ignores Type
fields, the application marker, identities, and cached metadata.

The measure is total on physical values. Its Program interpretation needs
the existing source layout certificate. It is not a Type progress measure.
-/
namespace MicroCFTA.SourceSynthesisProgramHeight
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open InternedNestedProvenance (Edges)
variable {Symbol Guard : Type}

mutual
/-- Measure ordinary Program height at the certified physical layouts. -/
def value : Value Symbol Guard → Nat
  | .node _ rows _ _ => 1 + edges rows
  | _ => 0
termination_by input => sizeOf input

/-- Select the recursive Program children of each source row layout. -/
def edge : EdgeValue Symbol Guard → Nat
  | .mk _ [_, _, function, argument] => max (value function) (value argument)
  | .mk _ [_, candidates] => value candidates
  | _ => 0
termination_by input => sizeOf input

/-- Take the largest recursive Program height among the ordered rows. -/
def edges : List (EdgeValue Symbol Guard) → Nat
  | [] => 0
  | first :: rest => max (edge first) (edges rest)
termination_by inputs => sizeOf inputs
end

/-- Every physical row has height at most the height of its row list. -/
theorem edge_mem_le (row : EdgeValue Symbol Guard) (rows : List (EdgeValue Symbol Guard))
    (member : row ∈ rows) : edge row ≤ edges rows := by
  induction rows with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with same | later
      · subst row
        simpa only [edges] using Nat.le_max_left (edge first) (edges rest)
      · simpa only [edges] using Nat.le_trans (ih later) (Nat.le_max_right (edge first) (edges rest))

/-- A common bound on complete rows bounds their maximum height. -/
theorem edges_le (rows : List (EdgeValue Symbol Guard)) (bound : Nat)
    (bounded : ∀ row ∈ rows, edge row ≤ bound) : edges rows ≤ bound := by
  induction rows with
  | nil => simpa only [edges] using Nat.zero_le bound
  | cons first rest ih =>
      simpa only [edges] using Nat.max_le.mpr
        ⟨bounded first List.mem_cons_self,
          ih (fun row member => bounded row (List.mem_cons_of_mem _ member))⟩

/-- Changes to child zero retain the complete Program height of a row. -/
theorem edge_same_tail (source result : EdgeValue Symbol Guard)
    (same : result.children.tail = source.children.tail) : edge result = edge source := by
  cases source with
  | mk original inputs =>
      cases result with
      | mk returned outputs =>
          cases inputs with
          | nil =>
              cases outputs with
              | nil => simp only [edge]
              | cons first rest =>
                  have empty : rest = [] := same
                  subst rest
                  simp only [edge]
          | cons first rest =>
              cases outputs with
              | nil =>
                  have empty : rest = [] := same.symm
                  subst rest
                  simp only [edge]
              | cons next remaining =>
                  have identical : remaining = rest := same
                  subst remaining
                  cases rest with
                  | nil => simp only [edge]
                  | cons second tail =>
                      cases tail with
                      | nil => simp only [edge]
                      | cons third suffix =>
                          cases suffix with
                          | nil => simp only [edge]
                          | cons fourth suffix => cases suffix <;> simp only [edge]

/-- Actual node normalization can remove rows and cannot increase their maximum. -/
theorem makeNode_le [DecidableEq (EdgeKey Symbol Guard)]
    (rows : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (resident : Edges state rows) :
    value (run (makeNode rows) state).1 ≤ 1 + edges rows := by
  have kept : Edges state (canonicalEdges (surviving rows)) :=
    fun row member => resident row (List.mem_filter.mp (canonicalEdges_member _ row member)).1
  have bounded : edges (canonicalEdges (surviving rows)) ≤ edges rows :=
    edges_le _ _ (fun row member => edge_mem_le row rows
      (List.mem_filter.mp (canonicalEdges_member _ row member)).1)
  unfold makeNode
  dsimp only
  split
  · simpa only [run, value] using Nat.zero_le (1 + edges rows)
  · rename_i first rest same
    obtain ⟨entry, readback⟩ := identifyNode_readback (first :: rest) state facts.coherent facts.linked
      (by simpa [InternedNestedProvenance.Edges, same] using kept)
    simp only [run, readback, identifyNode, value]
    simpa only [same] using Nat.add_le_add_left bounded 1

/-- Each actual application Program child has smaller height than its ordinary parent. -/
theorem application_descend (entry) (rows : List (EdgeValue Symbol Guard)) (depth free)
    (row : EdgeValue Symbol Guard) (member : row ∈ rows)
    (types marker function argument : Value Symbol Guard)
    (layout : row.children = [types, marker, function, argument]) :
    value function < value (.node entry rows depth free) ∧
      value argument < value (.node entry rows depth free) := by
  have height : edge row = max (value function) (value argument) := by
    cases row
    cases layout
    simp only [edge]
  have bounded := edge_mem_le row rows member
  rw [height] at bounded
  have first := Nat.le_max_left (value function) (value argument)
  have last := Nat.le_max_right (value function) (value argument)
  simp only [value]
  omega

/-- An actual filter Program child has smaller height than its ordinary parent. -/
theorem filter_descend (entry) (rows : List (EdgeValue Symbol Guard)) (depth free)
    (row : EdgeValue Symbol Guard) (member : row ∈ rows)
    (goal candidates : Value Symbol Guard) (layout : row.children = [goal, candidates]) :
    value candidates < value (.node entry rows depth free) := by
  have height : edge row = value candidates := by
    cases row
    cases layout
    simp only [edge]
  have bounded := edge_mem_le row rows member
  rw [height] at bounded
  simp only [value]
  omega

end MicroCFTA.SourceSynthesisProgramHeight
