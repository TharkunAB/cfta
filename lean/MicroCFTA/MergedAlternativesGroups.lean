import MicroCFTA.Language

/-!
# Language coverage of merged alternative groups

The source groups edges by symbol and arity. Singleton groups retain their
guard. Larger groups use an unconstrained edge and the union of each child
column. The recursive child calls have explicit language-coverage premises.
This proves one group operation; it does not assume that the source recursion
terminates or that physical interning has this semantic interpretation.
-/
namespace MicroCFTA.MergedAlternativesGroups
open Language

/-- The first `arity` columns of the child rows. Equal arities give source transpose. -/
def columns (rows : List (List Node)) : Nat → List (List Node)
  | 0 => []
  | arity + 1 => rows.filterMap List.head? :: columns (rows.map List.tail) arity

/-- Every accepted input row survives in the union of its child columns. -/
theorem columns_cover (meaning : Node → Value → Prop) (rows : List (List Node))
    (row : List Node) (values : List Value) (member : row ∈ rows)
    (accepted : All₂ meaning row values) :
    All₂ (fun choices value => ∃ node ∈ choices, meaning node value)
      (columns rows row.length) values := by
  induction accepted generalizing rows with
  | nil => exact .nil
  | @cons node value row values head tail ih =>
      apply All₂.cons
      · exact ⟨node, List.mem_filterMap.mpr ⟨node :: row, member, rfl⟩, head⟩
      · exact ih (rows.map List.tail) (List.mem_map.mpr ⟨node :: row, member, rfl⟩)

/-- Map related entries while preserving their accepted values. -/
theorem all₂_map (relation : A → Value → Prop) (meaning : B → Value → Prop)
    (map : A → B) (preserves : ∀ a value, relation a value → meaning (map a) value)
    (entries : List A) (values : List Value) (accepted : All₂ relation entries values) :
    All₂ meaning (entries.map map) values := by
  induction accepted with
  | nil => exact .nil
  | cons head tail ih => exact .cons (preserves _ _ head) ih

/-- One edge accepts its complete term through its child languages and guard. -/
def EdgeAccepts (meaning : Node → Term Symbol → Prop) (edge : Edge Node Symbol)
    (term : Term Symbol) : Prop :=
  ∃ children, term = .node edge.label children ∧
    All₂ meaning edge.children children ∧ edge.guard term = true

/-- The source singleton and multi-edge group branches. -/
def mergeGroup (merge : Node → Node) (mergeUnion : List Node → Node) :
    List (Edge Node Symbol) → Option (Edge Node Symbol)
  | [] => none
  | [edge] => some {edge with children := edge.children.map merge}
  | edge :: second :: rest => some {
      label := edge.label
      children := (columns ((edge :: second :: rest).map Edge.children) edge.children.length).map mergeUnion
      guard := fun _ => true}

/-- Matching the source group key means equal labels and equal numbers of children. -/
def SameKey (edges : List (Edge Node Symbol)) : Prop :=
  ∀ first ∈ edges, ∀ second ∈ edges,
    first.label = second.label ∧ first.children.length = second.children.length

/-- Both source group branches retain every original accepted term. -/
theorem mergeGroup_covers (meaning : Node → Term Symbol → Prop)
    (merge : Node → Node) (mergeUnion : List Node → Node)
    (mergeCovers : ∀ node term, meaning node term → meaning (merge node) term)
    (unionCovers : ∀ nodes node, node ∈ nodes → ∀ term, meaning node term → meaning (mergeUnion nodes) term)
    (edges : List (Edge Node Symbol)) (sameKey : SameKey edges)
    (original : Edge Node Symbol) (member : original ∈ edges)
    (term : Term Symbol) (accepted : EdgeAccepts meaning original term) :
    ∃ result, mergeGroup merge mergeUnion edges = some result ∧ EdgeAccepts meaning result term := by
  cases edges with
  | nil => simp at member
  | cons first rest =>
      cases rest with
      | nil =>
          have equal : original = first := by simpa using member
          subst original
          obtain ⟨children, termEqual, childRuns, guard⟩ := accepted
          refine ⟨_, rfl, children, termEqual, ?_, guard⟩
          exact all₂_map meaning meaning merge mergeCovers first.children children childRuns
      | cons second rest =>
          obtain ⟨children, termEqual, childRuns, guard⟩ := accepted
          obtain ⟨label, arity⟩ := sameKey original member first (by simp)
          refine ⟨_, rfl, children, ?_, ?_, rfl⟩
          · simpa only [label] using termEqual
          · have covered := columns_cover meaning
              ((first :: second :: rest).map Edge.children) original.children children
              (List.mem_map.mpr ⟨original, member, rfl⟩) childRuns
            rw [arity] at covered
            exact all₂_map _ meaning mergeUnion (fun nodes term accepted => by
              obtain ⟨node, member, accepted⟩ := accepted
              exact unionCovers nodes node member term accepted) _ children covered

/-- Distinct guarded nullary alternatives can reject a term that their merged edge accepts. -/
theorem nullary_guard_widening :
    let first : Edge Unit Unit := ⟨(), [], fun _ => false⟩
    let second : Edge Unit Unit := ⟨(), [], fun | .node _ children => !children.isEmpty⟩
    let term : Term Unit := .node () []
    first ≠ second ∧ ¬EdgeAccepts (fun _ _ => True) first term ∧
    ¬EdgeAccepts (fun _ _ => True) second term ∧
    ∃ result, mergeGroup id (fun _ => ()) [first, second] = some result ∧
      EdgeAccepts (fun _ _ => True) result term := by
  refine ⟨?_, ?_, ?_, _, rfl, [], rfl, .nil, rfl⟩
  · intro same
    have impossible : false = true := congrArg
      (fun edge : Edge Unit Unit => edge.guard (.node () [.node () []])) same
    cases impossible
  · simp [EdgeAccepts]
  · simp [EdgeAccepts]

end MicroCFTA.MergedAlternativesGroups
