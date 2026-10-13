import MicroCFTA.SourceSizedDecidedTrim

/-!
# Exact reference order after selecting trim keys

A live transition from a trim key has all its children in the trim keys.
Every other transition has a structurally empty child. Such transitions
have no candidates at any size. Thus state selection preserves each row's
candidate list and every first-occurrence position.
-/

namespace MicroCFTA.SourceSizedDecidedOrder

open Language Productivity SourceSizedCandidates SourceSizedReference
open SourceSizedDecided SourceSizedDecidedTable SourceSizedDecidedTrim

/-- An edge with productive children makes its parent structurally productive. -/
theorem productive_edge (nodes : List State) (complete : ∀ state, state ∈ nodes)
    (A : Automaton State Symbol) (state : State) (edge : Edge State Symbol)
    (member : edge ∈ A state) (children : edge.children.all (productive nodes A) = true) :
    productive nodes A state = true := by
  obtain ⟨terms, accepted⟩ := all₂_witnesses (Accepts (eraseGuards A)) edge.children
    (fun child present => (productive_correct nodes complete A child).mp
      (List.all_eq_true.mp children child present))
  apply (productive_correct nodes complete A state).mpr
  exact ⟨.node edge.label terms, .node {edge with guard := fun _ => true} terms
    (List.mem_map.mpr ⟨edge, member, rfl⟩) accepted rfl⟩

/-- Every live child of an original transition from a trim key is also a trim key. -/
theorem trimKeys_live_children [DecidableEq State]
    (nodes : List State) (complete : ∀ state, state ∈ nodes)
    (A : Automaton State Symbol) (root state : State)
    (included : state ∈ trimKeys nodes A root) (edge : Edge State Symbol)
    (member : edge ∈ A state) (children : edge.children.all (productive nodes A) = true)
    (child : State) (present : child ∈ edge.children) : child ∈ trimKeys nodes A root := by
  have marked := productive_edge nodes complete A state edge member children
  have liveEdge : edge ∈ GraphTrim.live nodes A state := by
    simp [GraphTrim.live, marked, member, children]
  have reached : Reachable (successors (GraphTrim.live nodes A)) [root] state := by
    have condition := (List.mem_filter.mp included).2
    rcases (Bool.or_eq_true _ _).mp condition with initial | reached
    · have equal : state = root := of_decide_eq_true initial
      subst state
      exact .seed (by simp)
    · exact (reachClosure_correct nodes complete _ _ state).mp ((Bool.and_eq_true _ _).mp reached).2
  have childReached := reachable_child (GraphTrim.live nodes A) [root] reached liveEdge present
  have childMarked := List.all_eq_true.mp children child present
  have childBit := (reachClosure_correct nodes complete _ _ child).mpr childReached
  simp [trimKeys, complete child, childMarked, childBit]

/-- A structurally unproductive state has no class in any subgraph. -/
theorem unproductive_classes [DecidableEq Symbol]
    (nodes : List State) (complete : ∀ state, state ∈ nodes)
    (original part : Automaton State Symbol)
    (subset : ∀ state edge, edge ∈ part state → edge ∈ original state)
    (state : State) (empty : productive nodes original state ≠ true) (size : Nat) :
    classes part size state = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro term present
  have accepted := (mem_classes_iff part size state term).mp present
  have source := FTAValidation.accepts_transfer part original subset accepted.1
  exact empty ((productive_correct nodes complete original state).mpr
    ⟨term, eraseGuards_accepts original source⟩)

/-- Selecting trim states preserves the full ordered reference class at every retained state. -/
theorem selected_classes_eq [DecidableEq State] [DecidableEq Symbol]
    (nodes : List State) (complete : ∀ state, state ∈ nodes)
    (original ordered : Automaton State Symbol)
    (subset : ∀ state edge, edge ∈ ordered state → edge ∈ original state)
    (root : State) (size : Nat) (state : State)
    (included : state ∈ trimKeys nodes original root) :
    classes (selected (trimKeys nodes original root) ordered) size state = classes ordered size state := by
  induction size using Nat.strongRecOn generalizing state with
  | ind size ih =>
      cases size with
      | zero => simp [classes_zero]
      | succ remaining =>
          rw [classes_succ, classes_succ]
          have retained : selected (trimKeys nodes original root) ordered state = ordered state := by
            simp [selected, included]
          rw [retained]
          unfold classOf
          congr 1
          apply congrArg List.flatten
          apply List.map_congr_left
          intro edge member
          have sameCandidates :
              candidates (fun child size => classes (selected (trimKeys nodes original root) ordered) size child)
                  edge.label edge.children (remaining + 1) =
                candidates (fun child size => classes ordered size child) edge.label edge.children (remaining + 1) := by
            by_cases live : edge.children.all (productive nodes original) = true
            · apply candidates_congr_children
              intro child present childSize smaller
              exact ih childSize smaller child
                (trimKeys_live_children nodes complete original root state included edge
                  (subset state edge member) live child present)
            · obtain ⟨child, present, empty⟩ := List.all_eq_false.mp (Bool.eq_false_iff.mpr live)
              have originalEmpty := unproductive_classes nodes complete original ordered subset child empty
              have selectedSubset : ∀ state edge,
                  edge ∈ selected (trimKeys nodes original root) ordered state → edge ∈ original state := by
                intro state edge present
                unfold selected at present
                split at present
                · exact subset state edge present
                · simp at present
              have selectedEmpty := unproductive_classes nodes complete original
                (selected (trimKeys nodes original root) ordered) selectedSubset child empty
              rw [candidates_nil_of_child _ _ _ child present selectedEmpty,
                candidates_nil_of_child _ _ _ child present originalEmpty]
          rw [sameCandidates]

/-- Successful decided root classes equal the full original-row reference sequence. -/
theorem sizedUpTo_reference_order [DecidableEq State] [DecidableEq Symbol]
    (nodes : List State) (complete : ∀ state, state ∈ nodes)
    (original : Automaton State Symbol)
    (rows : State → List (Row State Symbol Constraint))
    (answer : Constraint × Term Symbol → Guards.Verdict)
    (holds : Constraint → Term Symbol → Bool)
    (rowOrder : ∀ state, (automaton rows holds state).Perm (original state))
    (adequate : SourceSizedDecidedFilter.Adequate answer (fun pair => holds pair.1 pair.2))
    (root : State) (bound : Nat) (output : Table State (Term Symbol))
    (success : sizedUpTo rows (trimKeys nodes original root) answer bound = .ok output)
    (size : Nat) :
    output root size = if size ≤ bound then classes (automaton rows holds) size root else [] := by
  have included := root_mem_trimKeys nodes complete original root
  rw [sizedUpTo_exact rows (trimKeys nodes original root) answer holds adequate bound output success root size]
  by_cases positive : 0 < size
  · simp only [included, positive, true_and]
    split
    · exact selected_classes_eq nodes complete original (automaton rows holds)
        (fun state edge present => (rowOrder state).mem_iff.mp present) root size root included
    · rfl
  · have zero : size = 0 := by omega
    subst size
    simp [classes_zero]

end MicroCFTA.SourceSizedDecidedOrder
