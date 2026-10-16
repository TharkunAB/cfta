import MicroCFTA.SourceCurrentConjunctionCompletionReads

/-!
# Physical conjunction tuples from completed edge reads

The list operators retain the source tuple order and every edge occurrence.
The tail operand lists precede the original head list in each tuple.
Residency refers to the same final heap of the chosen Exposures sequence.
That completed sequence does not specify Haskell lazy read demand.
-/
namespace MicroCFTA.SourceCurrentConjunctionTuples
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentConjunctionCompletionReads

/-- Source tuple filtering observes the symbol and child arity. -/
def shape (edge : EdgeValue Symbol Guard) : Symbol × Nat :=
  (edge.entry.key.symbol, edge.children.length)

/-- The source visits prior tuples first, then matching edges of this operand. -/
def extend [DecidableEq Symbol] (edges : List (EdgeValue Symbol Guard))
    (previous : List (List (EdgeValue Symbol Guard))) : List (List (EdgeValue Symbol Guard)) :=
  previous.flatMap fun tuple => match tuple with
    | [] => []
    | first :: _ => (edges.filter fun edge => decide (shape edge = shape first)).map (· :: tuple)

/-- Fold the tail edge lists over singleton edges of the original head. -/
def tuples [DecidableEq Symbol] : List (List (EdgeValue Symbol Guard)) → List (List (EdgeValue Symbol Guard))
  | [] => []
  | first :: rest => rest.foldr extend (first.map fun edge => [edge])

/-- Tuple components have one common source symbol and arity. -/
def Matching (tuple : List (EdgeValue Symbol Guard)) : Prop :=
  tuple.Pairwise (fun left right => shape left = shape right)

/-- Ordered tuple positions select literal edges of their corresponding operand lists. -/
def Chosen (rows : List (List (EdgeValue Symbol Guard))) (tuple : List (EdgeValue Symbol Guard)) : Prop :=
  All₂ (fun edge edges => edge ∈ edges) tuple rows ∧ Matching tuple

/-- A literal extension retains its selected edge, prior tuple, and source filter test. -/
theorem mem_extend [DecidableEq Symbol] (edges : List (EdgeValue Symbol Guard))
    (previous : List (List (EdgeValue Symbol Guard))) (tuple : List (EdgeValue Symbol Guard)) :
    tuple ∈ extend edges previous ↔
      ∃ edge first rest, tuple = edge :: first :: rest ∧ first :: rest ∈ previous ∧
        edge ∈ edges ∧ shape edge = shape first := by
  constructor
  · intro member
    obtain ⟨old, present, selected⟩ := List.mem_flatMap.mp member
    cases old with
    | nil => simp at selected
    | cons first rest =>
        obtain ⟨edge, included, rfl⟩ := List.mem_map.mp selected
        have checked := List.mem_filter.mp included
        exact ⟨edge, first, rest, rfl, present, checked.1, of_decide_eq_true checked.2⟩
  · rintro ⟨edge, first, rest, rfl, present, included, same⟩
    exact List.mem_flatMap.mpr ⟨first :: rest, present,
      List.mem_map.mpr ⟨edge, List.mem_filter.mpr ⟨included, decide_eq_true same⟩, rfl⟩⟩

private theorem extend_chosen [DecidableEq Symbol] (edges : List (EdgeValue Symbol Guard))
    (rows : List (List (EdgeValue Symbol Guard))) (previous : List (List (EdgeValue Symbol Guard)))
    (nonempty : rows ≠ []) (prior : ∀ tuple, tuple ∈ previous ↔ Chosen rows tuple)
    (tuple : List (EdgeValue Symbol Guard)) :
    tuple ∈ extend edges previous ↔ Chosen (edges :: rows) tuple := by
  constructor
  · intro member
    obtain ⟨edge, first, rest, rfl, previousIn, edgeIn, same⟩ := (mem_extend edges previous tuple).mp member
    obtain ⟨ordered, matched⟩ := (prior _).mp previousIn
    refine ⟨.cons edgeIn ordered, List.pairwise_cons.mpr ⟨?_, matched⟩⟩
    intro other included
    rcases List.mem_cons.mp included with rfl | included
    · exact same
    · exact same.trans ((List.pairwise_cons.mp matched).1 other included)
  · rintro ⟨ordered, matched⟩
    cases ordered with
    | cons edgeIn remaining =>
        rename_i edge tail
        cases tail with
        | nil => cases remaining; exact False.elim (nonempty rfl)
        | cons first rest =>
            exact (mem_extend edges previous _).mpr ⟨edge, first, rest, rfl,
              (prior _).mpr ⟨remaining, (List.pairwise_cons.mp matched).2⟩,
              edgeIn, (List.pairwise_cons.mp matched).1 first List.mem_cons_self⟩

private theorem seed_chosen (edges : List (EdgeValue Symbol Guard)) (tuple : List (EdgeValue Symbol Guard)) :
    tuple ∈ edges.map (fun edge => [edge]) ↔ Chosen [edges] tuple := by
  constructor
  · intro member
    obtain ⟨edge, included, rfl⟩ := List.mem_map.mp member
    exact ⟨.cons included .nil, by simp [Matching]⟩
  · rintro ⟨ordered, _⟩
    cases ordered with
    | cons included remaining =>
        cases remaining
        exact List.mem_map.mpr ⟨_, included, rfl⟩

private theorem fold_chosen [DecidableEq Symbol]
    (first : List (EdgeValue Symbol Guard)) (rest : List (List (EdgeValue Symbol Guard)))
    (tuple : List (EdgeValue Symbol Guard)) :
    tuple ∈ rest.foldr extend (first.map (fun edge => [edge])) ↔ Chosen (rest ++ [first]) tuple := by
  induction rest generalizing tuple with
  | nil => exact seed_chosen first tuple
  | cons edges rest ih =>
      apply extend_chosen edges (rest ++ [first]) _ (by simp)
      exact ih

/-- Exact tuple membership preserves original edge occurrences and the source rotation. -/
theorem tuples_mem [DecidableEq Symbol] (first : List (EdgeValue Symbol Guard))
    (rest : List (List (EdgeValue Symbol Guard))) (tuple : List (EdgeValue Symbol Guard)) :
    tuple ∈ tuples (first :: rest) ↔ Chosen (rest ++ [first]) tuple :=
  fold_chosen first rest tuple

/-- Every tuple has one literal selected edge per source operand, in rotated order. -/
theorem tuples_selection [DecidableEq Symbol] (first : List (EdgeValue Symbol Guard))
    (rest : List (List (EdgeValue Symbol Guard))) (tuple : List (EdgeValue Symbol Guard))
    (member : tuple ∈ tuples (first :: rest)) :
    All₂ (fun edge edges => edge ∈ edges) tuple (rest ++ [first]) :=
  ((tuples_mem first rest tuple).mp member).1

/-- Every source tuple has matching symbols and arities. -/
theorem tuples_matching [DecidableEq Symbol] (rows : List (List (EdgeValue Symbol Guard)))
    (tuple : List (EdgeValue Symbol Guard)) (member : tuple ∈ tuples rows) : Matching tuple := by
  cases rows with
  | nil => cases member
  | cons first rest => exact ((tuples_mem first rest tuple).mp member).2

/-- Empty operands produce no empty tuple, and every returned tuple is nonempty. -/
theorem tuples_nonempty [DecidableEq Symbol] (rows : List (List (EdgeValue Symbol Guard)))
    (tuple : List (EdgeValue Symbol Guard)) (member : tuple ∈ tuples rows) : tuple ≠ [] := by
  cases rows with
  | nil => cases member
  | cons first rest =>
      have length := (tuples_selection first rest tuple member).length_eq
      intro same
      simp only [same, List.length_nil, List.length_append, List.length_singleton] at length
      omega

private theorem selection_member {tuple : List (EdgeValue Symbol Guard)}
    {rows : List (List (EdgeValue Symbol Guard))}
    (selected : All₂ (fun edge edges => edge ∈ edges) tuple rows) :
    ∀ edge ∈ tuple, edge ∈ rows.flatten := by
  induction selected with
  | nil => simp
  | cons included remaining ih =>
      intro edge member
      rcases List.mem_cons.mp member with rfl | member
      · exact List.mem_flatten.mpr ⟨_, List.mem_cons_self, included⟩
      · obtain ⟨edges, rowIn, edgeIn⟩ := List.mem_flatten.mp (ih edge member)
        exact List.mem_flatten.mpr ⟨edges, List.mem_cons_of_mem _ rowIn, edgeIn⟩

/-- Every physical tuple component comes from a literal exposed edge-list occurrence. -/
theorem tuples_members [DecidableEq Symbol] (rows : List (List (EdgeValue Symbol Guard)))
    (tuple : List (EdgeValue Symbol Guard)) (member : tuple ∈ tuples rows) :
    ∀ edge ∈ tuple, edge ∈ rows.flatten := by
  cases rows with
  | nil => cases member
  | cons first rest =>
      intro edge included
      have selected := selection_member (tuples_selection first rest tuple member) edge included
      obtain ⟨edges, rowIn, edgeIn⟩ := List.mem_flatten.mp selected
      have original : edges ∈ first :: rest := by
        rcases List.mem_append.mp rowIn with tail | head
        · exact List.mem_cons_of_mem _ tail
        · exact List.mem_cons.mpr (Or.inl (List.mem_singleton.mp head))
      exact List.mem_flatten.mpr ⟨edges, original, edgeIn⟩

/-- Actual completed reads derive resident closed tuple fields at their same final heap. -/
theorem tuples_verified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) {values : List (Value Symbol Guard)} {before after : State Symbol Guard}
    {rows : List (List (EdgeValue Symbol Guard))} (actual : Exposures values before rows after)
    (semantic : SemanticReady before) (costs : InternedFreshOrdinaryCostHeap.Heap before)
    (fields : SourceEqualityAnnotationHeap.Heap annotation before) (available : Values before values)
    (closed : ClosedValues values) (tuple : List (EdgeValue Symbol Guard)) (member : tuple ∈ tuples rows) :
    Effects annotation before after ∧ Edges after tuple ∧ ClosedEdges tuple := by
  have checked := actual.verified annotation semantic costs fields available closed
  refine ⟨checked.1, ?_, ?_⟩
  · intro edge included
    obtain ⟨edges, rowIn, edgeIn⟩ := List.mem_flatten.mp (tuples_members rows tuple member edge included)
    exact (checked.2 edges rowIn).1 edge edgeIn
  · intro edge included
    obtain ⟨edges, rowIn, edgeIn⟩ := List.mem_flatten.mp (tuples_members rows tuple member edge included)
    exact (checked.2 edges rowIn).2 edge edgeIn

end MicroCFTA.SourceCurrentConjunctionTuples
