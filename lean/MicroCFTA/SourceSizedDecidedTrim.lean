import MicroCFTA.SourceSizedDecided
import MicroCFTA.GraphTrim

/-!
# The trimmed state inventory of the decided Sized worker

The source builds classes at the keys of the trimmed graph but retains the
original sorted rows. The selected graph therefore lies between the trimmed
graph and the original graph. This proves exact root-language preservation
without assuming that all original children belong to the trimmed inventory.
-/

namespace MicroCFTA.SourceSizedDecidedTrim

open Language Productivity SourceSizedDecided SourceSizedDecidedTable RecursiveSize

/-- The source trim keys retain the root even when its structural language is empty. -/
def trimKeys [DecidableEq State] (nodes : List State) (A : Automaton State Symbol)
    (root : State) : List State :=
  nodes.filter fun state => decide (state = root) ||
    (productive nodes A state && reachClosure nodes (successors (GraphTrim.live nodes A)) [root] state)

/-- The initial state always has a table entry in the source trimmed graph. -/
theorem root_mem_trimKeys [DecidableEq State] (nodes : List State)
    (complete : ∀ state, state ∈ nodes) (A : Automaton State Symbol) (root : State) :
    root ∈ trimKeys nodes A root := by
  simp [trimKeys, complete root]

/-- Every transition retained by trim is available in the decided selected graph. -/
theorem trim_subset_selected [DecidableEq State] (nodes : List State)
    (complete : ∀ state, state ∈ nodes) (A : Automaton State Symbol)
    (root state : State) (edge : Edge State Symbol)
    (present : edge ∈ GraphTrim.trim nodes A root state) :
    edge ∈ selected (trimKeys nodes A root) A state := by
  have original := GraphTrim.trim_subset nodes A root state edge present
  unfold GraphTrim.trim at present
  split at present
  next reached =>
    unfold GraphTrim.live at present
    split at present
    next productive =>
      have included : state ∈ trimKeys nodes A root := by
        simp [trimKeys, complete state, productive, reached]
      simpa [selected, included] using original
    next => simp at present
  next => simp at present

/-- Keeping original rows at trim keys does not remove or add any accepted root term. -/
theorem selected_exact [DecidableEq State] (nodes : List State)
    (complete : ∀ state, state ∈ nodes) (A : Automaton State Symbol)
    (root : State) (term : Term Symbol) :
    Accepts (selected (trimKeys nodes A root) A) root term ↔ Accepts A root term := by
  constructor
  · apply FTAValidation.accepts_transfer
    intro state edge present
    unfold selected at present
    split at present
    · exact present
    · simp at present
  · intro accepted
    have trimmed := (GraphTrim.trim_exact nodes complete A root term).mpr accepted
    exact FTAValidation.accepts_transfer _ _ (trim_subset_selected nodes complete A root) trimmed

/-- Sorting original rows preserves acceptance after selecting a common state inventory. -/
theorem selected_order_exact [DecidableEq State]
    (states : List State) (original ordered : Automaton State Symbol)
    (rowOrder : ∀ state, (ordered state).Perm (original state))
    (state : State) (term : Term Symbol) :
    Accepts (selected states ordered) state term ↔ Accepts (selected states original) state term := by
  have same : ∀ state edge, edge ∈ selected states ordered state ↔
      edge ∈ selected states original state := by
    intro state edge
    by_cases included : state ∈ states
    · simpa [selected, included] using (rowOrder state).mem_iff (a := edge)
    · simp [selected, included]
  exact ⟨FTAValidation.accepts_transfer _ _ (fun state edge present => (same state edge).mp present),
    FTAValidation.accepts_transfer _ _ (fun state edge present => (same state edge).mpr present)⟩

/-- Source trim keys and original sorted rows have the complete original root language. -/
theorem sorted_selected_exact [DecidableEq State] (nodes : List State)
    (complete : ∀ state, state ∈ nodes) (original ordered : Automaton State Symbol)
    (rowOrder : ∀ state, (ordered state).Perm (original state))
    (root : State) (term : Term Symbol) :
    Accepts (selected (trimKeys nodes original root) ordered) root term ↔
      Accepts original root term :=
  (selected_order_exact (trimKeys nodes original root) original ordered rowOrder root term).trans
    (selected_exact nodes complete original root term)

/-- A successful decided table contains exactly the original accepted terms up to its bound. -/
theorem sizedUpTo_original_iff [DecidableEq State] [DecidableEq Symbol]
    (nodes : List State) (complete : ∀ state, state ∈ nodes)
    (original : Automaton State Symbol)
    (rows : State → List (Row State Symbol Constraint))
    (answer : Constraint × Term Symbol → Guards.Verdict)
    (holds : Constraint → Term Symbol → Bool)
    (rowOrder : ∀ state, (automaton rows holds state).Perm (original state))
    (adequate : SourceSizedDecidedFilter.Adequate answer (fun pair => holds pair.1 pair.2))
    (root : State) (bound : Nat) (output : Table State (Term Symbol))
    (success : sizedUpTo rows (trimKeys nodes original root) answer bound = .ok output)
    (size : Nat) (term : Term Symbol) :
    term ∈ output root size ↔ Accepts original root term ∧ nodeSize term = size ∧ size ≤ bound := by
  rw [sizedUpTo_member_iff rows (trimKeys nodes original root) answer holds adequate bound output success,
    sorted_selected_exact nodes complete original (automaton rows holds) rowOrder root term]
  have included := root_mem_trimKeys nodes complete original root
  constructor
  · rintro ⟨_, _, below, accepted, exactSize⟩
    exact ⟨accepted, exactSize, below⟩
  · rintro ⟨accepted, exactSize, below⟩
    have positive := nodeSize_pos term
    exact ⟨included, by omega, below, accepted, exactSize⟩

end MicroCFTA.SourceSizedDecidedTrim
