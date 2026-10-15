import MicroCFTA.Cache

/-!
# A decreasing rank for ordered binder contexts

The source keeps only bound states below an unbound child before building
that child. Lower state indexes have greater binary weight. Adding that
child therefore outweighs every removed higher state. This proves progress
within one component. Cross-component calls still need condensation order.
-/
namespace MicroCFTA.SourceOrderedBinderRank

/-- Encode bounded state membership with the smallest index as the most significant bit. -/
def code : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | width + 1, member => (if member 0 then 2 ^ width else 0) + code width (fun index => member (index + 1))

/-- The finite membership code is strictly below its binary capacity. -/
theorem code_bound (width : Nat) (member : Nat → Bool) : code width member < 2 ^ width := by
  induction width generalizing member with
  | zero => simp [code]
  | succ width ih =>
      have tail := ih (fun index => member (index + 1))
      simp only [code, Nat.pow_succ]
      split <;> omega

/-- Equal membership at every bounded state gives equal context codes. -/
theorem code_congr (width : Nat) (first second : Nat → Bool)
    (same : ∀ index < width, first index = second index) : code width first = code width second := by
  induction width generalizing first second with
  | zero => rfl
  | succ width ih =>
      rw [code, code, same 0 (by omega), ih _ _ (fun index bound => same (index + 1) (by omega))]

/-- At the first different index, absent-to-present membership strictly increases the code. -/
theorem code_first_difference (width pivot : Nat) (first second : Nat → Bool)
    (bounded : pivot < width) (earlier : ∀ index < pivot, first index = second index)
    (absent : first pivot = false) (present : second pivot = true) : code width first < code width second := by
  induction width generalizing pivot first second with
  | zero => omega
  | succ width ih =>
      cases pivot with
      | zero =>
          have tail := code_bound width (fun index => first (index + 1))
          simp only [code, absent, present, Bool.false_eq_true, ↓reduceIte]
          omega
      | succ pivot =>
          have tail := ih pivot (fun index => first (index + 1)) (fun index => second (index + 1))
            (by omega) (fun index bound => earlier (index + 1) (by omega)) absent present
          rw [code, code, earlier 0 (by omega)]
          omega

/-- An unbound child retains lower membership and becomes the last bound state itself. -/
def select (member : Nat → Bool) (pivot : Nat) (index : Nat) : Bool :=
  if index < pivot then member index else decide (index = pivot)

/-- The exact ordered-prefix update increases the code of every bounded absent child. -/
theorem select_increases (width pivot : Nat) (member : Nat → Bool)
    (bounded : pivot < width) (absent : member pivot = false) :
    code width member < code width (select member pivot) :=
  code_first_difference width pivot member (select member pivot) bounded
    (fun index before => by simp only [select, before, ↓reduceIte]) absent
    (by simp only [select, Nat.lt_irrefl, ↓reduceIte, decide_true])

/-- A source build context includes its current state and the earlier enclosing binders. -/
def context (bound : List Nat) (here index : Nat) : Bool := decide (index ∈ here :: bound)

/-- Remaining binary capacity is a natural-number rank for same-component build calls. -/
def rank (width : Nat) (bound : List Nat) (here : Nat) : Nat :=
  2 ^ width - code width (context bound here)

/-- The rank depends on bound-state membership, not the chosen list representation. -/
theorem rank_congr (width : Nat) (first second : List Nat) (here : Nat)
    (same : ∀ index, index ∈ first ↔ index ∈ second) : rank width first here = rank width second here := by
  have equal : context first here = context second here := by
    funext index
    simp only [context, List.mem_cons, same index]
  simp only [rank, equal]

/-- The actual strict-prefix child context has exactly the ordered-prefix membership update. -/
theorem context_child (bound : List Nat) (here next : Nat) :
    context ((here :: bound).filter (fun state => decide (state < next))) next = select (context bound here) next := by
  funext index
  by_cases before : index < next
  · have different : index ≠ next := by omega
    simp [context, select, before, different]
  · simp [context, select, before]

/-- Every actual bounded unbound same-component child call strictly decreases the rank. -/
theorem child_decreases (width : Nat) (bound : List Nat) (here next : Nat)
    (bounded : next < width) (unbound : next ∉ here :: bound) :
    rank width ((here :: bound).filter (fun state => decide (state < next))) next < rank width bound here := by
  have absent : context bound here next = false := by simp only [context, decide_eq_false_iff_not]; exact unbound
  have grows := select_increases width next (context bound here) bounded absent
  have lower := code_bound width (context bound here)
  have upper := code_bound width (select (context bound here) next)
  simp only [rank, context_child]
  omega

/-- The ascending-list form of the actual source body context has the same decreasing rank. -/
theorem child_decreases_append (width : Nat) (bound : List Nat) (here next : Nat)
    (bounded : next < width) (unbound : next ∉ bound ++ [here]) :
    rank width ((bound ++ [here]).filter (fun state => decide (state < next))) next < rank width bound here := by
  rw [rank_congr width _ ((here :: bound).filter (fun state => decide (state < next))) next
    (fun index => by simp [or_comm, or_and_right])]
  exact child_decreases width bound here next bounded (by simpa [or_comm] using unbound)

end MicroCFTA.SourceOrderedBinderRank
