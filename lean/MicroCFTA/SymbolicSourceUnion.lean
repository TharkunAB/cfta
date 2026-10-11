import MicroCFTA.SymbolicIndicators

/-!
# Empty-intersection filtering and coefficient traversal order

The Haskell union loop removes an intersection when its normalized singleton
node has no rows. The counter model retains this zero contribution. The
theorems below compare their numeric results. They do not identify the cache
traces. The source traverses a Map in key order; the model uses a list.
-/
namespace MicroCFTA.SymbolicSourceUnion
open Symbolic SignedUnion

/-- The source retains only nonempty normalized intersection nodes. -/
def filteredMeet (meet : Key → Key → Option Key) (keep : Key → Bool)
    (left right : Key) : Option Key :=
  (meet left right).filter keep

/-- Removing a numeric zero retains exact multiplication at every intersection. -/
theorem filtered_product (value : Key → Int) (meet : Key → Key → Option Key)
    (keep : Key → Bool) (exact : ExactProduct value meet)
    (empty : ∀ key, keep key = false → value key = 0) :
    ExactProduct value (filteredMeet meet keep) := by
  intro left right
  have product := exact left right
  cases found : meet left right with
  | none => simpa [filteredMeet, found] using product
  | some common =>
    cases retained : keep common with
    | false =>
      have zero := empty common retained
      simpa [filteredMeet, Option.filter, found, retained, zero] using product
    | true => simpa [filteredMeet, Option.filter, found, retained] using product

/-- Empty intersections may be removed throughout the complete signed union loop. -/
theorem union_filter_exact [DecidableEq Key] (value : Key → Int) (member : Key → Bool)
    (meet : Key → Key → Option Key) (keep : Key → Bool)
    (exact : ExactProduct value meet) (empty : ∀ key, keep key = false → value key = 0)
    (keys : List Key) (originals : ∀ key ∈ keys, value key = Lattice.indicator (member key)) :
    weighted value (unionCoefficients (filteredMeet meet keep) keys) =
      weighted value (unionCoefficients meet keys) := by
  rw [union_indicator value member _ (filtered_product value meet keep exact empty) keys originals,
    union_indicator value member meet exact keys originals]

/-- Reordering the finite coefficient map does not change its numeric interpretation. -/
theorem weighted_permutation (value : Key → Int) (left right : Coefficients Key)
    (same : left.Perm right) : weighted value left = weighted value right := by
  induction same with
  | nil => rfl
  | cons entry _ ih => simp only [weighted, ih]
  | swap first second rest => simp only [weighted]; omega
  | trans _ _ first second => exact first.trans second

/-- List summation is the interpretation used by the signed coefficient map. -/
theorem map_sum_weighted (value : Key → Int) (pieces : Coefficients Key) :
    (pieces.map fun piece => piece.2 * value piece.1).sum = weighted value pieces := by
  induction pieces with
  | nil => rfl
  | cons first rest ih => simp [weighted, ih]

/-- A signed traversal uses semantic recursive results and preserves its cache invariant. -/
theorem traversal_correct
    (action : Key → StateT State (Except Failure) Int)
    (value : Key → Int) (invariant : State → Prop)
    (correct : ∀ key before result after, invariant before →
      action key before = .ok (result, after) → result = value key ∧ invariant after)
    (pieces : Coefficients Key) (before after : State) (result : Int)
    (starts : invariant before)
    (success : ((do
      let values ← pieces.mapM fun piece => do pure (piece.2 * (← action piece.1))
      pure values.sum) : StateT State (Except Failure) Int) before = .ok (result, after)) :
    result = weighted value pieces ∧ invariant after := by
  let contribution := fun piece : Key × Int =>
    (do pure (piece.2 * (← action piece.1)) : StateT State (Except Failure) Int)
  have each : ∀ piece initial output finalState, invariant initial →
      contribution piece initial = .ok (output, finalState) →
      output = piece.2 * value piece.1 ∧ invariant finalState := by
    intro piece initial output finalState start done
    change Except.bind (action piece.1 initial)
      (fun (number, state) => .ok (piece.2 * number, state)) = .ok (output, finalState) at done
    cases counted : action piece.1 initial with
    | error error => simp only [counted] at done; cases done
    | ok pair =>
      rcases pair with ⟨number, state⟩
      obtain ⟨right, safe⟩ := correct piece.1 initial number state start counted
      simp only [counted, Except.bind, Except.ok.injEq, Prod.mk.injEq] at done
      rcases done with ⟨rfl, rfl⟩
      exact ⟨by rw [right], safe⟩
  change Except.bind ((pieces.mapM contribution : StateT State (Except Failure) (List Int)) before)
    (fun (values, state) => .ok (values.sum, state)) = .ok (result, after) at success
  cases counted : (pieces.mapM contribution : StateT State (Except Failure) (List Int)) before with
  | error error => simp only [counted] at success; cases success
  | ok pair =>
    rcases pair with ⟨values, state⟩
    obtain ⟨right, safe⟩ := SymbolicDriver.state_mapM_correct contribution
      (fun piece => piece.2 * value piece.1) invariant each pieces before state values starts counted
    simp only [counted, Except.bind, Except.ok.injEq, Prod.mk.injEq] at success
    rcases success with ⟨rfl, rfl⟩
    refine ⟨?_, safe⟩
    rw [right]
    exact map_sum_weighted value pieces

end MicroCFTA.SymbolicSourceUnion
