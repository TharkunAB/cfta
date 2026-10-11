import MicroCFTA.MinimumSize

/-!
# Recursive generator probe convergence

`Gen.Internal.Recur` rebuilds a body at decreasing minimum-size assumptions.
The first assumption is `NoFiniteMember`. After the first finite result the
stored natural size can only decrease. This module implements that control
loop with a terminating recursion and derives its stable probe result.
-/

namespace MicroCFTA.RecursionProbe
open MinimumSize

/-- The fields read from a successful recursive view of the probe body. -/
structure View where
  minimum : Option Nat
  usesOccurrence : Bool
  unguarded : Bool
  weighted : Bool
  deriving DecidableEq, Repr

/-- The source checks opaque and construction-error bodies before recursive metadata. -/
inductive Body where
  | opaque
  | failed (error : Nat)
  | ready (view : View)
  deriving DecidableEq, Repr

/-- A failed or opaque recursive view contributes no finite minimum. -/
def minimum : Body → Option Nat
  | .ready view => view.minimum
  | _ => none

/-- The stable assumption, its actual body, and the number of body constructions. -/
structure Result where
  assumption : Option Nat
  body : Body
  steps : Nat
  deriving Repr

/-- Once a finite minimum is found, each recursive call uses a strictly smaller natural size. -/
def convergeFinite (build : Option Nat → Body) (assumed : Nat) : Result :=
  let body := build (some assumed)
  match minimum body with
  | none => ⟨some assumed, body, 1⟩
  | some reached =>
      if _smaller : reached < assumed then
        let result := convergeFinite build reached
        {result with steps := result.steps + 1}
      else ⟨some assumed, body, 1⟩
termination_by assumed

/-- The source starts with no known finite member, then retains the least discovered size. -/
def converge (build : Option Nat → Body) : Result :=
  let body := build none
  match minimum body with
  | none => ⟨none, body, 1⟩
  | some reached =>
      let result := convergeFinite build reached
      {result with steps := result.steps + 1}

/-- Every finite probe run returns an actual body at a stable assumption within its derived step bound. -/
theorem convergeFinite_correct (build : Option Nat → Body) (assumed : Nat) :
    let result := convergeFinite build assumed
    result.body = build result.assumption ∧ best result.assumption (minimum result.body) = result.assumption ∧
      (∃ finalSize, result.assumption = some finalSize ∧ finalSize ≤ assumed) ∧ result.steps ≤ assumed + 1 := by
  induction assumed using Nat.strongRecOn with
  | ind assumed ih =>
      rw [convergeFinite]
      split
      next absent => simp [best, absent]
      next reached found =>
        split
        next smaller =>
          obtain ⟨body, stable, ⟨finalSize, shape, smallerFinal⟩, bound⟩ := ih reached smaller
          exact ⟨body, stable, ⟨finalSize, shape, by omega⟩, by dsimp; omega⟩
        next stopped => simp [best, found, Nat.min_eq_left (by omega : assumed ≤ reached)]

/-- Probe convergence is total for every total body builder; no fixed-point postcondition is assumed. -/
theorem converge_correct (build : Option Nat → Body) :
    (converge build).body = build (converge build).assumption ∧
      best (converge build).assumption (minimum (converge build).body) = (converge build).assumption := by
  rw [converge]
  split
  next absent => simp [best, absent]
  next reached found => exact ⟨(convergeFinite_correct build reached).1, (convergeFinite_correct build reached).2.1⟩

/-- The initial successful finite discovery bounds all later body constructions. -/
theorem converge_steps (build : Option Nat → Body) (reached : Nat)
    (first : minimum (build none) = some reached) : (converge build).steps ≤ reached + 2 := by
  simp only [converge, first]
  have bound := (convergeFinite_correct build reached).2.2.2
  omega

/-- Public dispatch preserves construction errors and separates finite bodies from invalid recursive knots. -/
inductive Dispatch where
  | opaque | failed (error : Nat) | finite | unguarded | empty
  | recursive (minimum : Nat) (weighted : Bool)
  deriving DecidableEq, Repr

/-- The final error and finite/recursive precedence in `recur`. -/
def dispatch : Body → Dispatch
  | .opaque => .opaque
  | .failed error => .failed error
  | .ready view =>
      if !view.usesOccurrence then .finite
      else if view.unguarded then .unguarded
      else match view.minimum with
        | none => .empty
        | some size => .recursive size view.weighted

/-- A body without its own occurrence is returned as a finite language before knot validation. -/
theorem unused_is_finite (view : View) (unused : view.usesOccurrence = false) :
    dispatch (.ready view) = .finite := by simp [dispatch, unused]

/-- A live unguarded occurrence is rejected even if its body also has no finite member. -/
theorem unguarded_precedence (view : View) (used : view.usesOccurrence = true) (unguarded : view.unguarded = true) :
    dispatch (.ready view) = .unguarded := by simp [dispatch, used, unguarded]

/-- A source construction failure cannot become an unbounded-generator error. -/
theorem construction_error_retained (error : Nat) : dispatch (.failed error) = .failed error := rfl

/-- Successful recursive dispatch derives all the metadata conditions needed to tie its fields. -/
theorem recursive_dispatch (view : View) (size : Nat) (weighted : Bool) :
    dispatch (.ready view) = .recursive size weighted ↔
      view.usesOccurrence = true ∧ view.unguarded = false ∧ view.minimum = some size ∧ view.weighted = weighted := by
  cases used : view.usesOccurrence <;> cases guarded : view.unguarded <;>
    cases found : view.minimum <;> simp [dispatch, used, guarded, found]

/-- The minimum metadata of the standard finite source, pay, choice, and product operations. -/
inductive MinimumExpr where
  | occurrence
  | source (minimum : Option Nat)
  | pay (inner : MinimumExpr)
  | atomic (inner : MinimumExpr)
  | choice (left right : MinimumExpr)
  | product (left right : MinimumExpr)
  deriving Repr

/-- Product minimum is finite exactly when both components have a finite minimum. -/
def productMinimum : Option Nat → Option Nat → Option Nat
  | some left, some right => some (left + right)
  | _, _ => none

/-- Interpret the source's minimum metadata without touching any count or decoder callback. -/
def evaluate (expression : MinimumExpr) (assumed : Option Nat) : Option Nat :=
  match expression with
  | .occurrence => assumed
  | .source minimum => minimum
  | .pay inner => (evaluate inner assumed).map (· + 1)
  | .atomic inner => (evaluate inner assumed).map (fun _ => 1)
  | .choice left right => best (evaluate left assumed) (evaluate right assumed)
  | .product left right => productMinimum (evaluate left assumed) (evaluate right assumed)

/-- Improving either child cannot increase the minimum of a choice. -/
theorem best_monotone (left right nextLeft nextRight : Option Nat)
    (hl : Improves left nextLeft) (hr : Improves right nextRight) :
    Improves (best left right) (best nextLeft nextRight) := by
  intro size found
  rcases best_source left right size found with fromLeft | fromRight
  · obtain ⟨smaller, present, bound⟩ := hl size fromLeft
    obtain ⟨smallest, kept, smallerBound⟩ := best_improves_left nextLeft nextRight smaller present
    exact ⟨smallest, kept, by omega⟩
  · obtain ⟨smaller, present, bound⟩ := hr size fromRight
    obtain ⟨smallest, kept, smallerBound⟩ := best_improves_right nextLeft nextRight smaller present
    exact ⟨smallest, kept, by omega⟩

/-- Improving child minima cannot increase their product's minimum. -/
theorem product_monotone (left right nextLeft nextRight : Option Nat)
    (hl : Improves left nextLeft) (hr : Improves right nextRight) :
    Improves (productMinimum left right) (productMinimum nextLeft nextRight) := by
  intro size found
  cases left with
  | none => simp [productMinimum] at found
  | some left =>
      cases right with
      | none => simp [productMinimum] at found
      | some right =>
          obtain ⟨smallerLeft, presentLeft, boundLeft⟩ := hl left rfl
          obtain ⟨smallerRight, presentRight, boundRight⟩ := hr right rfl
          refine ⟨smallerLeft + smallerRight, ?_, ?_⟩
          · simp [productMinimum, presentLeft, presentRight]
          · simp only [productMinimum, Option.some.injEq] at found
            omega

/-- The actual standard minimum operations make the probe transformer monotone. -/
theorem evaluate_monotone (expression : MinimumExpr) (before after : Option Nat) (improves : Improves before after) :
    Improves (evaluate expression before) (evaluate expression after) := by
  induction expression with
  | occurrence => exact improves
  | source minimum => exact improves_refl minimum
  | pay inner ih =>
      intro size found
      obtain ⟨old, original, same⟩ := Option.map_eq_some_iff.mp found
      obtain ⟨smaller, present, bound⟩ := ih old original
      exact ⟨smaller + 1, by simp [evaluate, present], by omega⟩
  | atomic inner ih =>
      intro size found
      obtain ⟨old, original, same⟩ := Option.map_eq_some_iff.mp found
      obtain ⟨smaller, present, _⟩ := ih old original
      exact ⟨1, by simp [evaluate, present], by omega⟩
  | choice left right ihl ihr => exact best_monotone _ _ _ _ ihl ihr
  | product left right ihl ihr => exact product_monotone _ _ _ _ ihl ihr

/-- A monotone builder's decreasing probe stops at an actual minimum fixed point. -/
theorem convergeFinite_fixed (build : Option Nat → Body)
    (monotone : ∀ before after, Improves before after → Improves (minimum (build before)) (minimum (build after)))
    (assumed : Nat) (noGrowth : Improves (some assumed) (minimum (build (some assumed)))) :
    minimum (convergeFinite build assumed).body = (convergeFinite build assumed).assumption := by
  revert noGrowth
  induction assumed using Nat.strongRecOn with
  | ind assumed ih =>
      intro noGrowth
      rw [convergeFinite]
      split
      next absent =>
        obtain ⟨smaller, present, _⟩ := noGrowth assumed rfl
        simp [absent] at present
      next reached found =>
        split
        next smaller =>
          have improves : Improves (some assumed) (some reached) := by
            intro size same
            have equal : assumed = size := Option.some.inj same
            exact ⟨reached, rfl, by omega⟩
          have nextGrowth := monotone (some assumed) (some reached) improves
          rw [found] at nextGrowth
          exact ih reached smaller nextGrowth
        next stopped =>
          obtain ⟨smaller, present, bound⟩ := noGrowth assumed rfl
          have equal : reached = smaller := Option.some.inj (found.symm.trans present)
          have same : reached = assumed := by omega
          simpa only [same] using found

/-- The source's initial unknown assumption yields an actual fixed minimum for every monotone builder. -/
theorem converge_fixed (build : Option Nat → Body)
    (monotone : ∀ before after, Improves before after → Improves (minimum (build before)) (minimum (build after))) :
    minimum (converge build).body = (converge build).assumption := by
  rw [converge]
  split
  next absent => exact absent
  next reached found =>
    have starts : Improves none (some reached) := by intro size same; contradiction
    have nextGrowth := monotone none (some reached) starts
    rw [found] at nextGrowth
    exact convergeFinite_fixed build monotone reached nextGrowth

/-- Minimum metadata built only from standard source operations meets the monotone probe contract. -/
def expressionBody (expression : MinimumExpr) (used unguarded weighted : Bool) (assumed : Option Nat) : Body :=
  .ready ⟨evaluate expression assumed, used, unguarded, weighted⟩

/-- Standard metadata construction needs no assumed minimum fixed-point postcondition. -/
theorem expression_minimum_fixed (expression : MinimumExpr) (used unguarded weighted : Bool) :
    minimum (converge (expressionBody expression used unguarded weighted)).body =
      (converge (expressionBody expression used unguarded weighted)).assumption :=
  converge_fixed _ (fun before after improved => evaluate_monotone expression before after improved)

/-- Weighted flags combine by disjunction through maps, pays, choices, and products. -/
inductive WeightExpr where
  | occurrence
  | source (weighted : Bool)
  | combine (left right : WeightExpr)
  deriving Repr

/-- The probe starts its own recursive occurrence with an unweighted flag. -/
def evaluateWeight : WeightExpr → Bool → Bool
  | .occurrence, assumed => assumed
  | .source weighted, _ => weighted
  | .combine left right, assumed => evaluateWeight left assumed || evaluateWeight right assumed

/-- If a standard flag expression is true without recursive weights, it stays true with them. -/
theorem weight_monotone (expression : WeightExpr) (positive : evaluateWeight expression false = true) :
    evaluateWeight expression true = true := by
  induction expression with
  | occurrence => simp [evaluateWeight] at positive
  | source weighted => exact positive
  | combine left right ihl ihr =>
      simp only [evaluateWeight, Bool.or_eq_true] at positive ⊢
      exact positive.elim (fun h => Or.inl (ihl h)) (fun h => Or.inr (ihr h))

/-- The source's single false-flag probe computes the least stable recursive weighted flag. -/
theorem weighted_probe_fixed (expression : WeightExpr) :
    evaluateWeight expression (evaluateWeight expression false) = evaluateWeight expression false := by
  cases found : evaluateWeight expression false
  · exact found
  · exact weight_monotone expression found

/-- Any stable weighted flag includes every intrinsic atomic weight found by the probe. -/
theorem weighted_probe_least (expression : WeightExpr) (candidate : Bool)
    (fixed : evaluateWeight expression candidate = candidate) :
    evaluateWeight expression false = true → candidate = true := by
  intro positive
  cases candidate
  · simp [positive] at fixed
  · rfl

end MicroCFTA.RecursionProbe
