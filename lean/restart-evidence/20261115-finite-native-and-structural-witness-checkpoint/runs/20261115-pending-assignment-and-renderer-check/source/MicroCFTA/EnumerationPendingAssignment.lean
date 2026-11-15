import MicroCFTA.EnumerationAssignment

/-!
# Stored fragment equations with fixed pending choices

The finite evaluator uses the supplied term at each unresolved variable.
Union-find compatibility preserves those choices on pending classes.
The result certifies stored fragment equations only.
-/

namespace MicroCFTA.EnumerationPendingAssignment
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDriver
open EnumerationDependencies EnumerationReferences EnumerationOrder

variable {Symbol Guard : Type}

/-- Evaluate stored fragments and retain the supplied choice at every unresolved variable. -/
def evaluateSlotsWith (values : List (UVarValue Symbol)) (roots : Nat → Nat)
    (base : Nat → Term Symbol) : Nat → Nat → Term Symbol
  | 0, uv => base uv
  | fuel + 1, uv =>
      match values[roots uv]? with
      | some (.enumerated fragment) => fill (evaluateSlotsWith values roots base fuel) fragment
      | _ => base uv

/-- Evaluation stabilizes above the remaining fragment dependency levels. -/
theorem evaluateSlotsWith_stable
    (state : State Symbol Guard) (roots : Nat → Nat) (paths : Roots state.representatives roots)
    (level : Nat → Nat) (frontier : Nat) (stratified : Stratified state level frontier)
    (base : Nat → Term Symbol) (uv leftFuel rightFuel : Nat)
    (leftBound : frontier - level uv < leftFuel) (rightBound : frontier - level uv < rightFuel) :
    evaluateSlotsWith state.values roots base leftFuel uv =
      evaluateSlotsWith state.values roots base rightFuel uv := by
  have stable : ∀ deficit uv, frontier - level uv = deficit → ∀ leftFuel rightFuel,
      deficit < leftFuel → deficit < rightFuel →
      evaluateSlotsWith state.values roots base leftFuel uv =
        evaluateSlotsWith state.values roots base rightFuel uv := by
    intro deficit
    induction deficit using Nat.strongRecOn with
    | ind deficit ih =>
        intro uv difference leftFuel rightFuel leftBound rightBound
        cases leftFuel with
        | zero => omega
        | succ leftFuel =>
            cases rightFuel with
            | zero => omega
            | succ rightFuel =>
                cases stored : state.values[roots uv]? with
                | none => simp [evaluateSlotsWith, stored]
                | some value =>
                    cases value with
                    | eliminated | unenumerated _ _ => simp [evaluateSlotsWith, stored]
                    | enumerated fragment =>
                        simp only [evaluateSlotsWith, stored]
                        apply EnumerationAssignment.fill_holes_congr
                        intro hole present
                        obtain ⟨size, path⟩ := paths uv
                        have sameLevel := stratified.classes uv (roots uv) (UnionFind.sameClass_root path)
                        obtain ⟨bound, dependencies⟩ := stratified.expanded (roots uv) fragment stored
                        have increases := dependencies hole present
                        have smaller : frontier - level hole < deficit := by omega
                        exact ih (frontier - level hole) smaller hole rfl leftFuel rightFuel (by omega) (by omega)
  exact stable (frontier - level uv) uv rfl leftFuel rightFuel leftBound rightBound

/-- One assignment retains pending choices and satisfies the UF and every stored fragment equation. -/
theorem stratified_extend_pending
    (state : State Symbol Guard) (safe : Safe state)
    (level : Nat → Nat) (frontier : Nat) (stratified : Stratified state level frontier)
    (base : Nat → Term Symbol) (compatible : UnionFind.Satisfies state.representatives base) :
    ∃ assignment : Nat → Term Symbol,
      UnionFind.Satisfies state.representatives assignment ∧
      (∀ uv fragment, state.values[uv]? = some (.enumerated fragment) →
        assignment uv = fill assignment fragment) ∧
      ∀ uv node scs, state.values[uv]? = some (.unenumerated node scs) → assignment uv = base uv := by
  obtain ⟨roots, paths⟩ := roots_exist state.representatives safe.1.total
  let assignment := evaluateSlotsWith state.values roots base (frontier + 1)
  have aliases : UnionFind.Satisfies state.representatives assignment := by
    intro left right same
    have sameRoot := (class_iff state.representatives roots paths left right).mp same
    change evaluateSlotsWith state.values roots base (frontier + 1) left =
      evaluateSlotsWith state.values roots base (frontier + 1) right
    rw [evaluateSlotsWith, evaluateSlotsWith, sameRoot]
    cases stored : state.values[roots right]? with
    | none => exact compatible left right same
    | some value =>
        cases value with
        | eliminated | unenumerated _ _ => exact compatible left right same
        | enumerated fragment => rfl
  refine ⟨assignment, aliases, ?_, ?_⟩
  · intro uv fragment stored
    have fixed := stored_root_fixed state safe roots paths uv _ stored (by simp)
    have equation : fill assignment fragment = assignment uv := by
      change fill assignment fragment = evaluateSlotsWith state.values roots base (frontier + 1) uv
      rw [evaluateSlotsWith, fixed, stored]
      apply EnumerationAssignment.fill_holes_congr
      intro hole present
      obtain ⟨bound, dependencies⟩ := stratified.expanded uv fragment stored
      have higher := dependencies hole present
      exact evaluateSlotsWith_stable state roots paths level frontier stratified base hole
        (frontier + 1) frontier (by omega) (by omega)
    exact equation.symm
  · intro uv node scs stored
    have fixed := stored_root_fixed state safe roots paths uv _ stored (by simp)
    change evaluateSlotsWith state.values roots base (frontier + 1) uv = base uv
    rw [evaluateSlotsWith, fixed, stored]

end MicroCFTA.EnumerationPendingAssignment

#print axioms MicroCFTA.EnumerationPendingAssignment.evaluateSlotsWith_stable
#print axioms MicroCFTA.EnumerationPendingAssignment.stratified_extend_pending
