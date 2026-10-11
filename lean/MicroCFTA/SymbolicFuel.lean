import MicroCFTA.SymbolicWellFounded

/-!
# Stability of successful normalization at larger execution bounds

Increasing fuel cannot change a completed substitution or normalization.
These exact-output results let finite recursive traversals share one bound.
-/
namespace MicroCFTA.SymbolicDriver
open Symbolic (Fragment Target Obligation)

/-- The second pure execution preserves every successful output of the first. -/
def ExceptRefines (first second : Except Failure Value) : Prop :=
  ∀ output, first = .ok output → second = .ok output

/-- Every pure computation preserves its own successful outputs. -/
theorem ExceptRefines.refl (action : Except Failure Value) : ExceptRefines action action := fun _ success => success

/-- Success preservation composes through the actual `Except` bind. -/
theorem except_bind_refines (first second : Except Failure Input) (left right : Input → Except Failure Output)
    (initial : ExceptRefines first second) (following : ∀ input, ExceptRefines (left input) (right input)) :
    ExceptRefines (first >>= left) (second >>= right) := by
  intro output success
  cases computed : first with
  | error error => simp only [computed, Bind.bind, Except.bind] at success; cases success
  | ok input =>
      have stable := initial input computed
      simp only [computed, Bind.bind, Except.bind] at success
      simpa only [stable, Bind.bind, Except.bind] using following input output success

/-- Success preservation composes through the source's finite pure traversal. -/
theorem except_mapM_refines (first second : Input → Except Failure Output) (inputs : List Input)
    (each : ∀ input, ExceptRefines (first input) (second input)) :
    ExceptRefines (inputs.mapM first) (inputs.mapM second) := by
  induction inputs with
  | nil => exact ExceptRefines.refl _
  | cons input inputs ih =>
      simp only [List.mapM_cons]
      apply except_bind_refines _ _ _ _ (each input)
      intro head
      apply except_bind_refines _ _ _ _ ih
      intro tail
      exact ExceptRefines.refl _

/-- Actual binding inlining preserves exact successful outputs when fuel increases. -/
theorem inline_fuel_mono (bindings : List (Nat × Fragment Symbol)) (fuel larger : Nat) (increase : fuel ≤ larger) :
    (∀ fragment, ExceptRefines (inline bindings fuel fragment) (inline bindings larger fragment)) ∧
    (∀ children, ExceptRefines (inlineMany bindings fuel children) (inlineMany bindings larger children)) := by
  induction fuel generalizing larger with
  | zero =>
      constructor
      · intro fragment output success; cases success
      · intro children
        cases children with
        | nil => simp only [inlineMany]; exact ExceptRefines.refl _
        | cons first rest => intro output success; cases success
  | succ fuel ih =>
      cases larger with
      | zero => omega
      | succ larger =>
          have recursive := ih larger (by omega)
          constructor
          · intro fragment
            cases fragment with
            | var name =>
                cases found : lookup bindings name with
                | none => simp only [inline, found]; exact ExceptRefines.refl _
                | some context => simpa only [inline, found] using recursive.1 context
            | constructor symbol children =>
                simp only [inline]
                exact except_bind_refines _ _ _ _ (recursive.2 children) (fun _ => ExceptRefines.refl _)
          · intro children
            cases children with
            | nil => exact ExceptRefines.refl _
            | cons first rest =>
                simp only [inlineMany]
                apply except_bind_refines _ _ _ _ (recursive.1 first)
                intro head
                exact except_bind_refines _ _ _ _ (recursive.2 rest) (fun _ => ExceptRefines.refl _)

/-- Actual path following preserves exact successful outputs when fuel increases. -/
theorem follow_fuel_mono (bindings : List (Nat × Fragment Symbol)) (fuel larger : Nat) (increase : fuel ≤ larger)
    (fragment : Fragment Symbol) (path : List Nat) : ExceptRefines (follow bindings fuel fragment path) (follow bindings larger fragment path) := by
  induction fuel generalizing larger fragment path with
  | zero => intro output success; cases success
  | succ fuel ih =>
      cases larger with
      | zero => omega
      | succ larger =>
          have increment : fuel ≤ larger := by omega
          cases fragment with
          | var name =>
              cases found : lookup bindings name with
              | none => simp only [follow, found]; exact ExceptRefines.refl _
              | some context => simpa only [follow, found] using ih larger increment context path
          | constructor symbol children =>
              cases path with
              | nil =>
                  simp only [follow]
                  exact except_bind_refines _ _ _ _ ((inline_fuel_mono bindings fuel larger increment).1 (.constructor symbol children))
                    (fun _ => ExceptRefines.refl _)
              | cons index rest =>
                  cases found : children[index]? with
                  | none => simp only [follow, found]; exact ExceptRefines.refl _
                  | some child => simpa only [follow, found] using ih larger increment child rest

/-- Actual alpha-renaming preserves exact successful outputs when fuel increases. -/
theorem rename_fuel_mono (names : List (Nat × Nat)) (fuel larger : Nat) (increase : fuel ≤ larger) :
    (∀ fragment : Fragment Symbol, ExceptRefines (rename names fuel fragment) (rename names larger fragment)) ∧
    (∀ children : List (Fragment Symbol), ExceptRefines (renameMany names fuel children) (renameMany names larger children)) := by
  induction fuel generalizing larger with
  | zero =>
      constructor
      · intro fragment output success; cases success
      · intro children
        cases children with
        | nil => simp only [renameMany]; exact ExceptRefines.refl _
        | cons first rest => intro output success; cases success
  | succ fuel ih =>
      cases larger with
      | zero => omega
      | succ larger =>
          have recursive := ih larger (by omega)
          constructor
          · intro fragment
            cases fragment with
            | var name => simp only [rename]; exact ExceptRefines.refl _
            | constructor symbol children =>
                simp only [rename]
                exact except_bind_refines _ _ _ _ (recursive.2 children) (fun _ => ExceptRefines.refl _)
          · intro children
            cases children with
            | nil => exact ExceptRefines.refl _
            | cons first rest =>
                simp only [renameMany]
                apply except_bind_refines _ _ _ _ (recursive.1 first)
                intro head
                exact except_bind_refines _ _ _ _ (recursive.2 rest) (fun _ => ExceptRefines.refl _)

/-- A completed target normalization keeps the same result at every larger fuel. -/
theorem normalizeTarget_fuel_mono (problem : Problem Symbol) (names : List (Nat × Nat))
    (fuel larger : Nat) (increase : fuel ≤ larger) (target : Target Symbol) :
    ExceptRefines (normalizeTarget fuel problem names target) (normalizeTarget larger problem names target) := by
  unfold normalizeTarget
  apply except_bind_refines _ _ _ _ (follow_fuel_mono problem.bindings fuel larger increase target.fragment target.path)
  intro result
  cases result with
  | none => exact ExceptRefines.refl _
  | some current =>
      exact except_bind_refines _ _ _ _ ((rename_fuel_mono names fuel larger increase).1 current.fragment)
        (fun _ => ExceptRefines.refl _)

/-- A completed requirement normalization keeps the same result at every larger fuel. -/
theorem normalizeObligation_fuel_mono [DecidableEq Symbol] [Ord Symbol]
    (problem : Problem Symbol) (names : List (Nat × Nat)) (fuel larger : Nat) (increase : fuel ≤ larger)
    (requirement : Obligation Symbol) :
    ExceptRefines (normalizeObligation fuel problem names requirement) (normalizeObligation larger problem names requirement) := by
  cases requirement with
  | «exists» target =>
      simp only [normalizeObligation]
      exact except_bind_refines _ _ _ _ (normalizeTarget_fuel_mono problem names fuel larger increase target)
        (fun _ => ExceptRefines.refl _)
  | equal left right =>
      simp only [normalizeObligation]
      apply except_bind_refines _ _ _ _ (normalizeTarget_fuel_mono problem names fuel larger increase left)
      intro first
      exact except_bind_refines _ _ _ _ (normalizeTarget_fuel_mono problem names fuel larger increase right)
        (fun _ => ExceptRefines.refl _)

/-- The complete actual normalizer keeps its exact result at every larger execution bound. -/
theorem normalize_fuel_mono [DecidableEq Symbol] [Ord Symbol]
    (problem : Problem Symbol) (fuel larger : Nat) (increase : fuel ≤ larger) :
    ExceptRefines (normalize fuel problem) (normalize larger problem) := by
  unfold normalize
  apply except_bind_refines _ _ _ _
    (except_mapM_refines _ _ problem.obligations (normalizeObligation_fuel_mono problem _ fuel larger increase))
  intro pending
  exact ExceptRefines.refl _

end MicroCFTA.SymbolicDriver
