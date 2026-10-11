import MicroCFTA.SymbolicCounter

/-!
# Structural work in symbolic normalization

A variable can carry the work of its finite substitution. A strict binding
budget excludes substitution cycles. Constructor work counts every context
node. It is independent of accepted-term cardinality and signed coefficients.
-/
namespace MicroCFTA.SymbolicDriver
open Language
open Symbolic (Fragment Target)

mutual
  /-- Count constructor nodes and the supplied work of each variable occurrence. -/
  def fragmentWork (weight : Nat → Nat) : Fragment Symbol → Nat
    | .var name => weight name
    | .constructor _ children => 1 + fragmentsWork weight children

  /-- Add the work of ordered child contexts. -/
  def fragmentsWork (weight : Nat → Nat) : List (Fragment Symbol) → Nat
    | [] => 0
    | child :: rest => fragmentWork weight child + fragmentsWork weight rest
end

/-- Every context has positive work when every variable does. -/
theorem fragmentWork_positive (weight : Nat → Nat) (positive : ∀ name, 0 < weight name) (fragment : Fragment Symbol) :
    0 < fragmentWork weight fragment := by
  cases fragment with
  | var name => exact positive name
  | constructor _ _ => simp only [fragmentWork]; omega

/-- Each child context uses at most the complete child-list work. -/
theorem fragmentsWork_member (weight : Nat → Nat) (children : List (Fragment Symbol))
    (child : Fragment Symbol) (member : child ∈ children) : fragmentWork weight child ≤ fragmentsWork weight children := by
  induction children with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · simp only [fragmentsWork]; omega
      · have bound := ih member
        simp only [fragmentsWork]; omega

/-- Every substituted context has strictly smaller work than its bound variable. -/
def BindingBudget (weight : Nat → Nat) (bindings : List (Nat × Fragment Symbol)) : Prop :=
  (∀ name, 0 < weight name) ∧ ∀ name fragment, lookup bindings name = some fragment → fragmentWork weight fragment < weight name

/-- Successful inlining cannot increase the supplied substitution work. -/
theorem inline_work (weight : Nat → Nat) (bindings : List (Nat × Fragment Symbol))
    (budget : BindingBudget weight bindings) (fuel : Nat) :
    (∀ fragment output, inline bindings fuel fragment = .ok output → fragmentWork (fun _ => 1) output ≤ fragmentWork weight fragment) ∧
    (∀ children output, inlineMany bindings fuel children = .ok output → fragmentsWork (fun _ => 1) output ≤ fragmentsWork weight children) := by
  induction fuel with
  | zero =>
      constructor
      · intro fragment output success; cases success
      · intro children output success
        cases children with
        | nil => cases success; exact Nat.le_refl _
        | cons first rest => cases success
  | succ fuel ih =>
      constructor
      · intro fragment output success
        cases fragment with
        | var name =>
            cases found : lookup bindings name with
            | none =>
                simp only [inline, found] at success
                cases success
                exact budget.1 name
            | some context =>
                simp only [inline, found] at success
                have smaller := budget.2 name context found
                exact Nat.le_trans (ih.1 context output success) (Nat.le_of_lt smaller)
        | constructor symbol children =>
            simp only [inline] at success
            cases computed : inlineMany bindings fuel children with
            | error error => simp only [computed] at success; cases success
            | ok outputs =>
                simp only [computed, Bind.bind, Except.bind, Pure.pure, Except.pure] at success
                cases success
                have bounded := ih.2 children outputs computed
                simp only [fragmentWork]
                omega
      · intro children output success
        cases children with
        | nil => cases success; exact Nat.le_refl _
        | cons first rest =>
            simp only [inlineMany] at success
            cases firstResult : inline bindings fuel first with
            | error error => simp only [firstResult] at success; cases success
            | ok firstOutput =>
                cases restResult : inlineMany bindings fuel rest with
                | error error => simp only [firstResult, restResult, Bind.bind, Except.bind] at success; cases success
                | ok restOutput =>
                    simp only [firstResult, restResult, Bind.bind, Except.bind, Pure.pure, Except.pure] at success
                    cases success
                    have firstBound := ih.1 first firstOutput firstResult
                    have restBound := ih.2 rest restOutput restResult
                    simp only [fragmentsWork]
                    omega

/-- A strict binding budget gives an explicit sufficient fuel bound for complete inlining. -/
theorem inline_total (weight : Nat → Nat) (bindings : List (Nat × Fragment Symbol))
    (budget : BindingBudget weight bindings) (fuel : Nat) :
    (∀ fragment, 2 * fragmentWork weight fragment ≤ fuel → ∃ output, inline bindings fuel fragment = .ok output) ∧
    (∀ children, 2 * fragmentsWork weight children + 1 ≤ fuel → ∃ output, inlineMany bindings fuel children = .ok output) := by
  induction fuel with
  | zero =>
      constructor
      · intro fragment bounded
        have positive := fragmentWork_positive weight budget.1 fragment
        omega
      · intro children bounded; omega
  | succ fuel ih =>
      constructor
      · intro fragment bounded
        cases fragment with
        | var name =>
            cases found : lookup bindings name with
            | none => exact ⟨.var name, by simp only [inline, found]⟩
            | some context =>
                have smaller := budget.2 name context found
                have bound : 2 * fragmentWork weight context ≤ fuel := by
                  simp only [fragmentWork] at bounded
                  omega
                obtain ⟨output, success⟩ := ih.1 context bound
                exact ⟨output, by simp only [inline, found, success]⟩
        | constructor symbol children =>
            have bound : 2 * fragmentsWork weight children + 1 ≤ fuel := by
              simp only [fragmentWork] at bounded
              omega
            obtain ⟨output, success⟩ := ih.2 children bound
            exact ⟨.constructor symbol output, by simp only [inline, success]; rfl⟩
      · intro children bounded
        cases children with
        | nil => exact ⟨[], rfl⟩
        | cons first rest =>
            have positive := fragmentWork_positive weight budget.1 first
            have firstBound : 2 * fragmentWork weight first ≤ fuel := by
              simp only [fragmentsWork] at bounded
              omega
            have restBound : 2 * fragmentsWork weight rest + 1 ≤ fuel := by
              simp only [fragmentsWork] at bounded
              omega
            obtain ⟨firstOutput, firstResult⟩ := ih.1 first firstBound
            obtain ⟨restOutput, restResult⟩ := ih.2 rest restBound
            exact ⟨firstOutput :: restOutput, by simp only [inlineMany, firstResult, restResult]; rfl⟩

/-- Target work includes its unresolved path length. -/
def targetWork (weight : Nat → Nat) (target : Target Symbol) : Nat :=
  fragmentWork weight target.fragment + target.path.length

/-- Following a target does not increase its substitution and path work. -/
theorem follow_work (weight : Nat → Nat) (bindings : List (Nat × Fragment Symbol))
    (budget : BindingBudget weight bindings) (fuel : Nat) (fragment : Fragment Symbol) (path : List Nat)
    (output : Target Symbol) (success : follow bindings fuel fragment path = .ok (some output)) :
    targetWork (fun _ => 1) output ≤ fragmentWork weight fragment + path.length := by
  induction fuel generalizing fragment path output with
  | zero => cases success
  | succ fuel ih =>
      cases fragment with
      | var name =>
          cases found : lookup bindings name with
          | none =>
              simp only [follow, found] at success
              cases success
              have positive := budget.1 name
              simp only [targetWork, fragmentWork]
              omega
          | some context =>
              simp only [follow, found] at success
              have bound := ih context path output success
              have smaller := budget.2 name context found
              simp only [fragmentWork]
              omega
      | constructor symbol children =>
          cases path with
          | nil =>
              simp only [follow] at success
              cases computed : inline bindings fuel (.constructor symbol children) with
              | error error => simp only [computed] at success; cases success
              | ok inlined =>
                  simp only [computed, Bind.bind, Except.bind, Pure.pure, Except.pure] at success
                  cases success
                  simpa only [targetWork, List.length_nil, Nat.add_zero] using
                    (inline_work weight bindings budget fuel).1 (.constructor symbol children) inlined computed
          | cons index rest =>
              simp only [follow] at success
              cases found : children[index]? with
              | none => simp only [found] at success; cases success
              | some child =>
                  simp only [found] at success
                  have bound := ih child rest output success
                  have childBound := fragmentsWork_member weight children child (List.mem_of_getElem? found)
                  simp only [fragmentWork, List.length_cons]
                  omega

/-- A strict substitution budget also bounds path following, including full contexts at empty paths. -/
theorem follow_total (weight : Nat → Nat) (bindings : List (Nat × Fragment Symbol))
    (budget : BindingBudget weight bindings) (fuel : Nat) (fragment : Fragment Symbol) (path : List Nat)
    (bounded : 2 * fragmentWork weight fragment + path.length + 1 ≤ fuel) :
    ∃ output, follow bindings fuel fragment path = .ok output := by
  induction fuel generalizing fragment path with
  | zero => omega
  | succ fuel ih =>
      cases fragment with
      | var name =>
          cases found : lookup bindings name with
          | none => exact ⟨some ⟨.var name, path⟩, by simp only [follow, found]⟩
          | some context =>
              have smaller := budget.2 name context found
              have bound : 2 * fragmentWork weight context + path.length + 1 ≤ fuel := by
                simp only [fragmentWork] at bounded
                omega
              obtain ⟨output, success⟩ := ih context path bound
              exact ⟨output, by simp only [follow, found, success]⟩
      | constructor symbol children =>
          cases path with
          | nil =>
              have bound : 2 * fragmentWork weight (.constructor symbol children) ≤ fuel := by
                simp only [List.length_nil] at bounded
                omega
              obtain ⟨output, success⟩ := (inline_total weight bindings budget fuel).1 (.constructor symbol children) bound
              exact ⟨some ⟨output, []⟩, by simp only [follow, success]; rfl⟩
          | cons index rest =>
              cases found : children[index]? with
              | none => exact ⟨none, by simp only [follow, found]⟩
              | some child =>
                  have childBound := fragmentsWork_member weight children child (List.mem_of_getElem? found)
                  have bound : 2 * fragmentWork weight child + rest.length + 1 ≤ fuel := by
                    simp only [fragmentWork, List.length_cons] at bounded
                    omega
                  obtain ⟨output, success⟩ := ih child rest bound
                  exact ⟨output, by simp only [follow, found, success]⟩

/-- Context work depends only on weights of variables that actually occur. -/
theorem fragmentWork_congr (first second : Nat → Nat) (fragment : Fragment Symbol)
    (agree : ∀ name, occurs name fragment = true → first name = second name) :
    fragmentWork first fragment = fragmentWork second fragment := by
  induction fragment using Fragment.rec
    (motive_2 := fun children => (∀ name, occursMany name children = true → first name = second name) →
      fragmentsWork first children = fragmentsWork second children) with
  | var name => exact agree name (by simp [occurs])
  | constructor symbol children ih => exact congrArg (1 + ·) (ih agree)
  | nil _ => rfl
  | cons child rest firstIH restIH agreement =>
      have head := firstIH (fun name occursChild => agreement name (by simp [occursMany, occursChild]))
      have tail := restIH (fun name occursRest => agreement name (by simp [occursMany, occursRest]))
      simp only [fragmentsWork, head, tail]

/-- The actual empty or single acyclic source substitution always has a strict finite budget. -/
theorem admissible_binding_budget (problem : Problem Symbol) (admissible : AdmissibleBindings problem) :
    ∃ weight, BindingBudget weight problem.bindings := by
  rcases admissible with empty | ⟨name, fragment, binding, absent, acyclic⟩
  · refine ⟨fun _ => 1, (fun _ => Nat.zero_lt_one), ?_⟩
    intro key context found
    simp [lookup, empty] at found
  · let weight := fun key => if key = name then 1 + fragmentWork (fun _ => 1) fragment else 1
    have sameWork : fragmentWork weight fragment = fragmentWork (fun _ => 1) fragment := by
      apply fragmentWork_congr
      intro key occursKey
      have different : key ≠ name := by
        intro same
        subst key
        rw [acyclic] at occursKey
        cases occursKey
      simp only [weight, ite_eq_right different]
    refine ⟨weight, ?_, ?_⟩
    · intro key
      dsimp only [weight]
      split <;> omega
    · intro key context found
      simp only [binding, lookup, List.find?_cons, List.find?_nil] at found
      split at found
      · rename_i matched
        have keySame : name = key := by simpa using matched
        subst key
        simp only [Option.map_some, Option.some.injEq] at found
        subst context
        simp only [sameWork, weight, ite_true]
        omega
      · cases found

/-- Successful alpha-renaming preserves every context node and its plain structural work. -/
theorem rename_work (names : List (Nat × Nat)) (fuel : Nat) :
    (∀ fragment output : Fragment Symbol, rename names fuel fragment = .ok output →
      fragmentWork (fun _ => 1) output = fragmentWork (fun _ => 1) fragment) ∧
    (∀ children output : List (Fragment Symbol), renameMany names fuel children = .ok output →
      fragmentsWork (fun _ => 1) output = fragmentsWork (fun _ => 1) children) := by
  induction fuel with
  | zero =>
      constructor
      · intro fragment output success; cases success
      · intro children output success
        cases children with
        | nil => cases success; rfl
        | cons first rest => cases success
  | succ fuel ih =>
      constructor
      · intro fragment output success
        cases fragment with
        | var name =>
            cases found : lookup names name with
            | none => simp only [rename, found] at success; cases success
            | some new => simp only [rename, found] at success; cases success; rfl
        | constructor symbol children =>
            simp only [rename] at success
            cases computed : renameMany names fuel children with
            | error error => simp only [computed] at success; cases success
            | ok outputs =>
                simp only [computed, Bind.bind, Except.bind, Pure.pure, Except.pure] at success
                cases success
                exact congrArg (1 + ·) (ih.2 children outputs computed)
      · intro children output success
        cases children with
        | nil => cases success; rfl
        | cons first rest =>
            simp only [renameMany] at success
            cases firstResult : rename names fuel first with
            | error error => simp only [firstResult] at success; cases success
            | ok firstOutput =>
                cases restResult : renameMany names fuel rest with
                | error error => simp only [firstResult, restResult, Bind.bind, Except.bind] at success; cases success
                | ok restOutput =>
                    simp only [firstResult, restResult, Bind.bind, Except.bind, Pure.pure, Except.pure] at success
                    cases success
                    simp only [fragmentsWork, ih.1 first firstOutput firstResult, ih.2 rest restOutput restResult]

end MicroCFTA.SymbolicDriver
