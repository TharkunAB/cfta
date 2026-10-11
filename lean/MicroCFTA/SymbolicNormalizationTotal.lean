import MicroCFTA.SymbolicNormalizationWork

/-!
# Total target normalization under finite source substitutions

Bound variables can refer to other bound variables or live names. A strict
binding budget excludes cycles. Every unbound occurrence must have an entry
in the alpha-renaming map. These conditions give explicit successful bounds.
-/
namespace MicroCFTA.SymbolicDriver
open Language
open Symbolic (Fragment Target Obligation)

/-- A variable is safe when it has a binding or belongs to the final live scope. -/
def BoundOrLive (bindings : List (Nat × Fragment Symbol)) (allowed : Nat → Prop) (name : Nat) : Prop :=
  lookup bindings name ≠ none ∨ allowed name

/-- Every substitution context uses only bound variables or final live names. -/
def BindingsScoped (bindings : List (Nat × Fragment Symbol)) (allowed : Nat → Prop) : Prop :=
  ∀ name fragment, lookup bindings name = some fragment → InScope (BoundOrLive bindings allowed) fragment

/-- Complete successful substitution eliminates every bound-variable occurrence from the final scope. -/
theorem inline_scope (bindings : List (Nat × Fragment Symbol)) (allowed : Nat → Prop)
    (bindingsWithin : BindingsScoped bindings allowed) (fuel : Nat) :
    (∀ fragment output, InScope (BoundOrLive bindings allowed) fragment → inline bindings fuel fragment = .ok output → InScope allowed output) ∧
    (∀ children output, (∀ child ∈ children, InScope (BoundOrLive bindings allowed) child) →
      inlineMany bindings fuel children = .ok output → ∀ child ∈ output, InScope allowed child) := by
  induction fuel with
  | zero =>
      constructor
      · intro fragment output _ success; cases success
      · intro children output _ success
        cases children with
        | nil => cases success; intro child member; cases member
        | cons first rest => cases success
  | succ fuel ih =>
      constructor
      · intro fragment output within success
        cases fragment with
        | var name =>
            cases found : lookup bindings name with
            | none =>
                simp only [inline, found] at success
                cases success
                have safe := within name (by simp [occurs])
                have live : allowed name := safe.elim (fun bound => False.elim (bound found)) id
                intro key occurrence
                have same : key = name := by simpa only [occurs, beq_iff_eq] using occurrence
                simpa only [same] using live
            | some context =>
                simp only [inline, found] at success
                exact ih.1 context output (bindingsWithin name context found) success
        | constructor symbol children =>
            simp only [inline] at success
            cases computed : inlineMany bindings fuel children with
            | error error => simp only [computed] at success; cases success
            | ok outputChildren =>
                simp only [computed, Bind.bind, Except.bind, Pure.pure, Except.pure] at success
                cases success
                have scopes := ih.2 children outputChildren (constructor_child_scope _ symbol children within) computed
                clear computed
                intro name occurrence
                change occursMany name outputChildren = true at occurrence
                induction outputChildren with
                | nil => cases occurrence
                | cons child rest tailIH =>
                    have alternatives : occurs name child = true ∨ occursMany name rest = true := by
                      simpa only [occursMany, Bool.or_eq_true] using occurrence
                    rcases alternatives with first | tail
                    · exact scopes child (by simp) name first
                    · exact tailIH (fun value member => scopes value (by simp [member])) tail
      · intro children output within success
        cases children with
        | nil => cases success; intro child member; cases member
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
                    intro child member
                    rcases List.mem_cons.mp member with rfl | member
                    · exact ih.1 first child (within first (by simp)) firstResult
                    · exact ih.2 rest restOutput (fun value present => within value (by simp [present])) restResult child member

/-- A followed target uses only final live names, including when an unbound variable retains its path. -/
theorem follow_scope (bindings : List (Nat × Fragment Symbol)) (allowed : Nat → Prop)
    (bindingsWithin : BindingsScoped bindings allowed) (fuel : Nat) (fragment : Fragment Symbol) (path : List Nat)
    (within : InScope (BoundOrLive bindings allowed) fragment) (output : Target Symbol)
    (success : follow bindings fuel fragment path = .ok (some output)) : InScope allowed output.fragment := by
  induction fuel generalizing fragment path output with
  | zero => cases success
  | succ fuel ih =>
      cases fragment with
      | var name =>
          cases found : lookup bindings name with
          | none =>
              simp only [follow, found] at success
              cases success
              have safe := within name (by simp [occurs])
              have live : allowed name := safe.elim (fun bound => False.elim (bound found)) id
              intro key occurrence
              have same : key = name := by simpa only [occurs, beq_iff_eq] using occurrence
              simpa only [same] using live
          | some context =>
              simp only [follow, found] at success
              exact ih context path (bindingsWithin name context found) output success
      | constructor symbol children =>
          cases path with
          | nil =>
              simp only [follow] at success
              cases computed : inline bindings fuel (.constructor symbol children) with
              | error error => simp only [computed] at success; cases success
              | ok current =>
                  simp only [computed, Bind.bind, Except.bind, Pure.pure, Except.pure] at success
                  cases success
                  exact (inline_scope bindings allowed bindingsWithin fuel).1 (.constructor symbol children) current within computed
          | cons index rest =>
              simp only [follow] at success
              cases found : children[index]? with
              | none => simp only [found] at success; cases success
              | some child =>
                  simp only [found] at success
                  exact ih child rest (constructor_child_scope _ symbol children within child (List.mem_of_getElem? found)) output success

/-- Renaming has an explicit finite bound when every occurring variable has a live-map entry. -/
theorem rename_total (names : List (Nat × Nat)) (fuel : Nat) :
    (∀ fragment : Fragment Symbol,
      InScope (fun name => ∃ new, lookup names name = some new) fragment →
      2 * fragmentWork (fun _ => 1) fragment ≤ fuel → ∃ output, rename names fuel fragment = .ok output) ∧
    (∀ children : List (Fragment Symbol),
      (∀ child ∈ children, InScope (fun name => ∃ new, lookup names name = some new) child) →
      2 * fragmentsWork (fun _ => 1) children + 1 ≤ fuel → ∃ output, renameMany names fuel children = .ok output) := by
  induction fuel with
  | zero =>
      constructor
      · intro fragment _ bounded
        have positive := fragmentWork_positive (fun _ => 1) (fun _ => Nat.zero_lt_one) fragment
        omega
      · intro children _ bounded; omega
  | succ fuel ih =>
      constructor
      · intro fragment within bounded
        cases fragment with
        | var name =>
            obtain ⟨new, found⟩ := within name (by simp [occurs])
            exact ⟨.var new, by simp only [rename, found]⟩
        | constructor symbol children =>
            have bound : 2 * fragmentsWork (fun _ => 1) children + 1 ≤ fuel := by
              simp only [fragmentWork] at bounded
              omega
            obtain ⟨output, success⟩ := ih.2 children (constructor_child_scope _ symbol children within) bound
            exact ⟨.constructor symbol output, by simp only [rename, success]; rfl⟩
      · intro children within bounded
        cases children with
        | nil => exact ⟨[], rfl⟩
        | cons first rest =>
            have positive := fragmentWork_positive (fun _ => 1) (fun _ => Nat.zero_lt_one) first
            have firstBound : 2 * fragmentWork (fun _ => 1) first ≤ fuel := by
              simp only [fragmentsWork] at bounded
              omega
            have restBound : 2 * fragmentsWork (fun _ => 1) rest + 1 ≤ fuel := by
              simp only [fragmentsWork] at bounded
              omega
            obtain ⟨firstOutput, firstResult⟩ := ih.1 first (within first (by simp)) firstBound
            obtain ⟨restOutput, restResult⟩ := ih.2 rest (fun child member => within child (by simp [member])) restBound
            exact ⟨firstOutput :: restOutput, by simp only [renameMany, firstResult, restResult]; rfl⟩

/-- Target normalization succeeds at a concrete bound under the source substitution and scope invariants. -/
theorem normalizeTarget_total (weight : Nat → Nat) (problem : Problem Symbol) (names : List (Nat × Nat))
    (budget : BindingBudget weight problem.bindings)
    (bindingsWithin : BindingsScoped problem.bindings (fun name => ∃ new, lookup names name = some new))
    (target : Target Symbol)
    (within : InScope (BoundOrLive problem.bindings (fun name => ∃ new, lookup names name = some new)) target.fragment)
    (fuel : Nat) (bounded : 2 * targetWork weight target + 1 ≤ fuel) :
    ∃ output, normalizeTarget fuel problem names target = .ok output := by
  have followBound : 2 * fragmentWork weight target.fragment + target.path.length + 1 ≤ fuel := by
    unfold targetWork at bounded
    omega
  obtain ⟨result, followed⟩ := follow_total weight problem.bindings budget fuel target.fragment target.path followBound
  cases result with
  | none => exact ⟨none, by simp only [normalizeTarget, followed]; rfl⟩
  | some current =>
      have currentScope := follow_scope problem.bindings _ bindingsWithin fuel target.fragment target.path within current followed
      have currentWork := follow_work weight problem.bindings budget fuel target.fragment target.path current followed
      have renameBound : 2 * fragmentWork (fun _ => 1) current.fragment ≤ fuel := by
        unfold targetWork at bounded currentWork
        omega
      obtain ⟨renamed, success⟩ := (rename_total names fuel).1 current.fragment currentScope renameBound
      exact ⟨some ⟨renamed, current.path⟩, by simp only [normalizeTarget, followed, success, Bind.bind, Except.bind]; rfl⟩

/-- Every well-scoped source obligation normalizes successfully at an explicit work bound. -/
theorem normalizeObligation_total [DecidableEq Symbol] [Ord Symbol]
    (weight : Nat → Nat) (problem : Problem Symbol) (names : List (Nat × Nat))
    (budget : BindingBudget weight problem.bindings)
    (bindingsWithin : BindingsScoped problem.bindings (fun name => ∃ new, lookup names name = some new))
    (requirement : Obligation Symbol)
    (within : ObligationInScope (BoundOrLive problem.bindings (fun name => ∃ new, lookup names name = some new)) requirement)
    (fuel : Nat) (bounded : 2 * obligationWork weight requirement + 1 ≤ fuel) :
    ∃ output, normalizeObligation fuel problem names requirement = .ok output := by
  cases requirement with
  | «exists» target =>
      obtain ⟨output, success⟩ := normalizeTarget_total weight problem names budget bindingsWithin target within fuel bounded
      exact ⟨output.map required, by simp only [normalizeObligation, success]; rfl⟩
  | equal left right =>
      have leftBound : 2 * targetWork weight left + 1 ≤ fuel := by
        simp only [obligationWork] at bounded
        omega
      have rightBound : 2 * targetWork weight right + 1 ≤ fuel := by
        simp only [obligationWork] at bounded
        omega
      obtain ⟨first, firstResult⟩ := normalizeTarget_total weight problem names budget bindingsWithin left within.1 fuel leftBound
      obtain ⟨second, secondResult⟩ := normalizeTarget_total weight problem names budget bindingsWithin right within.2 fuel rightBound
      simp only [normalizeObligation, firstResult, secondResult, Bind.bind, Except.bind]
      cases first with
      | none => exact ⟨none, rfl⟩
      | some a =>
          cases second with
          | none => exact ⟨none, rfl⟩
          | some b =>
              dsimp only
              split
              · exact ⟨some (required a), rfl⟩
              · split
                · exact ⟨some [.equal b a], rfl⟩
                · exact ⟨some [.equal a b], rfl⟩

/-- A finite pure traversal succeeds when every visited action succeeds. -/
theorem pure_mapM_total (action : Input → Except Failure Output) (inputs : List Input)
    (total : ∀ input ∈ inputs, ∃ output, action input = .ok output) :
    ∃ outputs, inputs.mapM action = .ok outputs := by
  induction inputs with
  | nil => exact ⟨[], rfl⟩
  | cons first rest ih =>
      obtain ⟨head, firstResult⟩ := total first (by simp)
      obtain ⟨tail, restResult⟩ := ih (fun input member => total input (by simp [member]))
      exact ⟨head :: tail, by simp only [List.mapM_cons, firstResult, restResult]; rfl⟩

/-- Each pending requirement is bounded by the total pending work. -/
theorem obligationWork_member (weight : Nat → Nat) (requirements : List (Obligation Symbol))
    (requirement : Obligation Symbol) (member : requirement ∈ requirements) :
    obligationWork weight requirement ≤ obligationsWork weight requirements := by
  induction requirements with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · simp only [obligationsWork, List.map_cons, List.sum_cons]; omega
      · have smaller := ih member
        simp only [obligationsWork, List.map_cons, List.sum_cons]
        unfold obligationsWork at smaller
        omega

/-- The complete source normalizer has a successful finite bound under explicit substitution and name-scope invariants. -/
theorem normalize_total [DecidableEq Symbol] [Ord Symbol]
    (weight : Nat → Nat) (problem : Problem Symbol) (budget : BindingBudget weight problem.bindings)
    (bindingsWithin : BindingsScoped problem.bindings (fun name => ∃ new,
      lookup (problem.domains.zipIdx.map fun (entry, index) => (entry.1, index)) name = some new))
    (within : ∀ requirement ∈ problem.obligations,
      ObligationInScope (BoundOrLive problem.bindings (fun name => ∃ new,
        lookup (problem.domains.zipIdx.map fun (entry, index) => (entry.1, index)) name = some new)) requirement)
    (fuel : Nat) (bounded : 2 * obligationsWork weight problem.obligations + 1 ≤ fuel) :
    ∃ output, normalize fuel problem = .ok output := by
  let names := problem.domains.zipIdx.map fun (entry, index) => (entry.1, index)
  obtain ⟨pending, successes⟩ := pure_mapM_total (normalizeObligation fuel problem names) problem.obligations (by
    intro requirement member
    have requirementBound := obligationWork_member weight problem.obligations requirement member
    exact normalizeObligation_total weight problem names budget bindingsWithin requirement (within requirement member) fuel (by omega))
  dsimp only [names] at successes
  simp only [normalize, successes, Bind.bind, Except.bind]
  split
  · exact ⟨none, rfl⟩
  · exact ⟨some _, rfl⟩

end MicroCFTA.SymbolicDriver
