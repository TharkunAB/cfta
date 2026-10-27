import MicroCFTA.SourceEqualityNativeDemand

/-!
# Operation-cache invariants for actual native demand

Current normalized source fields derive successful load readiness. Every
body outcome retains valid operation caches and actual allocation receipts.
Finite execution requires normalized fields only at reached controls.
No future validity or semantic cache answer is assumed.
-/
namespace MicroCFTA.SourceEqualityNativeDemandOperations
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
open SourceEqualityConstraintMemoAllocation (Valid Grows)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq

/-- Every checked-body observation retains the complete native state. -/
theorem body_native (request : EdgeRequest Symbol Guard) (next : EdgeValue Symbol Guard → Code Symbol Guard Output)
    (state : State width) : (body request next state).state.native = state.native := by
  unfold body
  split
  · rfl
  · split
    · rfl
    · rfl
    · split
      · rfl
      · rfl
      · dsimp only
        split <;> rfl

private theorem grows_trans {before middle after : SourceEqualityConstraintMemoAllocation.State}
    (first : Grows before middle) (second : Grows middle after) : Grows before after :=
  ⟨SourceEqualityConstraintAllocation.steps_trans first.constraints second.constraints,
    Cache.extends_trans first.combinations second.combinations, Cache.extends_trans first.descents second.descents⟩

/-- Sentinel continuation retains its actual empty-field allocation receipt. -/
theorem sentinel_operations (request : EdgeRequest Symbol Guard) (next : EdgeValue Symbol Guard → Code Symbol Guard Output)
    (state : State width) (valid : Valid state.operations) :
    Valid (sentinel request next state).state.operations ∧ Grows state.operations (sentinel request next state).state.operations := by
  have checked := SourceEqualityMkEdgeAllocation.emptyField_correct state.operations valid
  exact ⟨checked.1, checked.2.1⟩

/-- Current normalized request fields suffice for all checked-body operation effects. -/
theorem body_operations (request : EdgeRequest Symbol Guard) (next : EdgeValue Symbol Guard → Code Symbol Guard Output)
    (state : State width) (valid : Valid state.operations)
    (leftCached : SourceEqualityGuardReadback.Cached request.left.entry.key.constraint.equalities)
    (rightCached : SourceEqualityGuardReadback.Cached request.right.entry.key.constraint.equalities) :
    Valid (body request next state).state.operations ∧ Grows state.operations (body request next state).state.operations := by
  by_cases mismatch : request.left.children.length ≠ request.right.children.length
  · rw [body_mismatch request next state mismatch]
    exact sentinel_operations request next state valid
  · simp only [body, ite_eq_right mismatch]
    cases firstFound : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint state.operations.constraints with
    | error message => exact ⟨valid, SourceEqualityConstraintMemoAllocation.grows_refl _⟩
    | ok first =>
        cases first with
        | none => exact ⟨valid, SourceEqualityConstraintMemoAllocation.grows_refl _⟩
        | some first =>
            cases secondFound : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint state.operations.constraints with
            | error message => exact ⟨valid, SourceEqualityConstraintMemoAllocation.grows_refl _⟩
            | ok second =>
                cases second with
                | none => exact ⟨valid, SourceEqualityConstraintMemoAllocation.grows_refl _⟩
                | some second =>
                    have firstReady := (SourceEqualityConstraintFieldLookup.load_ready _ _ valid.constraints leftCached first firstFound).1
                    have secondReady := (SourceEqualityConstraintFieldLookup.load_ready _ _ valid.constraints rightCached second secondFound).1
                    obtain ⟨branch, done, _, afterValid, growth, _⟩ := SourceEqualityIntersectionEdgeAllocation.run_correct
                      GuardStructuralOrder.le first second request.left.children.length request.right.children.length state.operations
                      valid firstReady secondReady
                    simp only [done]
                    cases branch with
                    | mismatch | rejected =>
                        have empty := SourceEqualityMkEdgeAllocation.emptyField_correct _ afterValid
                        exact ⟨empty.1, grows_trans growth empty.2.1⟩
                    | ready combined => exact ⟨afterValid, growth⟩

/-- Only an actual edge-body control reads normalized original fields. -/
def Fields : Control Output → Prop
  | .code _ => True
  | .edgeBody request _ =>
      SourceEqualityGuardReadback.Cached request.left.entry.key.constraint.equalities ∧
      SourceEqualityGuardReadback.Cached request.right.entry.key.constraint.equalities

/-- Lifting any ordinary native outcome preserves the entire operation state. -/
theorem lift_operations (operations : SourceEqualityConstraintMemoAllocation.State)
    (outcome : SourceRecursiveIntersectionNative.Outcome width Symbol Guard Output) :
    (lift operations outcome).state.operations = operations := by cases outcome <;> rfl

/-- Ordinary code, including edge publication and demand, does not change operation caches. -/
theorem step_code_operations [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (code : Code Symbol Guard Output) (state : State width) :
    (step (.code code) state).state.operations = state.operations := by
  cases code <;> dsimp only [step]
  all_goals try exact lift_operations _ _
  all_goals split <;> rfl

/-- One actual step preserves valid growing operations from current normalized fields alone. -/
theorem step_operations [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control : Control Output) (state : State width) (valid : Valid state.operations) (fields : Fields control) :
    Valid (step control state).state.operations ∧ Grows state.operations (step control state).state.operations := by
  cases control with
  | code code =>
      rw [step_code_operations code state]
      exact ⟨valid, SourceEqualityConstraintMemoAllocation.grows_refl _⟩
  | edgeBody request next => exact body_operations request next state valid fields.1 fields.2

/-- Normalized original fields are required only on the actual reached control path. -/
noncomputable def FieldsThrough [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] :
    Nat → Control Output → State width → Prop
  | 0, control, _ => Fields control
  | fuel + 1, control, state =>
      Fields control ∧ match step control state with
      | .yielded next after => FieldsThrough fuel next after
      | .done _ _ | .failed _ _ | .constraintError _ _ | .blocked _ _ _ => True

/-- Every finite actual execution retains valid operation caches and complete atomic allocation receipts. -/
theorem execute_operations [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control : Control Output) (state : State width) (valid : Valid state.operations)
    (fields : FieldsThrough fuel control state) :
    Valid (execute fuel control state).state.operations ∧ Grows state.operations (execute fuel control state).state.operations := by
  induction fuel generalizing control state with
  | zero => exact ⟨valid, SourceEqualityConstraintMemoAllocation.grows_refl _⟩
  | succ fuel ih =>
      have one := step_operations control state valid fields.1
      cases observed : step control state with
      | yielded next after =>
          have nextFields : FieldsThrough fuel next after := by simpa only [observed] using fields.2
          have checked : Valid after.operations ∧ Grows state.operations after.operations := by
            simpa only [observed, Outcome.state] using one
          have rest := ih next after checked.1 nextFields
          simpa only [execute, observed] using And.intro rest.1 (grows_trans checked.2 rest.2)
      | done | failed | constraintError | blocked =>
          simpa only [execute, observed, Outcome.state] using one

/-- Finite native demand derives the full interner trace without a future-state validity assumption. -/
theorem execute_constraint_steps [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control : Control Output) (state : State width) (valid : Valid state.operations)
    (fields : FieldsThrough fuel control state) :
    Cache.Steps state.operations.constraints (execute fuel control state).state.operations.constraints :=
  (execute_operations fuel control state valid fields).2.constraints

end MicroCFTA.SourceEqualityNativeDemandOperations
