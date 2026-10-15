import MicroCFTA.SourceEqualityPartialMemoBodySound
import MicroCFTA.SourceEqualityPartialMemoRequestProofs

/-!
# Sound completed executions of the actual recursive memo worker

The induction follows the body bound. Check plans contain reached native
word checks and smaller actual child plans. They contain no future cache
soundness assumption. Ready hits use the existing completed-cell invariant.
The result does not assert that a successful execution always exists.
-/
namespace MicroCFTA.SourceEqualityPartialResultMemoProofs
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceObservations SourceSymbolicIndex SourceEqualityClassFoldGraph SourceEqualityNativeScoped
open SourceEqualityPartialMemoWorker SourceEqualityPartialMemoFrame SourceEqualityPartialMemoSound
open SourceEqualityPartialGraphLaws SourceEqualityPartialScope
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- Reached plans inspect only a body that actual demand starts and its smaller recursive calls. -/
def Checked (g e p h c n : Nat) : Nat → SourceEqualityPrecheck.Constraint → Value Symbol Guard →
    SourceEqualityPartialMemoWorker.State width → Prop
  | 0, _, _, _ => True
  | fuel + 1, inherited, value, before =>
      SourceEqualityPartialMemoRequestProofs.Checked (fun _ original state =>
        SourceEqualityPartialMemoBodyLaws.Checked (SourceEqualityPartialMemoWorker.run g e p h c n fuel)
          (Checked g e p h c n fuel) g e p h c n original state) ⟨inherited, value⟩ before

variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol)
local notation "holds" => acceptsConstraint formulas solver

/-- Every successful checked bounded run preserves all cells and the exact contextual public language. -/
theorem run_verified (g e p h c n fuel : Nat) (inherited : SourceEqualityPrecheck.Constraint)
    (value : Value Symbol Guard) (before : SourceEqualityPartialMemoWorker.State width)
    (result : Value Symbol Guard) (after : SourceEqualityPartialMemoWorker.State width)
    (plan : Checked g e p h c n fuel inherited value before)
    (sound : Sound holds ambient before) (scope : Scope before.native)
    (available : Available before.native.machine.heap value) (closed : value.free = [])
    (wellFormed : SourceEqualityDescend.WellFormed inherited)
    (done : SourceEqualityPartialMemoWorker.run g e p h c n fuel inherited value before = .done (.ok result) after) :
    Sound holds ambient after ∧ NodeLaw formulas solver ambient inherited value before.native result after.native := by
  induction fuel generalizing inherited value before result after with
  | zero =>
      apply SourceEqualityPartialMemoRequestProofs.verified formulas solver ambient
        (fun handle original state => .incomplete (.exhausted original handle state)) (fun _ _ _ => True)
        (fun _ _ _ valid => .refl _ valid) ?_ ⟨inherited, value⟩ before result after ?_
        sound scope available closed wellFormed done
      · intro handle original state result after _ _ _ impossible
        cases impossible
      · unfold SourceEqualityPartialMemoRequestProofs.Checked
        dsimp only
        split <;> trivial
  | succ fuel ih =>
      have children : SourceEqualityPartialMemoBodySound.CallbackSound (width := width) formulas solver ambient
          (SourceEqualityPartialMemoWorker.run g e p h c n fuel) (Checked g e p h c n fuel) := by
        intro inherited value before result after plan sound scope available closed wellFormed done
        exact ih inherited value before result after plan sound scope available closed wellFormed done
      exact SourceEqualityPartialMemoRequestProofs.verified formulas solver ambient
        (fun _ => step (SourceEqualityPartialMemoWorker.run g e p h c n fuel) g e p h c n)
        (fun _ original state => SourceEqualityPartialMemoBodyLaws.Checked
          (SourceEqualityPartialMemoWorker.run g e p h c n fuel) (Checked g e p h c n fuel) g e p h c n original state)
        (fun _ original state valid => step_frame _ (run_frame g e p h c n fuel) g e p h c n original state valid)
        (fun handle original state result after plan sound running done scope => by
          have good := sound.cells handle ⟨original, .evaluating⟩ running
          exact SourceEqualityPartialMemoBodySound.step formulas solver ambient children g e p h c n original state result after
            sound scope good.1 good.2.1 good.2.2.1 plan done)
        ⟨inherited, value⟩ before result after plan sound scope available closed wellFormed done

/-- Empty inherited constraints give exact public language while preserving the complete result memo. -/
theorem public_exact (g e p h c n fuel : Nat) (value : Value Symbol Guard)
    (before : SourceEqualityPartialMemoWorker.State width) (result : Value Symbol Guard)
    (after : SourceEqualityPartialMemoWorker.State width)
    (plan : Checked g e p h c n fuel (some []) value before)
    (sound : Sound holds ambient before) (scope : Scope before.native)
    (available : Available before.native.machine.heap value) (closed : value.free = [])
    (done : SourceEqualityPartialMemoWorker.run g e p h c n fuel (some []) value before = .done (.ok result) after) :
    Sound holds ambient after ∧ Scope after.native ∧
      SourceEqualityRequiredCache.Keeps before.native.machine.heap after.native.machine.heap ∧
      Available after.native.machine.heap result ∧ result.free = [] ∧
      ∀ term, InternedGuardedLanguage.meaning holds ambient result term ↔
        InternedGuardedLanguage.meaning holds ambient value term := by
  have wellFormed : SourceEqualityDescend.WellFormed (some []) := by
    intro records same record member
    cases same
    cases member
  have proof := run_verified formulas solver ambient g e p h c n fuel (some []) value before result after
    plan sound scope available closed wellFormed done
  have native := proof.2 scope available closed
  exact ⟨proof.1, native.1, native.2.1, native.2.2.1, native.2.2.2.1,
    fun term => (native.2.2.2.2 term).2 (by simp [SourceEqualityPrecheck.Sat, EqualityNormalize.Satisfies])⟩

end MicroCFTA.SourceEqualityPartialResultMemoProofs
