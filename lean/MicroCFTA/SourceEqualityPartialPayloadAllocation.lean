import MicroCFTA.SourceEqualityConstraintMemoAllocation
import MicroCFTA.SourceEqualityPartialAllocationFrame

/-!
# Actual inherited constructor receipts before a child request

The caller combines inherited and own constraints. Contradiction makes no
child request. A live result descends at the selected child index. Both
operations retain their completed caches and actual allocation receipts.
These effects preserve the existing recursive result-memo invariant.
-/
namespace MicroCFTA.SourceEqualityPartialPayloadAllocation
open SourceEqualityConstraintAllocation
open SourceEqualityConstraintMemoAllocation (State Valid Grows)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Complete the source inherited constructor prefix for one demanded child, or retain contradiction. -/
noncomputable def childInheritance (inherited own : Value) (index : Nat) (before : State) : Except String (Option Value) × State :=
  let combined := SourceEqualityConstraintMemoAllocation.combine inherited own before
  match combined.1 with
  | .error message => (.error message, combined.2)
  | .ok .contradiction => (.ok none, combined.2)
  | .ok parent =>
      let child := SourceEqualityConstraintMemoAllocation.descend parent index combined.2
      (.ok (some child.1), child.2)

/-- Actual inherited constructor execution derives exact physical output and a complete allocation receipt. -/
theorem childInheritance_correct (inherited own : Value) (index : Nat) (before : State) (valid : Valid before)
    (inheritedReady : Ready before.constraints inherited) (ownReady : Ready before.constraints own) :
    ∃ result, (childInheritance inherited own index before).1 = .ok result ∧
      Valid (childInheritance inherited own index before).2 ∧
      (∀ value, result = some value → Ready (childInheritance inherited own index before).2.constraints value) ∧
      (match result with
      | none => SourceEqualityInheritedPayload.combine inherited.payload own.payload = .ok none
      | some value => ∃ records, SourceEqualityInheritedPayload.combine inherited.payload own.payload = .ok (some records) ∧
          value.payload = SourceEqualityDescend.descend (some records) index) ∧
      Grows before (childInheritance inherited own index before).2 := by
  obtain ⟨parent, combined, combinedValid, parentReady, parentExact, parentGrows⟩ :=
    SourceEqualityConstraintMemoAllocation.combine_correct inherited own before valid inheritedReady ownReady
  cases parent with
  | contradiction =>
      have actual : childInheritance inherited own index before =
          (.ok none, (SourceEqualityConstraintMemoAllocation.combine inherited own before).2) := by
        simp only [childInheritance, combined]
      rw [actual]
      refine ⟨none, rfl, combinedValid, ?_, parentExact, parentGrows⟩
      intro value impossible
      cases impossible
  | live identity records =>
      have child := SourceEqualityConstraintMemoAllocation.descend_correct (.live identity records) index
        (SourceEqualityConstraintMemoAllocation.combine inherited own before).2 combinedValid parentReady
      have actual : childInheritance inherited own index before =
          (.ok (some (SourceEqualityConstraintMemoAllocation.descend (.live identity records) index
            (SourceEqualityConstraintMemoAllocation.combine inherited own before).2).1),
            (SourceEqualityConstraintMemoAllocation.descend (.live identity records) index
              (SourceEqualityConstraintMemoAllocation.combine inherited own before).2).2) := by
        simp only [childInheritance, combined]
      rw [actual]
      refine ⟨_, rfl, child.1, ?_, ⟨records, parentExact, child.2.2.1⟩, ?_⟩
      · intro value same
        cases same
        exact child.2.1
      · exact ⟨steps_trans parentGrows.constraints child.2.2.2.constraints,
          Cache.extends_trans parentGrows.combinations child.2.2.2.combinations,
          Cache.extends_trans parentGrows.descents child.2.2.2.descents⟩

/-- The actual constructor prefix preserves every original result cell and its current semantic proof. -/
theorem childInheritance_sound (holds : Guard → Language.Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (inherited own : Value) (index : Nat) (before : State) (valid : Valid before)
    (inheritedReady : Ready before.constraints inherited) (ownReady : Ready before.constraints own)
    (worker : SourceEqualityPartialMemoWorker.State width)
    (same : worker.constraints = before.constraints) (sound : SourceEqualityPartialMemoSound.Sound holds ambient worker) :
    SourceEqualityPartialMemoSound.Sound holds ambient
      {worker with constraints := (childInheritance inherited own index before).2.constraints} ∧
      SourceEqualityPartialMemoFrame.Frame (SourceEqualityPartialMemoFrame.stateTables worker)
        (SourceEqualityPartialMemoFrame.stateTables {worker with constraints := (childInheritance inherited own index before).2.constraints}) := by
  obtain ⟨_, _, _, _, _, growth⟩ := childInheritance_correct inherited own index before valid inheritedReady ownReady
  have steps : Cache.Steps worker.constraints (childInheritance inherited own index before).2.constraints := by
    simpa only [same] using growth.constraints
  exact ⟨SourceEqualityPartialAllocationFrame.steps_sound holds ambient worker _ sound steps,
    SourceEqualityPartialAllocationFrame.steps_frame worker _ sound.valid steps⟩

/-- A successful inherited constructor prefix supplies the actual child memo key without another allocation. -/
theorem childInheritance_prepare (inherited own : Value) (index : Nat) (before : State) (valid : Valid before)
    (inheritedReady : Ready before.constraints inherited) (ownReady : Ready before.constraints own)
    (child : Value) (done : (childInheritance inherited own index before).1 = .ok (some child))
    (node : InternedConstructorTemplates.Value Symbol Guard) (worker : SourceEqualityPartialMemoWorker.State width) :
    let after := {worker with constraints := (childInheritance inherited own index before).2.constraints}
    SourceEqualityPartialMemoWorker.prepare ⟨child.payload, node⟩ after = ((child.identity, node.referenceOf), after) := by
  obtain ⟨result, actual, _, ready, _, _⟩ := childInheritance_correct inherited own index before valid inheritedReady ownReady
  have same : result = some child := Except.ok.inj (actual.symm.trans done)
  exact SourceEqualityPartialAllocationFrame.prepare_stored child node _ (ready child same).1

/-- Actual constructor receipts retain inherited satisfaction at every existing selected child. -/
theorem childInheritance_sat (inherited own : Value) (index : Nat) (before : State) (valid : Valid before)
    (inheritedReady : Ready before.constraints inherited) (ownReady : Ready before.constraints own)
    (symbol : OtherSymbol) (children : List (Language.Term OtherSymbol)) (term : Language.Term OtherSymbol)
    (found : children[index]? = some term)
    (inheritedSat : SourceEqualityPrecheck.Sat (.node symbol children) inherited.payload)
    (ownSat : SourceEqualityPrecheck.Sat (.node symbol children) own.payload) :
    ∃ child, (childInheritance inherited own index before).1 = .ok (some child) ∧
      Ready (childInheritance inherited own index before).2.constraints child ∧ SourceEqualityPrecheck.Sat term child.payload := by
  obtain ⟨result, actual, _, ready, exact, _⟩ := childInheritance_correct inherited own index before valid inheritedReady ownReady
  cases result with
  | none =>
      have falsehood := ((SourceEqualityInheritedPayload.combine_exact exact).2 (.node symbol children)).mpr ⟨inheritedSat, ownSat⟩
      exact False.elim falsehood
  | some child =>
      obtain ⟨records, combined, descended⟩ := exact
      exact ⟨child, actual, ready child rfl, descended ▸ SourceEqualityInheritedPayload.combined_child combined symbol children index term found inheritedSat ownSat⟩

end MicroCFTA.SourceEqualityPartialPayloadAllocation
