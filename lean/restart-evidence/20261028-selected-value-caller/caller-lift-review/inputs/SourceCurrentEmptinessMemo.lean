import MicroCFTA.SourceCurrentEmptinessDecision

/-!
# The separate completed conservative-emptiness memo

This table is a fourth memo family. It does not replace the unfolding,
predicate, or descendant tables. Misses execute an actual current decision.
Hits retain the entire native state. The invariant proves conservative
answers and the open-input result. It does not assert exact Boolean
completeness or model pending GHC memo thunks and publication.
-/
namespace MicroCFTA.SourceCurrentEmptinessMemo
open Language InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredCache SourceEqualityNativeScoped
open InternedGuardedLanguage (meaning)
open InternedBinderProtocol (NodeRef)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Value" => InternedConstructorTemplates.Value Symbol Guard
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin

/-- The emptiness table retains its complete immutable queried record. -/
abbrev Memo := NodeRef → Option (Value × Bool)

/-- Each stored answer rejects open queries and soundly certifies true answers. -/
def AnswerSound (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (input : Value) (answer : Bool) : Prop :=
  (input.free ≠ [] → answer = false) ∧
    (answer = true → ∀ ambient term, ¬meaning (SourceEqualityPCSGuard.holds formulas solver) ambient input term)

/-- Every completed entry has its actual physical key and conservative semantic law. -/
def Correct (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (heap : State Symbol Guard) (memo : Memo) : Prop :=
  ∀ key input answer, memo key = some (input, answer) →
    input.referenceOf = key ∧ Available heap input ∧ AnswerSound formulas solver input answer

/-- The initial emptiness table has no entries. -/
def empty : Memo := fun _ => none

/-- The empty table is coherent in every physical heap. -/
theorem empty_correct (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (heap : State Symbol Guard) :
    Correct formulas solver heap empty := by
  intro key input answer found
  cases found

/-- A completed miss saves the actual queried record and result. -/
def insert (memo : Memo) (input : Value) (answer : Bool) : Memo :=
  fun key => if key = input.referenceOf then some (input, answer) else memo key

/-- Earlier completed entries retain their exact input records and answers. -/
def Extends (before after : Memo) : Prop :=
  ∀ key entry, before key = some entry → after key = some entry

/-- Physical heap history preserves every earlier immutable semantic memo law. -/
theorem grows (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) {before after : State Symbol Guard}
    (keeps : Keeps before after) (memo : Memo) (correct : Correct formulas solver before memo) :
    Correct formulas solver after memo := by
  intro key input answer found
  obtain ⟨identity, available, sound⟩ := correct key input answer found
  exact ⟨identity, keeps.available input available, sound⟩

/-- Lookup precedes the initial free-list test; only misses execute the body. -/
inductive Call [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat} :
    Memo → Value → Native width Symbol Guard → Bool → Native width Symbol Guard → Memo → Prop where
  | hit (found : memo query.referenceOf = some (original, answer)) : Call memo query before answer before memo
  | miss (absent : memo query.referenceOf = none)
      (actual : SourceCurrentEmptinessDecision.Decision query before answer after) :
      Call memo query before answer after (insert memo query answer)

/-- Every actual body receipt derives the law retained by completed memo entries. -/
theorem answer_sound [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {query : Value} {before after : Native width Symbol Guard} {answer : Bool}
    (actual : SourceCurrentEmptinessDecision.Decision query before answer after)
    (ready : IdleReady top conjoin before) (fields : SourceEqualityNativeDemandFieldHeap.Heap before.machine.heap)
    (available : Available before.machine.heap query) : AnswerSound formulas solver query answer := by
  constructor
  · intro notClosed
    exact (SourceCurrentEmptinessDecision.open_no_work actual notClosed).1
  · intro same
    subst answer
    intro ambient
    exact SourceCurrentEmptinessDecision.sound formulas solver ambient actual ready fields available

/-- A completed lookup or actual miss preserves valid entries and all earlier answers. -/
theorem verified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {query : Value} {before after : Native width Symbol Guard} {answer : Bool} {memo saved : Memo}
    (call : Call memo query before answer after saved) (ready : IdleReady top conjoin before)
    (fields : SourceEqualityNativeDemandFieldHeap.Heap before.machine.heap)
    (available : Available before.machine.heap query) (correct : Correct formulas solver before.machine.heap memo) :
    IdleReady top conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧
      SourceEqualityNativeDemandFieldHeap.Heap after.machine.heap ∧
      Correct formulas solver after.machine.heap saved ∧ AnswerSound formulas solver query answer ∧ Extends memo saved := by
  cases call with
  | hit found =>
      obtain ⟨identity, originalAvailable, sound⟩ := correct _ _ _ found
      have same := InternedFreshProbeKeys.resident_reference_injective before.machine.heap
        ready.semantic.ready.semantic.1.normal.facts.coherent _ query
        originalAvailable.resident available.resident identity
      subst_vars
      exact ⟨ready, pure_keeps _ ready.semantic.ready, fields, correct, sound, fun _ _ found => found⟩
  | miss absent actual =>
      have effects := SourceCurrentEmptinessDecision.effects actual ready fields
      have sound := answer_sound formulas solver actual ready fields available
      have old := grows formulas solver effects.2.1 memo correct
      refine ⟨effects.1, effects.2.1, effects.2.2, ?_, sound, ?_⟩
      · intro key original result found
        dsimp only [insert] at found
        split at found
        · rename_i same
          have pair : query = original ∧ answer = result := by
            simpa only [Option.some.injEq, Prod.mk.injEq] using found
          rcases pair with ⟨rfl, rfl⟩
          exact ⟨same.symm, effects.2.1.available query available, sound⟩
        · exact old key original result found
      · intro key entry found
        have different : key ≠ query.referenceOf := by
          intro same
          subst key
          rw [absent] at found
          cases found
        simp only [insert, different, ↓reduceIte, found]

end MicroCFTA.SourceCurrentEmptinessMemo
