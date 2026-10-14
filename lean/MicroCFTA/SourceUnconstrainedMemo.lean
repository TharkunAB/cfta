import MicroCFTA.SourceMemoGate

/-!
# The source unconstrained-predicate memo

Canonical identity selects the complete immutable queried record. The memo
returns the exact visited-node source predicate. Misses compute that read
and save it. Constructor-cache growth preserves all earlier saved reads.
-/
namespace MicroCFTA.SourceUnconstrainedMemo
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open SourceObservations SourceSymbolicIndex SourceGuards
open InternedBinderProtocol (NodeRef)

local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula

/-- The source predicate memo retains each immutable input and its Boolean read. -/
abbrev Memo := NodeRef → Option (Value Symbol Guard × Bool)

/-- Every saved Boolean is the concrete source read of its exact resident input. -/
def Correct (state : State Symbol Guard) (memo : Memo) : Prop :=
  ∀ key input answer, memo key = some (input, answer) → input.referenceOf = key ∧
    Available state input ∧ answer = SourceMemoGate.unconstrained input

/-- The initial source predicate memo has no saved reads. -/
def empty : Memo := fun _ => none

/-- The empty predicate memo is coherent in every constructor cache. -/
theorem empty_correct (state : State Symbol Guard) : Correct state empty := by
  intro key input answer found
  cases found

/-- A miss saves the complete queried value and its exact source Boolean. -/
def insert (memo : Memo) (input : Value Symbol Guard) (answer : Bool) : Memo :=
  fun key => if key = input.referenceOf then some (input, answer) else memo key

/-- Execute source predicate memo lookup, concrete crush computation, and insertion. -/
noncomputable def run (input : Value Symbol Guard) (memo : Memo) : Bool × Memo :=
  match memo input.referenceOf with
  | some (_, answer) => (answer, memo)
  | none => let answer := SourceMemoGate.unconstrained input
            (answer, insert memo input answer)

/-- Actual record and reservation growth preserve all saved concrete predicate reads. -/
theorem grows (before after : State Symbol Guard) (growth : Grows before after)
    (history : Extends before.nodes.issued after.nodes.issued) (memo : Memo) (correct : Correct before memo) :
    Correct after memo := by
  intro key input answer found
  obtain ⟨identity, available, actual⟩ := correct key input answer found
  exact ⟨identity, available.grows before after growth history, actual⟩

/-- Every source predicate memo hit or miss gives the exact concrete Boolean and a coherent returned memo. -/
theorem run_exact (input : Value Symbol Guard) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Available state input) (memo : Memo) (correct : Correct state memo) :
    (run input memo).1 = SourceMemoGate.unconstrained input ∧ Correct state (run input memo).2 := by
  cases found : memo input.referenceOf with
  | some pair =>
      rcases pair with ⟨original, answer⟩
      obtain ⟨identity, originalAvailable, actual⟩ := correct _ original answer found
      have same := InternedFreshProbeKeys.resident_reference_injective state coherent original input
        originalAvailable.resident available.resident identity
      subst original
      exact ⟨by simpa only [run, found] using actual, by simpa only [run, found] using correct⟩
  | none =>
      simp only [run, found]
      refine ⟨True.intro, ?_⟩
      intro key original answer selected
      dsimp only [insert] at selected
      split at selected
      · rename_i same
        have fields : input = original ∧ SourceMemoGate.unconstrained input = answer := by
          simpa only [Option.some.injEq, Prod.mk.injEq] using selected
        rcases fields with ⟨rfl, rfl⟩
        exact ⟨same.symm, available, rfl⟩
      · exact correct key original answer selected

end MicroCFTA.SourceUnconstrainedMemo
