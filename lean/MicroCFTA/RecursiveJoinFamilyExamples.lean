import MicroCFTA.RecursiveJoinQuery
import MicroCFTA.RecursiveNaryExamples

/-!
# Concrete heterogeneous joins inside mutual recursive families

Two keys recurse through exact JoinN terms. The argument chain mixes Bool
and Nat. A nullary join occurs inside an argument. Flat choices retain key
masses nine and one after two recursive steps.
-/
namespace MicroCFTA.RecursiveJoinFamilyExamples
open Language GeneratorCombinators IntegerTermViews SizedRank
open RecursiveCallbackTermination
open RecursiveJoinBodyFields
open RecursiveJoinInverse
open RecursiveNaryExamples (pureCallbacks pure_exact)

/-- Pure operands retain their independent finite callback. -/
def pureBody (value : Value) (symbol : Nat) : CheckedBody Bool Nat Nat Value :=
  ofNary pureCallbacks (.finite (.pure (value, .node (.user symbol) []))) (pure_exact _)

/-- Retained alternatives can assign different masses to identical user values. -/
def retained (mass : Rat) (positive : 0 < mass) : CheckedBody Bool Nat Nat Nat :=
  ofNary pureCallbacks (.retained (fun _ => mass) (fun _ => positive) (.pure (0, .node .pure []))) (pure_exact _)

/-- A recursive occurrence reads the selected key without a finite callback premise. -/
def occurrence (key : Bool) : CheckedBody Bool Nat Nat Nat :=
  ofNary pureCallbacks (.occurrence key) True.intro

/-- The Bool operand itself uses the nullary JoinN branch. -/
def flag : CheckedBody Bool Nat Nat Bool := join 7 (pureBody true 1) .nil

/-- The source operation consumes different types at the two argument positions. -/
def operation : CheckedBody Bool Nat Nat (Bool → Nat → Nat) :=
  pureBody (fun flag value => if flag then value + 1 else value) 20

/-- A flat branch can contain a labelled heterogeneous join with a mutual call. -/
def branches : Fin 3 → CheckedBody Bool Nat Nat Nat
  | ⟨0, _⟩ => retained 9 (by decide)
  | ⟨1, _⟩ => retained 1 (by decide)
  | ⟨2, _⟩ => label 10 (join 5 operation (.cons flag (.cons (occurrence true) .nil)))

/-- Both recursion directions construct the private source JoinN wrappers. -/
def program : Bool → CheckedBody Bool Nat Nat Nat
  | false => nary 3 branches
  | true => label 11 (join 6 (pureBody Nat.succ 21) (.cons (occurrence false) .nil))

/-- Source key codes remain distinct at the family boundary. -/
def code (key : Bool) : Nat := if key then 1 else 0

def keys : List Bool := [false, true]

theorem complete (key : Bool) : key ∈ keys := by cases key <;> simp [keys]

/-- A pure finite callback has one valid candidate or none in every view. -/
theorem pure_candidates (entry : Value × EngineTerm Nat) :
    KeyedNaryFields.LeavesBounded pureCallbacks (KeyedNaryAlignment.Recipe.finite (Key := Bool) (Root := Nat) (.pure entry)) ∧
    KeyedNaryFields.LeavesOrdered pureCallbacks (KeyedNaryAlignment.Recipe.finite (Key := Bool) (Root := Nat) (.pure entry)) ∧
    KeyedNaryFields.LeavesDistinct pureCallbacks (KeyedNaryAlignment.Recipe.finite (Key := Bool) (Root := Nat) (.pure entry)) := by
  constructor
  · intro view wanted row member
    simp only [RecursiveCallbackAlignment.finite, pureCallbacks] at member
    split at member
    · have same := List.mem_singleton.mp member
      subst row
      simp [RecursiveCallbackAlignment.finite, FiniteSource.classMembers]
    · simp at member
  · constructor
    · intro view wanted
      simp only [RecursiveCallbackAlignment.finite, pureCallbacks]
      split <;> simp
    · intro view wanted
      simp only [RecursiveCallbackAlignment.finite, pureCallbacks]
      split <;> simp [RecursiveCallbackDistinct.Distinct]

/-- The concrete mutual program supplies all false-row, order, and distinctness obligations locally. -/
theorem candidates : ∀ key, (program key).candidates := by
  intro key
  cases key with
  | false =>
      intro ⟨index, within⟩
      have cases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
      rcases cases with rfl | rfl | rfl
      · exact pure_candidates (0, .node .pure [])
      · exact pure_candidates (0, .node .pure [])
      · exact ⟨pure_candidates _, ⟨⟨pure_candidates _, True.intro⟩, ⟨⟨True.intro, True.intro, True.intro⟩, True.intro⟩⟩⟩
  | true => exact ⟨pure_candidates _, ⟨⟨True.intro, True.intro, True.intro⟩, True.intro⟩⟩

/-- Actual value guards accept both bodies without an assumed recursive minimum. -/
theorem accepted : Guarded keys complete program := by
  intro key
  cases key <;> simp [program, branches, label, nary, RecursiveJoinComposition.nary,
    RecursiveJoinComposition.alternatives, RecursiveJoinComposition.choice, RecursiveJoinComposition.map,
    RecursiveJoinComposition.label, RecursiveJoinComposition.pay, RecursiveJoinFamily.valueProgram,
    lower, retained, ofNary, RecursiveJoinComposition.ofNary, KeyedNaryAlignment.valueRecipe,
    KeyedSource.guarded]

/-- A nullary join still retains its center operation and empty key forest. -/
def flagTerm : EngineTerm Nat := SupportJoin.joinTerm 7 (.node (.user 1) []) []

/-- The first mutual step keeps the base branch number inside the nested key boundary. -/
def firstTerm : EngineTerm Nat := KeyedTermBoundary.atKeyTerm 1
  (SupportTerms.labelTerm 11 (SupportJoin.joinTerm 6 (.node (.user 21) [])
    [KeyedTermBoundary.atKeyTerm 0 (.node (.choice 0) [.node .pure []])]))

/-- The second recursive step retains heterogeneous argument order and both join components. -/
def delayedTerm : EngineTerm Nat := KeyedTermBoundary.atKeyTerm 0
  (.node (.choice 2) [SupportTerms.labelTerm 10 (SupportJoin.joinTerm 5 (.node (.user 20) []) [flagTerm, firstTerm])])

/-- The compiled independent term family contains the full nested JoinN tree. -/
theorem delayed_select :
    Decoder.decode (KeyedSource.family (RecursiveJoinFamily.termProgram code (lower program)) 2 false).members.plan 0 =
      some delayedTerm := by cbv

/-- Full family callback recursion returns the original shared source rank in every view. -/
theorem delayed_inverse :
    positions code program false .whole [delayedTerm] = [(⟨2, 0⟩, true)] ∧
    positions code program false .labelled [delayedTerm] = [(⟨2, 0⟩, true)] ∧
    positions code program false .spine [delayedTerm] = [(⟨2, 0⟩, true)] := by cbv

/-- Recursion preserves retained key masses and their complete rank probabilities. -/
theorem delayed_mass :
    (KeyedSource.family (RecursiveJoinFamily.valueProgram (lower program)) 2 false).mass = 10 ∧
    (KeyedSource.family (RecursiveJoinFamily.valueProgram (lower program)) 2 false).members.sampling.ranked =
      [(9 / 10, (0, 2)), (1 / 10, (1, 2))] := by cbv <;> decide

/-- Wrong inner join keys preserve the unchecked candidate before replay filtering. -/
def wrongComponent : EngineTerm Nat := KeyedTermBoundary.atKeyTerm 0
  (.node (.choice 2) [SupportTerms.labelTerm 10 (SupportJoin.joinTerm 9 (.node (.user 20) []) [flagTerm, firstTerm])])

theorem wrong_component :
    positions code program false .whole [wrongComponent] = [(⟨2, 0⟩, false)] := by cbv

/-- An incorrect outer family key cannot dispatch to any body callback. -/
theorem wrong_key : positions code program true .whole [delayedTerm] = [] := by cbv

/-- The derived mutual inverse theorem applies at every candidate rank of this concrete family. -/
theorem delayed_exact (position : Position) :
    (position, true) ∈ positions code program false .whole [delayedTerm] ↔
      Decoder.decode (KeyedSource.family (RecursiveJoinFamily.termProgram code (lower program)) position.size false).members.plan position.rank =
        some delayedTerm := by
  rw [positions_exact keys complete code program accepted]
  simp [project]

/-- The public filter replays and removes a false candidate with mismatched join keys. -/
theorem wrong_component_filtered :
    RecursiveJoinQuery.query code program false .whole [wrongComponent] = [] := by cbv

/-- A delayed class position keeps its size-major global rank and obeys the size bound. -/
theorem bounded_delayed :
    RecursiveJoinQuery.boundedQuery code program false 2 .whole [delayedTerm] = [2] ∧
    RecursiveJoinQuery.boundedQuery code program false 1 .whole [delayedTerm] = [] ∧
    RecursiveJoinQuery.boundedDecode code program false 2 2 = some delayedTerm := by cbv

/-- Every query of the concrete family has distinct ascending global ranks. -/
theorem all_queries_ordered (key : Bool) (bound : Nat) (view : View) (wanted : List (EngineTerm Nat)) :
    (RecursiveJoinQuery.boundedQuery code program key bound view wanted).Nodup ∧
    (RecursiveJoinQuery.boundedQuery code program key bound view wanted).Pairwise (· ≤ ·) :=
  ⟨RecursiveJoinQuery.bounded_query_nodup code program key keys complete accepted candidates bound view wanted,
    RecursiveJoinQuery.bounded_query_ordered code program key keys complete accepted candidates bound view wanted⟩

end MicroCFTA.RecursiveJoinFamilyExamples
