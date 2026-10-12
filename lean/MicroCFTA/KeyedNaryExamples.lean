import MicroCFTA.KeyedNaryCausality
import MicroCFTA.KeyedNaryQuery
import MicroCFTA.KeyedNaryDispatch
import MicroCFTA.RecursiveNaryExamples

/-!
# Concrete flat keyed recursive families

Two keys retain finite masses nine and one. A third flat branch is empty
at the base size and becomes live through mutual recursion.
-/
namespace MicroCFTA.KeyedNaryExamples
open Language GeneratorCombinators IntegerTermViews SizedRank
open RecursiveCallbackTermination KeyedNaryFields KeyedNaryInverse
open KeyedNaryAlignment (Recipe valueProgram sourceTermProgram)
open RecursiveNaryExamples (pureCallbacks pure_exact)

/-- Flat source branches retain indices zero, one, and two. -/
def branches : Fin 3 → Recipe Bool Nat Nat Nat
  | ⟨0, _⟩ => .retained (fun _ => 9) (by intro; decide) (.pure (0, .node .pure []))
  | ⟨1, _⟩ => .retained (fun _ => 1) (by intro; decide) (.pure (0, .node .pure []))
  | ⟨2, _⟩ => .label 10 (.map Nat.succ (.occurrence true))

/-- The two keyed bodies have one flat choice and one labelled mutual call. -/
def program : Bool → Recipe Bool Nat Nat Nat
  | false => .choice 3 branches
  | true => .label 11 (.map Nat.succ (.occurrence false))

def code (key : Bool) : Nat := if key then 1 else 0

def keys : List Bool := [false, true]

theorem complete (key : Bool) : key ∈ keys := by cases key <;> simp [keys]

/-- The actual discovered per-key metadata accepts both bodies. -/
theorem accepted : Guarded keys complete program := by
  intro key
  cases key <;> simp [program, branches, KeyedNaryAlignment.valueProgram,
    KeyedNaryAlignment.valueRecipe, KeyedNaryAlignment.alternatives, KeyedSource.guarded]

/-- Each retained leaf uses an independently correct finite callback. -/
theorem exact_leaves : ∀ key, LeavesExact (pureCallbacks (Symbol := Nat)) (program key) := by
  intro key
  cases key with
  | false =>
      intro ⟨index, within⟩
      have cases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
      rcases cases with rfl | rfl | rfl
      · exact pure_exact _
      · exact pure_exact _
      · trivial
  | true => trivial

/-- The first mutual term keeps the original flat branch zero. -/
def firstTerm : EngineTerm Nat := KeyedTermBoundary.atKeyTerm 1
  (.node (.user 11) [KeyedTermBoundary.atKeyTerm 0
    (.node (.choice 0) [.node .pure []])])

/-- The second mutual term keeps the original flat branch one. -/
def secondTerm : EngineTerm Nat := KeyedTermBoundary.atKeyTerm 1
  (.node (.user 11) [KeyedTermBoundary.atKeyTerm 0
    (.node (.choice 1) [.node .pure []])])

/-- The delayed alternative retains branch two after its empty base class. -/
def delayedTerm : EngineTerm Nat := KeyedTermBoundary.atKeyTerm 0
  (.node (.choice 2) [.node (.user 10) [firstTerm]])

theorem initial_counts : rootCounts program false 0 = 2 ∧ rootCounts program false 1 = 0 ∧ rootCounts program false 2 = 2 := by cbv

theorem delayed_branch_empty :
    Decoder.count (KeyedNarySource.valueRecord (branches 2) (fun key size => KeyedSource.family (valueProgram program) size key) 0).members.plan = 0 := by cbv

theorem first_inverse : positions code pureCallbacks program true .whole [firstTerm] = [(⟨1, 0⟩, true)] := by cbv

theorem second_inverse : positions code pureCallbacks program true .whole [secondTerm] = [(⟨1, 1⟩, true)] := by cbv

theorem delayed_inverse : positions code pureCallbacks program false .whole [delayedTerm] = [(⟨2, 0⟩, true)] := by cbv

theorem all_views :
    positions code pureCallbacks program false .spine [delayedTerm] = [(⟨2, 0⟩, true)] ∧
    positions code pureCallbacks program false .labelled [delayedTerm] = [(⟨2, 0⟩, true)] := by cbv

/-- Mutual recursion retains mass nine-to-one at the later size. -/
theorem retained_mass :
    (KeyedSource.family (valueProgram program) 2 false).mass = 10 ∧
    (KeyedSource.family (valueProgram program) 2 false).members.sampling.ranked =
      [(9 / 10, (0, 2)), (1 / 10, (1, 2))] := by cbv

/-- Flat source correspondence has no extra binary choice wrapper. -/
theorem delayed_decodes : rootSelect code program false ⟨2, 0⟩ = some delayedTerm := by cbv

theorem wrong_outer_key : positions code pureCallbacks program true .whole [delayedTerm] = [] := by cbv

theorem wrong_inner_key : positions code pureCallbacks program false .whole
    [.node .atKey [.node (.key 0) [], .node .family [.node (.key 1) [], .node .pure []]]] = [] := by cbv

/-- The checked inverse theorem applies to the independent delayed-branch decoder. -/
theorem delayed_exact (position : Position) :
    (position, true) ∈ positions code pureCallbacks program false .whole [delayedTerm] ↔
      rootSelect code program false position = some delayedTerm := by
  rw [positions_exact keys complete code pureCallbacks program accepted exact_leaves]
  simp [project]

/-- A raw singleton choice has a private choice label, unlike same-key merge dispatch. -/
def singleton : Recipe Bool Nat Nat Nat := .choice 1 (fun _ => .finite (.pure (0, .node .pure [])))

theorem raw_singleton_term :
    Decoder.values (KeyedNarySource.termRecord singleton (fun _ _ => GroupedRecord.empty) 0).members.plan =
      [.node (.choice 0) [.node .pure []]] := by cbv

theorem merged_singleton_term :
    (KeyedNaryDispatch.mergeGroups [(Recipe.finite (.pure (0, .node .pure [])) : Recipe Bool Nat Nat Nat)]).map
      (fun body => Decoder.values (KeyedNarySource.termRecord body (fun _ _ => GroupedRecord.empty) 0).members.plan) =
      some [.node .pure []] := by cbv

/-- A raw empty choice has no members; source merge dispatch omits its absent key. -/
theorem raw_empty_count :
    Decoder.count (KeyedNarySource.valueRecord
      (Recipe.choice (Key := Bool) (Root := Nat) (Symbol := Nat) (α := Nat) 0 Fin.elim0)
      (fun _ _ => GroupedRecord.empty) 0).members.plan = 0 := by cbv

end MicroCFTA.KeyedNaryExamples
