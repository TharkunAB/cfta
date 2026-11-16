import MicroCFTA.EnumerationSchedule

namespace MicroCFTA.SourcePruningEnumerationRawAliasPrimitives
open EnumerationState EnumerationCorrectness EnumerationSchedule
set_option autoImplicit false

/- Note [Raw alias growth]
Successful lookup and union retain every existing finite alias.
The forward laws do not require totality or an allocation bound.
Allocation retains the complete representative forest.
These local laws do not identify an output's causal branch.
The actual worker still needs a proof that composes its control steps.
-/

/-- Successful lookup retains every existing raw alias. -/
theorem findRoot_sameClass_forward
    (fuel uv : Nat) (before : UnionFind.Forest) (found : UnionFind.Result)
    (actual : UnionFind.findRoot fuel before uv = some found) :
    ∀ left right, UnionFind.SameClass before left right →
      UnionFind.SameClass found.forest left right := by
  intro left right same
  obtain ⟨root, size, leftPath, rightPath⟩ := same
  exact ⟨root, size,
    (UnionFind.findRoot_correct fuel before uv found actual).2 leftPath,
    (UnionFind.findRoot_correct fuel before uv found actual).2 rightPath⟩

/-- Successful union retains every existing raw alias without a totality premise. -/
theorem union_sameClass_forward
    (leftFuel rightFuel left right : Nat) (before after : UnionFind.Forest)
    (actual : UnionFind.union leftFuel rightFuel before left right = some after) :
    ∀ first second, UnionFind.SameClass before first second →
      UnionFind.SameClass after first second := by
  cases firstResult : UnionFind.findRoot leftFuel before left with
  | none => simp [UnionFind.union, firstResult] at actual
  | some first =>
    cases secondResult : UnionFind.findRoot rightFuel first.forest right with
    | none => simp [UnionFind.union, firstResult, secondResult] at actual
    | some second =>
      have firstRun := UnionFind.findRoot_correct leftFuel before left first firstResult
      have secondRun := UnionFind.findRoot_correct rightFuel first.forest right second secondResult
      have leftPath := secondRun.2 (firstRun.2 firstRun.1)
      have rightPath := secondRun.2 secondRun.1
      have leftRoot := UnionFind.reaches_terminal leftPath
      have rightRoot := UnionFind.reaches_terminal rightPath
      have kept (a b : Nat) (same : UnionFind.SameClass before a b) :
          UnionFind.SameClass second.forest a b :=
        findRoot_sameClass_forward rightFuel right first.forest second secondResult a b
          (findRoot_sameClass_forward leftFuel left before first firstResult a b same)
      by_cases same : first.representative = second.representative
      · simp [UnionFind.union, firstResult, secondResult, same] at actual
        subst after
        exact kept
      · by_cases smaller : first.size < second.size
        · simp [UnionFind.union, firstResult, secondResult, same, smaller] at actual
          subst after
          intro a b original
          obtain ⟨root, size, aPath, bPath⟩ := kept a b original
          exact ⟨_, _, UnionFind.link_reaches leftRoot rightRoot same aPath,
            UnionFind.link_reaches leftRoot rightRoot same bPath⟩
        · simp [UnionFind.union, firstResult, secondResult, same, smaller] at actual
          subst after
          intro a b original
          obtain ⟨root, size, aPath, bPath⟩ := kept a b original
          exact ⟨_, _, UnionFind.link_reaches rightRoot leftRoot (Ne.symm same) aPath,
            UnionFind.link_reaches rightRoot leftRoot (Ne.symm same) bPath⟩

variable {Symbol Guard : Type}

/-- Allocation retains every raw alias because it retains the representative forest. -/
theorem allocated_sameClass_forward (node : Option Nat) (before : State Symbol Guard) :
    ∀ left right, UnionFind.SameClass before.representatives left right →
      UnionFind.SameClass (allocated node before).representatives left right := by
  intro left right same
  exact same

/-- The actual successful representative action retains every raw alias. -/
theorem representative_sameClass_forward
    (fuel uv root : Nat) (before after : State Symbol Guard)
    (actual : Success (representative fuel uv) before root after) :
    ∀ left right, UnionFind.SameClass before.representatives left right →
      UnionFind.SameClass after.representatives left right := by
  obtain ⟨found, lookup, _rootSame, rfl⟩ :=
    (representative_success fuel uv before after root).mp actual
  exact findRoot_sameClass_forward fuel uv before.representatives found lookup

/-- The actual successful union action retains every raw alias. -/
theorem unionVariables_sameClass_forward
    (fuel left right : Nat) (before after : State Symbol Guard)
    (actual : Success (unionVariables fuel left right) before () after) :
    ∀ first second, UnionFind.SameClass before.representatives first second →
      UnionFind.SameClass after.representatives first second := by
  obtain ⟨forest, joined, rfl⟩ := (unionVariables_success fuel left right before after).mp actual
  exact union_sameClass_forward fuel fuel left right before.representatives forest joined

end MicroCFTA.SourcePruningEnumerationRawAliasPrimitives
