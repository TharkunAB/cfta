import MicroCFTA.SourcePruningEnumerationNativeIndex

/-! Successful native waiting updates equal the count at the original supplied roots. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentNativeCountObserved
open EnumerationState EnumerationSchedule InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol

private theorem root_eq_of_observed (fuel : Nat) (forest : UnionFind.Forest)
    (roots : Nat → Nat) (paths : Roots forest roots) (uv representative : Nat)
    (observed : SourceUnionFindRoot.root fuel forest uv = some representative) :
    representative = roots uv := by
  obtain ⟨size, path⟩ := paths uv
  obtain ⟨completeFuel, complete⟩ := SourceUnionFindRoot.root_terminates forest uv (roots uv) size path
  have seen := SourceUnionFindRoot.root_moreFuel fuel completeFuel forest uv representative observed
  have canonical := SourceUnionFindRoot.root_moreFuel completeFuel fuel forest uv (roots uv) complete
  rw [Nat.add_comm] at canonical
  exact Option.some.inj (seen.symm.trans canonical)

/-- Every actual successful count uses the entry forest's mathematical roots at any fuel. -/
theorem count_eq_of_some (fuel : Nat) (forest : UnionFind.Forest) (roots : Nat → Nat)
    (paths : Roots forest roots) (change : Int) (scs : List Suspended)
    (waiting actual : EnumerationWaitingIndex.Waiting)
    (observed : SourcePruningEnumerationNativeIndex.count fuel forest change scs waiting = some actual) :
    actual = EnumerationCanonicalWaiting.count roots change scs waiting := by
  induction scs generalizing waiting actual with
  | nil =>
      simp only [SourcePruningEnumerationNativeIndex.count, Option.some.injEq] at observed
      simpa only [EnumerationCanonicalWaiting.count, List.map_nil,
        EnumerationWaitingIndex.count, List.foldl_nil] using observed.symm
  | cons sc rest ih =>
      cases found : SourceUnionFindRoot.root fuel forest sc.var with
      | none => simp [SourcePruningEnumerationNativeIndex.count, found] at observed
      | some representative =>
          have same := root_eq_of_observed fuel forest roots paths sc.var representative found
          have tailObserved : SourcePruningEnumerationNativeIndex.count fuel forest change rest
              (EnumerationWaitingIndex.bump change representative waiting) = some actual := by
            simpa only [SourcePruningEnumerationNativeIndex.count, found, Option.bind_some] using observed
          have counted := ih _ _ tailObserved
          simpa only [EnumerationCanonicalWaiting.count, List.map_cons,
            EnumerationWaitingIndex.count, List.foldl_cons, same] using counted

variable {NativeGuard EnumGuard : Type}

/-- An actual successful write removes and adds exactly the original reference counts. -/
theorem write_waiting (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (fuel target : Nat) (value : UVarValue Symbol) (gained lost : List Suspended)
    (roots : Nat → Nat) (paths : Roots before.core.representatives roots)
    (done : SourcePruningEnumerationNativeIndex.write heap fuel target value gained lost before = some after) :
    after.waiting = EnumerationCanonicalWaiting.count roots 1 gained
      (EnumerationCanonicalWaiting.count roots (-1) lost before.waiting) := by
  cases classified : SourcePruningEnumerationNativeIndex.candidate heap value with
  | none => simp [SourcePruningEnumerationNativeIndex.write, classified] at done
  | some flag =>
      cases removedEq : SourcePruningEnumerationNativeIndex.count fuel before.core.representatives (-1) lost before.waiting with
      | none => simp [SourcePruningEnumerationNativeIndex.write, classified, removedEq] at done
      | some removed =>
          cases savedEq : SourcePruningEnumerationNativeIndex.count fuel before.core.representatives 1 gained removed with
          | none => simp [SourcePruningEnumerationNativeIndex.write, classified, removedEq, savedEq] at done
          | some saved =>
              simp [SourcePruningEnumerationNativeIndex.write, classified, removedEq, savedEq] at done
              subst after
              have removedSame := count_eq_of_some fuel before.core.representatives roots paths (-1) lost
                before.waiting removed removedEq
              have savedSame := count_eq_of_some fuel before.core.representatives roots paths 1 gained
                removed saved savedEq
              simpa only [removedSame] using savedSame

end MicroCFTA.SourceCurrentNativeCountObserved
