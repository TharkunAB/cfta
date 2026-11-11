import MicroCFTA.SourcePruningEnumerationSharedOpaqueBucketBoundary
import MicroCFTA.SourcePruningEnumerationSharedSelectedOpaqueDispatch
import MicroCFTA.SourcePruningEnumerationStorageProgress
import MicroCFTA.EnumerationIndexSelection

/-!
# Current candidate work at an actual opaque completion

Every active native slot has at least one assigned constructor.
Opaque allocation parks its fresh slot. Finalization disables the original target.
The original native handle and the prepared handle can differ.
These structural laws do not construct a model or bound the whole driver.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedOpaqueWork
open Language EnumerationState EnumerationCorrectness InternedConstructorTemplates
open EnumerationStorageProgress
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat}

private def assignedCost (assignment : Nat → Term Symbol) (uv : Nat) : UVarValue Symbol → Nat
  | .unenumerated (some _) _ => NumberedTerms.size (assignment uv)
  | _ => 0

private theorem append_cost
    (base : Core) (values : List (UVarValue Symbol)) (value : UVarValue Symbol)
    (assignment : Nat → Term Symbol) :
    pendingSize {base with values := values ++ [value]} assignment =
      pendingSize {base with values := values} assignment + assignedCost assignment values.length value := by
  let prefixState : Core := {base with counter := values.length, values := values}
  have allocation : Success (allocate none) prefixState prefixState.counter (allocated none prefixState) := by
    simp only [Success, allocate_exact, ExceptT.run, List.mem_singleton]
  have added := EnumerationStorageProgress.allocate_pendingSize none prefixState (allocated none prefixState)
    prefixState.counter assignment assignment rfl (fun _ _ => rfl) allocation
  have fresh : (allocated none prefixState).values[values.length]? =
      some (.unenumerated none []) := allocated_slot none prefixState rfl
  have written := values_set_pendingSize (allocated none prefixState) values.length
    (.unenumerated none []) value assignment fresh
  have replace : (values ++ [UVarValue.unenumerated none []]).set values.length value =
      values ++ [value] := by
    rw [List.set_append_right _ _ (Nat.le_refl _)]
    simp only [Nat.sub_self, List.set_cons_zero]
  simp only [pendingSize, allocated, prefixState, replace, assignedCost, Nat.add_zero] at added written ⊢
  rw [added] at written
  cases value with
  | eliminated | enumerated _ => exact written
  | unenumerated node _ => cases node <;> exact written

private theorem reverse_values_bound
    (reversed : List (UVarValue Symbol)) (base : Core) (assignment : Nat → Term Symbol)
    (enabled : Nat → Bool)
    (supported : ∀ offset value, reversed.reverse[offset]? = some value → enabled offset = true →
      ∃ handle scs, value = .unenumerated (some handle) scs) :
    ((List.range reversed.reverse.length).filter enabled).length ≤
      pendingSize {base with values := reversed.reverse} assignment := by
  revert supported
  induction reversed with
  | nil => intro _supported; exact Nat.le_refl 0
  | cons value rest ih =>
      intro supported
      have prefixSupported : ∀ offset item, rest.reverse[offset]? = some item → enabled offset = true →
          ∃ handle scs, item = .unenumerated (some handle) scs := by
        intro offset item stored active
        apply supported offset item _ active
        have inside := (List.getElem?_eq_some_iff.mp stored).1
        simpa only [List.reverse_cons, List.getElem?_append_left inside] using stored
      have earlier := ih prefixSupported
      have cost := append_cost base rest.reverse value assignment
      rw [List.reverse_cons, List.length_append, List.length_singleton,
        List.range_succ, List.filter_append]
      cases active : enabled rest.reverse.length with
      | false =>
          simp only [List.filter_cons, List.filter_nil, active, Bool.false_eq_true,
            ↓reduceIte, List.append_nil]
          omega
      | true =>
          have lastStored : (value :: rest).reverse[rest.reverse.length]? = some value := by
            simp only [List.reverse_cons, List.getElem?_append_right (Nat.le_refl _),
              Nat.sub_self, List.getElem?_cons_zero]
          obtain ⟨handle, scs, valueSame⟩ := supported rest.reverse.length value lastStored active
          rw [valueSame] at cost
          have positive : 1 ≤ NumberedTerms.size (assignment rest.reverse.length) := by
            cases assignment rest.reverse.length
            simp only [NumberedTerms.size]
            omega
          simp only [assignedCost] at cost
          simp only [List.filter_cons, List.filter_nil, active, ↓reduceIte,
            List.length_append, List.length_cons, List.length_nil]
          rw [valueSame]
          omega

/-- Current native flags bound candidate count for every finite assignment. -/
theorem candidates_le_pendingSize
    (caller : Caller width) (before : Cached) (assignment : Nat → Term Symbol)
    (aligned : before.core.counter = before.core.values.length)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate
      caller.checked.native.machine.heap ((before.core.values[slot]?).getD .eliminated) =
        some (before.expandable slot)) :
    (EnumerationIndexSelection.candidates before).length ≤ pendingSize before.core assignment := by
  have supported : ∀ offset value, before.core.values[offset]? = some value →
      before.expandable offset = true → ∃ handle scs, value = .unenumerated (some handle) scs := by
    intro offset value stored active
    have classified := flags offset
    rw [stored, Option.getD_some, active] at classified
    cases value with
    | eliminated | enumerated _ =>
        simp only [SourcePruningEnumerationNativeIndex.candidate, Option.some.injEq,
          Bool.false_eq_true] at classified
    | unenumerated node scs =>
        cases node with
        | none =>
            simp only [SourcePruningEnumerationNativeIndex.candidate, Option.some.injEq,
              Bool.false_eq_true] at classified
        | some handle => exact ⟨handle, scs, rfl⟩
  have bounded := reverse_values_bound before.core.values.reverse before.core assignment
    before.expandable (by simpa only [List.reverse_reverse] using supported)
  unfold EnumerationIndexSelection.candidates
  rw [aligned]
  simpa only [List.reverse_reverse] using bounded

private theorem disabled_count (values : List Nat) (enabled : Nat → Bool) (target : Nat) :
    values.Nodup → target ∈ values → enabled target = true →
      (values.filter (fun other => if other = target then false else enabled other)).length + 1 =
        (values.filter enabled).length := by
  induction values with
  | nil => intro _nodup member; cases member
  | cons first rest ih =>
      intro nodup member active
      obtain ⟨absent, tailNodup⟩ := List.nodup_cons.mp nodup
      by_cases same : first = target
      · subst first
        have tailSame : rest.filter (fun other => if other = target then false else enabled other) =
            rest.filter enabled := by
          apply List.filter_congr
          intro other present
          have different : other ≠ target := by
            intro equal
            exact absent (equal ▸ present)
          simp only [ite_eq_right different]
        simp only [List.filter_cons, Bool.false_eq_true, ↓reduceIte, active, tailSame, List.length_cons]
      · have later : target ∈ rest := (List.mem_cons.mp member).resolve_left (Ne.symm same)
        have tail := ih tailNodup later active
        simp only [List.filter_cons, ite_eq_right same]
        cases enabled first <;> simp_all only [Bool.false_eq_true, ↓reduceIte, List.length_cons] <;> omega

private theorem finalizer_frame
    (heap : InternedConstructorTemplates.State Symbol Constraint) (fuel target : Nat)
    (fragment : Fragment) (before after : Cached)
    (completed : SourcePruningEnumerationFinalize.run heap fuel target fragment before = some after) :
    after.core.counter = before.core.counter ∧
      after.core.values = before.core.values.set target (.enumerated fragment) ∧
      after.expandable = (fun other => if other = target then false else before.expandable other) := by
  simp only [SourcePruningEnumerationFinalize.run, Option.bind_eq_some_iff] at completed
  obtain ⟨_old, _stored, written⟩ := completed
  simp only [SourcePruningEnumerationNativeIndex.write, Option.bind_eq_some_iff,
    Option.some.injEq] at written
  obtain ⟨flag, classified, _removed, _removedCounts, _saved, _savedCounts, same⟩ := written
  have flagSame : flag = false := by
    exact (Option.some.inj classified).symm
  subst flag
  subst after
  exact ⟨rfl, rfl, rfl⟩

section Executions
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Actual opaque completion parks its fresh slot and removes one old candidate. -/
theorem complete_candidates
    (checkEmpty : Bool) (r n p h k target originalHandle : Nat) (scs : List Suspended)
    (value : Node) (preparedHandle : Nat) (caller : Caller width) (before : Cached) (queries : Queries)
    (fragment : Fragment) (reached : Caller width) (saved : Queries) (after : Cached)
    (stored : before.core.values[target]? = some (.unenumerated (some originalHandle) scs))
    (active : before.expandable target = true)
    (aligned : before.core.counter = before.core.values.length)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate
      caller.checked.native.machine.heap ((before.core.values[slot]?).getD .eliminated) =
        some (before.expandable slot))
    (encoded : SourcePruningEnumerationNodes.encodeNode value = some preparedHandle)
    (decoded : SourcePruningEnumerationNodes.lookupNode caller.checked.native.machine.heap preparedHandle = some value)
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (completed : SourcePruningEnumerationSharedSelectedOpaqueDispatch.run
      checkEmpty r n p h k target scs value caller before queries =
        some (.complete fragment reached saved after)) :
    fragment = .hole before.core.counter ∧ reached = caller ∧ saved = queries ∧
      after.core.counter = before.core.counter + 1 ∧
      after.core.values = (before.core.values ++ [(UVarValue.unenumerated (some preparedHandle) [] : UVarValue Symbol)]).set
        target (.enumerated (.hole before.core.counter)) ∧
      after.expandable = (fun other => if other = target then false else before.expandable other) ∧
      (EnumerationIndexSelection.candidates after).length + 1 =
        (EnumerationIndexSelection.candidates before).length := by
  have child := SourcePruningEnumerationSharedOpaqueBucketBoundary.run_exact
    checkEmpty r n p h k scs value preparedHandle caller before queries encoded decoded boundary nonterminal
  have parked := SourcePruningEnumerationSharedOpaqueBucketBoundary.fresh_parked
    preparedHandle caller before aligned flags
  have nonempty : value ≠ .empty := by
    intro same
    simp only [same, MergedOrdinaryHeight.recursiveBoundary, Bool.false_eq_true] at boundary
  have eligible : (match (generalizing := false) value with
      | .node .. => !(scs.any (fun sc => EqualityTrie.isTerminal sc.trie))
      | _ => false) = false := by
    cases value with
    | empty | reference _ | node _ _ _ _ =>
        simp only [MergedOrdinaryHeight.recursiveBoundary, Bool.false_eq_true] at boundary
    | union _ _ _ _ | mu _ _ _ _ => rfl
  cases finalized : SourcePruningEnumerationFinalize.run caller.checked.native.machine.heap k target
      (.hole before.core.counter)
      (SourcePruningEnumerationSharedOpaqueBucketBoundary.after preparedHandle before) with
  | none =>
      have actual := SourcePruningEnumerationSharedSelectedOpaqueDispatch.finalize_stopped
        checkEmpty r n p h k target scs value caller caller before
        (SourcePruningEnumerationSharedOpaqueBucketBoundary.after preparedHandle before)
        queries queries (.hole before.core.counter)
        (SourcePruningEnumerationSharedOpaqueBucketBoundary.after preparedHandle before).core
        before.core before.waiting nonempty eligible child finalized
      have impossible := actual.symm.trans completed
      cases impossible
  | some finished =>
      have actual := SourcePruningEnumerationSharedSelectedOpaqueDispatch.finalized
        checkEmpty r n p h k target scs value caller caller before
        (SourcePruningEnumerationSharedOpaqueBucketBoundary.after preparedHandle before) finished
        queries queries (.hole before.core.counter)
        (SourcePruningEnumerationSharedOpaqueBucketBoundary.after preparedHandle before).core
        before.core before.waiting nonempty eligible child finalized
      have same : (Fragments.Fragment.hole before.core.counter : Fragment) = fragment ∧ caller = reached ∧
          queries = saved ∧ finished = after := by
        simpa only [Option.some.injEq,
          SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result.complete.injEq]
          using actual.symm.trans completed
      obtain ⟨fragmentSame, callerSame, queriesSame, cacheSame⟩ := same
      have frame := finalizer_frame caller.checked.native.machine.heap k target
        (.hole before.core.counter)
        (SourcePruningEnumerationSharedOpaqueBucketBoundary.after preparedHandle before) finished finalized
      rw [cacheSame] at frame
      have counter : after.core.counter = before.core.counter + 1 :=
        frame.1.trans parked.2.1
      have values : after.core.values =
          (before.core.values ++ [(UVarValue.unenumerated (some preparedHandle) [] : UVarValue Symbol)]).set
            target (.enumerated (.hole before.core.counter)) := by
        simpa only [SourcePruningEnumerationSharedOpaqueBucketBoundary.after, allocated] using frame.2.1
      have flagFrame : after.expandable =
          (fun other => if other = target then false else before.expandable other) := frame.2.2
      refine ⟨fragmentSame.symm, callerSame.symm, queriesSame.symm, counter, values, flagFrame, ?_⟩
      have inside : target < before.core.counter := by
        rw [aligned]
        exact (List.getElem?_eq_some_iff.mp stored).1
      have freshDifferent : before.core.counter ≠ target := by omega
      have freshFalse : before.expandable before.core.counter = false := parked.2.2.1
      unfold EnumerationIndexSelection.candidates
      rw [counter, flagFrame, List.range_succ, List.filter_append]
      simp only [List.filter_cons, List.filter_nil, ite_eq_right freshDifferent, freshFalse,
        Bool.false_eq_true, ↓reduceIte, List.append_nil]
      exact disabled_count (List.range before.core.counter) before.expandable target
        List.nodup_range (List.mem_range.mpr inside) active

end Executions
end MicroCFTA.SourcePruningEnumerationSharedOpaqueWork
