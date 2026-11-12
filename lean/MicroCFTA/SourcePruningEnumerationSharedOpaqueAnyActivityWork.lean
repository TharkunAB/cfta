import MicroCFTA.SourcePruningEnumerationSharedOpaqueWork

/-!
# Exact candidate debit at an opaque head

The actual head clears its captured target flag.
The fresh opaque slot has a false flag.
An active target contributes one unit. An inactive target contributes zero units.
The stored native handle and prepared native handle can differ.
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


private theorem disabled_count_any_activity (values : List Nat) (enabled : Nat → Bool) (target : Nat)
    (unique : values.Nodup) (member : target ∈ values) :
    (values.filter (fun other => if other = target then false else enabled other)).length +
      (if enabled target then 1 else 0) = (values.filter enabled).length := by
  cases active : enabled target with
  | false =>
      have unchanged : values.filter (fun other => if other = target then false else enabled other) =
          values.filter enabled := by
        apply List.filter_congr
        intro other _present
        by_cases same : other = target
        · subst other
          simp only [↓reduceIte, active]
        · simp only [ite_eq_right same]
      simp only [unchanged, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  | true =>
      simpa only [active, ↓reduceIte] using disabled_count values enabled target unique member active

section Executions
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Actual opaque completion consumes its target flag if that flag is active. -/
theorem complete_candidates_any_activity
    (checkEmpty : Bool) (r n p h k target originalHandle : Nat) (scs : List Suspended)
    (value : Node) (preparedHandle : Nat) (caller : Caller width) (before : Cached) (queries : Queries)
    (fragment : Fragment) (reached : Caller width) (saved : Queries) (after : Cached)
    (stored : before.core.values[target]? = some (.unenumerated (some originalHandle) scs))
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
      (EnumerationIndexSelection.candidates after).length + (if before.expandable target then 1 else 0) =
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
      exact disabled_count_any_activity (List.range before.core.counter) before.expandable target
        List.nodup_range (List.mem_range.mpr inside)


end Executions
end MicroCFTA.SourcePruningEnumerationSharedOpaqueWork
