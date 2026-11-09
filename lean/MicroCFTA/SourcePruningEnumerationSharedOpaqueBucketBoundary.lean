import MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations

namespace MicroCFTA.SourcePruningEnumerationSharedOpaqueBucketBoundary
open EnumerationState EnumerationCorrectness
open InternedConstructorTemplates SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {width : Nat}

/-- The opaque allocation retains the old indexes and appends an empty bucket. -/
def after (handle : Nat) (before : Cached) : Cached :=
  ⟨allocated (some handle) before.core, before.expandable, before.waiting⟩

private theorem candidate_false
    (heap : InternedConstructorTemplates.State Symbol Constraint) (value : Node) (handle : Nat)
    (decoded : lookupNode heap handle = some value)
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true) :
    SourcePruningEnumerationNativeIndex.candidate heap
      (.unenumerated (some handle) []) = some false := by
  simp [SourcePruningEnumerationNativeIndex.candidate, decoded, boundary]

section Executions
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every fuel returns the same literal opaque child row with no supplied bucket. -/
theorem run_exact
    (checkEmpty : Bool) (r n p h k : Nat) (scs : List Suspended)
    (value : Node) (handle : Nat) (caller : Caller width) (before : Cached)
    (queries : Queries)
    (encoded : encodeNode value = some handle)
    (decoded : lookupNode caller.checked.native.machine.heap handle = some value)
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false) :
    SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run
      checkEmpty r n p h k scs value caller before queries =
      ((.ok (some [.ok (.hole before.core.counter, (after handle before).core)]),
        caller, queries, before.core, before.waiting), some (after handle before)) := by
  have nonempty : value ≠ .empty := by
    intro same
    simp only [same, MergedOrdinaryHeight.recursiveBoundary, Bool.false_eq_true] at boundary
  have partitioned : (scs.partition (fun sc => EqualityTrie.isTerminal sc.trie)).1 = [] := by
    simp only [List.partition_eq_filter_filter]
    exact List.filter_eq_nil_iff.mpr (fun sc member =>
      List.any_eq_false.mp nonterminal sc member)
  have classified := candidate_false caller.checked.native.machine.heap value handle decoded boundary
  have cached : SourcePruningEnumerationCachedChild.allocate
      caller.checked.native.machine.heap (some handle) before =
      some (before.core.counter, after handle before) := by
    simp only [SourcePruningEnumerationCachedChild.allocate, classified, Option.map_some,
      Bool.false_eq_true, ↓reduceIte, after]
  cases value with
  | empty | reference _ | node _ _ _ _ =>
    simp only [MergedOrdinaryHeight.recursiveBoundary, Bool.false_eq_true] at boundary
  | union entry members depth free | mu entry body depth ordinary =>
    cases split : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk here descendants =>
      have hereSame : here = [] := by simpa only [split] using partitioned
      subst here
      simp only [SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run,
        SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.observe,
        ite_eq_right nonempty, split, SourcePruningEnumerationShallowChild.prepareChild,
        nonterminal, Bool.false_eq_true, ↓reduceIte, encoded,
        SourcePruningEnumerationCachedPrepare.prepareChild, Option.bind_some,
        cached, Option.map_some]
      rfl

/-- Two nonterminal buckets give identical complete shared observations and caches. -/
theorem bucket_irrelevant
    (checkEmpty : Bool) (r n p h k : Nat) (left right : List Suspended)
    (value : Node) (handle : Nat) (caller : Caller width) (before : Cached)
    (queries : Queries)
    (encoded : encodeNode value = some handle)
    (decoded : lookupNode caller.checked.native.machine.heap handle = some value)
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true)
    (leftNonterminal : left.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (rightNonterminal : right.any (fun sc => EqualityTrie.isTerminal sc.trie) = false) :
    SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run
      checkEmpty r n p h k left value caller before queries =
    SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run
      checkEmpty r n p h k right value caller before queries := by
  rw [run_exact checkEmpty r n p h k left value handle caller before queries
    encoded decoded boundary leftNonterminal,
    run_exact checkEmpty r n p h k right value handle caller before queries
    encoded decoded boundary rightNonterminal]

end Executions

/-- A correct input index leaves the fresh opaque slot parked with an empty bucket. -/
theorem fresh_parked
    (handle : Nat) (caller : Caller width) (before : Cached)
    (aligned : before.core.counter = before.core.values.length)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate
      caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot)) :
    (after handle before).core.values[before.core.counter]? =
        some (.unenumerated (some handle) []) ∧
      (after handle before).core.counter = before.core.counter + 1 ∧
      (after handle before).expandable before.core.counter = false ∧
      (after handle before).waiting = before.waiting := by
  have absent : before.core.values[before.core.counter]? = none := by
    exact List.getElem?_eq_none (by omega)
  have flag := flags before.core.counter
  simp only [absent, Option.getD_none, SourcePruningEnumerationNativeIndex.candidate,
    Option.some.injEq] at flag
  exact ⟨allocated_slot (some handle) before.core aligned, rfl, flag.symm, rfl⟩

end MicroCFTA.SourcePruningEnumerationSharedOpaqueBucketBoundary
