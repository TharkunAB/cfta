import MicroCFTA.SourceCurrentPreparedChildHistoryUnion
import MicroCFTA.SourcePruningEnumerationCachedOwn
import MicroCFTA.SourcePruningEnumerationChildDispatch

/-! Actual first-child dispatches retain staged active keys at the allocated slot. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentOwnFirstChildDispatchHistory
open EnumerationState EnumerationSchedule EnumerationCorrectness EnumerationCompressionFrame
open InternedConstructorTemplates SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Input" => Node × List Suspended × Option (EnumerateM Symbol Constraint (Fragments.Fragment Symbol))
local notation "OwnRow" => (Symbol × List Input × Option Constraint) × Cached

private theorem allocation_active {NativeGuard EnumGuard : Type}
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (allocation : Nat × EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (observed : SourcePruningEnumerationCachedChild.allocate heap none before = some allocation) :
    allocation.2.core.expansionAncestry = before.core.expansionAncestry := by
  cases classified : SourcePruningEnumerationNativeIndex.candidate heap (.unenumerated none []) with
  | none => simp [SourcePruningEnumerationCachedChild.allocate, classified] at observed
  | some flag =>
      simp only [SourcePruningEnumerationCachedChild.allocate, classified, Option.map_some,
        Option.some.injEq] at observed
      rw [← observed]
      rfl

private theorem suspend_many_active {NativeGuard EnumGuard : Type}
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (tries : List EqualityTrie.Trie)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard) (suspended : List Suspended)
    (observed : SourcePruningEnumerationCachedOwn.suspendMany heap tries before = some (suspended, after)) :
    after.core.expansionAncestry = before.core.expansionAncestry := by
  induction tries generalizing before after suspended with
  | nil =>
      simp only [SourcePruningEnumerationCachedOwn.suspendMany, Option.some.injEq, Prod.mk.injEq] at observed
      rcases observed with ⟨rfl, rfl⟩
      rfl
  | cons trie rest ih =>
      cases allocated : SourcePruningEnumerationCachedChild.allocate heap none before with
      | none => simp [SourcePruningEnumerationCachedOwn.suspendMany, allocated] at observed
      | some allocation =>
          cases tail : SourcePruningEnumerationCachedOwn.suspendMany heap rest allocation.2 with
          | none => simp [SourcePruningEnumerationCachedOwn.suspendMany, allocated, tail] at observed
          | some result =>
              simp only [SourcePruningEnumerationCachedOwn.suspendMany, allocated, Option.bind_some,
                tail, Option.map_some, Option.some.injEq, Prod.mk.injEq] at observed
              rw [← observed.2]
              exact (ih allocation.2 result.2 result.1 tail).trans (allocation_active heap before allocation allocated)

private theorem own_active
    (heap : InternedConstructorTemplates.State Symbol Constraint) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (before : Cached) (row : OwnRow)
    (member : row ∈ (SourcePruningEnumerationCachedOwn.prepare heap scs edge before).getD []) :
    row.2.core.expansionAncestry = before.core.expansionAncestry := by
  cases allowed : arityAllows edge.children.length scs with
  | false => simp [SourcePruningEnumerationCachedOwn.prepare, allowed] at member
  | true =>
      cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
      | none => simp [SourcePruningEnumerationCachedOwn.prepare, allowed, projected] at member
      | some projection =>
          rcases projection with ⟨tries, residual⟩
          cases suspended : SourcePruningEnumerationCachedOwn.suspendMany heap tries before with
          | none => simp [SourcePruningEnumerationCachedOwn.prepare, allowed, projected, suspended] at member
          | some result =>
              simp only [SourcePruningEnumerationCachedOwn.prepare, allowed, ite_true,
                projected, suspended, Option.map_some, Option.getD_some, List.mem_singleton] at member
              subst row
              exact suspend_many_active heap tries before result.2 result.1 suspended

variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- A literal nonterminal dispatch derives its cache, raw core, caller, query, and child history together. -/
theorem nonterminal_dispatch_history
    (checkEmpty : Bool) (r n p h k : Nat) (scs : List Suspended) (incoming : Node)
    (caller : Caller width) (before : Cached) (queries : SourceEndpointMemo.Memos) :
    match scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | ([], _) =>
        let actual := SourcePruningEnumerationChildDispatch.run checkEmpty r n p h k scs incoming caller before queries
        match actual.2 with
        | none => True
        | some after =>
            match actual.1.1 with
            | .ok (some [.ok (fragment, returned)]) =>
                fragment = .hole before.core.counter ∧ returned = after.core ∧
                  actual.1.2.1 = caller ∧ actual.1.2.2.1 = queries ∧
                  after.core.expansionAncestry = before.core.expansionAncestry ∧
                  after.core.recursionAncestry before.core.counter =
                    (before.core.expansionAncestry ++ before.core.recursionAncestry before.core.counter).eraseDups ∧
                  ∀ key ∈ before.core.expansionAncestry, key ∈ after.core.recursionAncestry before.core.counter
            | _ => True
    | _ => True := by
  cases partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
  | mk terminals descendants =>
      cases terminals with
      | cons first rest => trivial
      | nil =>
          have terminalEmpty : scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) = [] := by
            simpa using congrArg Prod.fst partitioned
          by_cases empty : incoming = .empty
          · subst incoming
            simp [SourcePruningEnumerationChildDispatch.run]
          · cases cached : SourcePruningEnumerationCachedPrepare.prepareChild caller.checked.native.machine.heap k scs incoming before with
            | none => simp [SourcePruningEnumerationChildDispatch.run, empty, terminalEmpty, cached]
            | some rows =>
                have erased := SourcePruningEnumerationCachedPrepare.erase_some caller.checked.native.machine.heap
                  k scs incoming before rows cached
                cases shallow : SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint) scs incoming with
                | none => simp [shallow] at erased
                | some action =>
                    have raw : ExceptT.run (action before.core) = rows.map (fun row => .ok (row.1, row.2.core)) := by
                      simpa only [shallow, Option.map_some, Option.some.injEq] using erased
                    cases rows with
                    | nil =>
                        simp [SourcePruningEnumerationChildDispatch.run, SourcePruningEnumerationChildDispatch.observe,
                          empty, terminalEmpty, cached, shallow, raw]
                    | cons row rest =>
                        cases rest with
                        | cons next tail => simp [SourcePruningEnumerationChildDispatch.run, empty, terminalEmpty, cached]
                        | nil =>
                            rcases row with ⟨fragment, after⟩
                            have facts := SourceCurrentPreparedChildHistoryUnion.prepare_child_history
                              caller.checked.native.machine.heap before after k scs incoming [(fragment, after)]
                              fragment cached (by simp)
                            have claimed : fragment = .hole before.core.counter ∧ after.core = after.core ∧
                                caller = caller ∧ queries = queries ∧
                                after.core.expansionAncestry = before.core.expansionAncestry ∧
                                after.core.recursionAncestry before.core.counter =
                                  (before.core.expansionAncestry ++ before.core.recursionAncestry before.core.counter).eraseDups ∧
                                ∀ key ∈ before.core.expansionAncestry, key ∈ after.core.recursionAncestry before.core.counter :=
                              ⟨facts.1, rfl, rfl, rfl, facts.2.1, facts.2.2.1, facts.2.2.2⟩
                            simpa [SourcePruningEnumerationChildDispatch.run, SourcePruningEnumerationChildDispatch.observe,
                              empty, terminalEmpty, cached, shallow, raw] using claimed

/-- The first own-staged literal dispatch retains the original active keys at its actual returned child slot. -/
theorem own_first_dispatch_history
    (checkEmpty : Bool) (r n p h k : Nat) (scs : List Suspended) (edge : EdgeValue Symbol Constraint)
    (caller : Caller width) (before : Cached) (queries : SourceEndpointMemo.Memos) :
    ∀ row ∈ (SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before).getD [],
      match row.1.2.1 with
      | [] => True
      | input :: _ =>
          match input.2.1.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
          | ([], _) =>
              let actual := SourcePruningEnumerationChildDispatch.run checkEmpty r n p h k input.2.1 input.1 caller row.2 queries
              match actual.2 with
              | none => True
              | some after =>
                  match actual.1.1 with
                  | .ok (some [.ok (fragment, returned)]) =>
                      fragment = .hole row.2.core.counter ∧ returned = after.core ∧
                        actual.1.2.1 = caller ∧ actual.1.2.2.1 = queries ∧
                        after.core.expansionAncestry = before.core.expansionAncestry ∧
                        after.core.recursionAncestry row.2.core.counter =
                          (before.core.expansionAncestry ++ row.2.core.recursionAncestry row.2.core.counter).eraseDups ∧
                        ∀ key ∈ before.core.expansionAncestry, key ∈ after.core.recursionAncestry row.2.core.counter
                  | _ => True
          | _ => True := by
  intro row member
  have active := own_active caller.checked.native.machine.heap scs edge before row member
  cases first : row.1.2.1 with
  | nil => trivial
  | cons input rest =>
      have actual := nonterminal_dispatch_history checkEmpty r n p h k input.2.1 input.1 caller row.2 queries
      simpa only [active] using actual

end MicroCFTA.SourceCurrentOwnFirstChildDispatchHistory
