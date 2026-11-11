import MicroCFTA.SourcePruningEnumerationSharedTraversalPendingSize

/-!
# Pending work through an actual shared selected edge

Own-class allocation adds zero-cost equality slots.
Each child charges at most its filled fragment's size.
The parent node supplies one unit for the final captured step.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge
open Language EnumerationState InternedConstructorTemplates EnumerationStorageProgress
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat}

private theorem suspendMany_aligned
    (heap : InternedConstructorTemplates.State Symbol Constraint) (tries : List EqualityTrie.Trie)
    (before after : Cached) (own : List Suspended)
    (aligned : before.core.counter = before.core.values.length)
    (observed : SourcePruningEnumerationCachedOwn.suspendMany heap tries before = some (own, after)) :
    after.core.counter = after.core.values.length := by
  induction tries generalizing before after own with
  | nil =>
      have same : before = after := congrArg Prod.snd (Option.some.inj observed)
      subst after
      exact aligned
  | cons trie rest ih =>
      simp only [SourcePruningEnumerationCachedOwn.suspendMany,
        Option.bind_eq_some_iff, Option.map_eq_some_iff] at observed
      obtain ⟨allocation, allocatedRun, result, continued, same⟩ := observed
      have cacheSame : result.2 = after := congrArg Prod.snd same
      simp only [SourcePruningEnumerationCachedChild.allocate, Option.map_eq_some_iff] at allocatedRun
      obtain ⟨_flag, _classified, allocationSame⟩ := allocatedRun
      have coreSame : allocated none before.core = allocation.2.core :=
        congrArg (fun value => value.2.core) allocationSame
      have middleAligned : allocation.2.core.counter = allocation.2.core.values.length := by
        rw [← coreSame]
        exact allocated_supply none before.core aligned
      rw [← cacheSame]
      exact ih allocation.2 result.2 result.1 middleAligned continued

private theorem forest_fill_size (assignment : Nat → Term Symbol) (children : List Fragment) :
    NumberedTerms.forestSize (children.map (Fragments.fill assignment)) =
      (children.map (fun child => NumberedTerms.size (Fragments.fill assignment child))).sum := by
  induction children with
  | nil => rfl
  | cons child children ih =>
      simp only [List.map_cons, NumberedTerms.forestSize, List.sum_cons, ih]

private theorem node_fill_size
    (assignment : Nat → Term Symbol) (symbol : Symbol) (children : List Fragment) :
    NumberedTerms.size (Fragments.fill assignment (.node symbol children)) =
      1 + (children.map (fun child => NumberedTerms.size (Fragments.fill assignment child))).sum := by
  simp only [Fragments.fill, NumberedTerms.size, forest_fill_size]

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)]
variable [DecidableEq (Value Symbol Constraint)]

/-- A complete actual edge reserves one unit beyond its children's work charge. -/
theorem complete_pendingSize_le
    (checkEmpty : Bool) (r n p h k : Nat) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (caller reached : Caller width)
    (before after : Cached) (queries saved : Queries) (fragment : Fragment)
    (assignment : Nat → Term Symbol)
    (aligned : before.core.counter = before.core.values.length)
    (completed : run checkEmpty r n p h k scs edge caller before queries =
      .complete fragment reached saved after) :
    pendingSize after.core assignment + 1 ≤ pendingSize before.core assignment +
      NumberedTerms.size (Fragments.fill assignment fragment) := by
  cases allowed : EnumerationState.arityAllows edge.children.length scs with
  | false =>
      simp only [run, SourcePruningEnumerationCachedOwn.prepare, allowed,
        Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at completed
  | true =>
      cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
      | none =>
          simp only [run, SourcePruningEnumerationCachedOwn.prepare, allowed,
            ↓reduceIte, projected, reduceCtorEq] at completed
      | some projection =>
          rcases projection with ⟨tries, residual⟩
          cases suspended : SourcePruningEnumerationCachedOwn.suspendMany
              caller.checked.native.machine.heap tries before with
          | none =>
              simp only [run, SourcePruningEnumerationCachedOwn.prepare, allowed,
                ↓reduceIte, projected, suspended, Option.map_none, reduceCtorEq] at completed
          | some ownResult =>
              rcases ownResult with ⟨own, middle⟩
              let staged := edge.children.zipIdx.map (fun indexed =>
                (indexed.1, EqualityTrie.descendScs indexed.2 scs ++
                  EqualityTrie.descendScs indexed.2 own,
                  SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint)
                    (EqualityTrie.descendScs indexed.2 scs ++
                      EqualityTrie.descendScs indexed.2 own) indexed.1))
              have prepared : SourcePruningEnumerationCachedOwn.prepare
                  caller.checked.native.machine.heap scs edge before =
                  some [((edge.entry.key.symbol, staged, residual), middle)] := by
                simp only [SourcePruningEnumerationCachedOwn.prepare, allowed, ↓reduceIte,
                  projected, suspended, Option.map_some, staged]
              have middleAligned := suspendMany_aligned caller.checked.native.machine.heap
                tries before middle own aligned suspended
              have ownCost := SourcePruningEnumerationStorageProgress.suspendMany_pendingSize
                caller.checked.native.machine.heap tries before middle own assignment suspended
              simp only [run, prepared] at completed
              cases childrenRun : ChildTraversal.run checkEmpty r n p h k
                  (staged.map (fun input => (input.1, input.2.1))) caller middle queries with
              | stopped completedPrefix observation candidate =>
                  simp only [childrenRun, reduceCtorEq] at completed
              | complete fragments nextCaller nextQueries childAfter =>
                  rw [childrenRun] at completed
                  cases completed
                  have childCost := ChildTraversal.complete_pendingSize_le checkEmpty r n p h k
                    (staged.map (fun input => (input.1, input.2.1))) caller reached
                    middle childAfter queries saved fragments assignment middleAligned childrenRun
                  change pendingSize childAfter.core assignment + 1 ≤ pendingSize before.core assignment +
                    NumberedTerms.size (Fragments.fill assignment (.node edge.entry.key.symbol fragments))
                  rw [node_fill_size]
                  omega

end MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge
