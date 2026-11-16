import MicroCFTA.SourcePruningEnumerationCachedOwn
import MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations

namespace MicroCFTA.SourcePruningEnumerationOwnAliasForest
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Edge" => EdgeValue Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Input" => Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)
local notation "Row" => (Symbol × List Input × Option Constraint) × Cached
set_option autoImplicit false

/- Note [Own preparation forest]
Own preparation allocates one raw slot for each projected trie.
Allocation extends the value slots and retains the representative forest.
The actual suspension equation determines every intermediate cache.
The preparation equation determines the same final cache.
Residual recording changes obligations and retains that forest.
These equalities need no storage, root, or capacity invariant.
-/

theorem suspendMany_forest {EnumGuard NativeGuard : Type}
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (tries : List EqualityTrie.Trie)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard) (own : List Suspended)
    (actual : SourcePruningEnumerationCachedOwn.suspendMany heap tries before = some (own, after)) :
    after.core.representatives = before.core.representatives := by
  induction tries generalizing before after own with
  | nil =>
      have resultSame : ([], before) = (own, after) := Option.some.inj actual
      have cacheSame : before = after :=
        congrArg (fun result : List Suspended × EnumerationExpandableIndex.Cached Symbol EnumGuard =>
          result.2) resultSame
      exact congrArg (fun cached : EnumerationExpandableIndex.Cached Symbol EnumGuard =>
        cached.core.representatives) cacheSame.symm
  | cons trie rest ih =>
      let middle : EnumerationExpandableIndex.Cached Symbol EnumGuard :=
        ⟨EnumerationState.allocated none before.core, before.expandable, before.waiting⟩
      have allocation : SourcePruningEnumerationCachedChild.allocate heap none before =
          some (before.core.counter, middle) := rfl
      simp only [SourcePruningEnumerationCachedOwn.suspendMany, allocation, Option.bind_some] at actual
      generalize tailRun : SourcePruningEnumerationCachedOwn.suspendMany heap rest middle = tail at actual
      cases tail with
      | none => cases actual
      | some result =>
          rcases result with ⟨tailOwn, tailAfter⟩
          have resultSame : (⟨trie, before.core.counter⟩ :: tailOwn, tailAfter) = (own, after) :=
            Option.some.inj actual
          have cacheSame : tailAfter = after :=
            congrArg (fun result : List Suspended × EnumerationExpandableIndex.Cached Symbol EnumGuard =>
              result.2) resultSame
          have tailForest := ih middle tailAfter tailOwn tailRun
          have middleForest : middle.core.representatives = before.core.representatives := rfl
          have afterForest : after.core.representatives = tailAfter.core.representatives :=
            congrArg (fun cached : EnumerationExpandableIndex.Cached Symbol EnumGuard =>
              cached.core.representatives) cacheSame.symm
          exact afterForest.trans (tailForest.trans middleForest)

theorem prepare_forest
    (heap : InternedConstructorTemplates.State Symbol Constraint) (scs : List Suspended) (edge : Edge)
    (before middle : Cached) (symbol : Symbol) (staged : List Input) (residual : Option Constraint)
    (actual : SourcePruningEnumerationCachedOwn.prepare heap scs edge before =
      some [((symbol, staged, residual), middle)]) :
    middle.core.representatives = before.core.representatives := by
  unfold SourcePruningEnumerationCachedOwn.prepare at actual
  split at actual
  next allowed =>
    generalize projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = plan at actual
    cases plan with
    | none => cases actual
    | some plan =>
        rcases plan with ⟨tries, kept⟩
        dsimp only at actual
        generalize suspended : SourcePruningEnumerationCachedOwn.suspendMany heap tries before = result at actual
        cases result with
        | none => cases actual
        | some result =>
            rcases result with ⟨own, after⟩
            have rowSame := (List.cons.inj (Option.some.inj actual)).1
            have cacheSame : after = middle := congrArg (fun row : Row => row.2) rowSame
            have forest := suspendMany_forest heap tries before after own suspended
            exact (congrArg (fun cached : Cached => cached.core.representatives) cacheSame.symm).trans forest
  next rejected => cases actual

theorem finish_forest (residual : Option Constraint) (fragment : Fragment) (before : Cached) :
    (SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.finish residual fragment before).core.representatives =
      before.core.representatives := by
  rfl

end MicroCFTA.SourcePruningEnumerationOwnAliasForest
