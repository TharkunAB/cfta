import MicroCFTA.SourcePruningEnumerationEdgeScalarBounds
import MicroCFTA.SourcePruningEnumerationEdgeInputs

namespace MicroCFTA.SourcePruningEnumerationCachedOwn
open EnumerationState EnumerationCorrectness
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint

/-- The actual own-class traversal returns its consecutive suspended variables in source order. -/
theorem suspendMany_vars
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (tries : List EqualityTrie.Trie) (before : Cached) (own : List Suspended) (after : Cached)
    (observed : suspendMany heap tries before = some (own, after)) :
    own = suspendedVars before.core.counter tries := by
  induction tries generalizing before own after with
  | nil =>
      simp only [suspendMany, Option.some.injEq, Prod.mk.injEq] at observed
      exact observed.1.symm
  | cons trie rest ih =>
      let middle : Cached := ⟨allocated none before.core, before.expandable, before.waiting⟩
      have allocatedNone : SourcePruningEnumerationCachedChild.allocate heap none before =
          some (before.core.counter, middle) := rfl
      simp only [suspendMany, allocatedNone, Option.bind_some, Option.map_eq_some_iff] at observed
      obtain ⟨tail, tailRun, resultSame⟩ := observed
      have ownSame := (Prod.mk.inj resultSame).1
      rw [← ownSame, ih middle tail.1 tail.2 tailRun]
      rfl

/-- An actual prepared singleton contains the exact inherited and fresh own-class child inputs. -/
theorem prepare_inputs
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (scs : List Suspended) (edge : InternedConstructorTemplates.EdgeValue Symbol Constraint)
    (before after : Cached) (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (result : Symbol × List (Node × List Suspended ×
      Option (EnumerateM Symbol Constraint (Fragments.Fragment Symbol))) × Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (observed : prepare heap scs edge before = some [(result, after)]) :
    result = (edge.entry.key.symbol,
      (SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries).map (fun input =>
        (input.1, input.2, SourcePruningEnumerationShallowChild.prepareChild
          (EnumGuard := Constraint) input.2 input.1)), residual) := by
  by_cases allowed : arityAllows edge.children.length scs = true
  · simp only [prepare, allowed, ↓reduceIte, projected, Option.map_eq_some_iff] at observed
    obtain ⟨ownResult, ownRun, resultSame⟩ := observed
    have ownSame := suspendMany_vars heap tries before ownResult.1 ownResult.2 ownRun
    have payloadSame := (Prod.mk.inj (List.cons.inj resultSame).1).1
    rw [ownSame] at payloadSame
    rw [← payloadSame]
    simp only [SourcePruningEnumerationEdgeInputs.children, List.map_map]
    rfl
  · simp [prepare, allowed] at observed

end MicroCFTA.SourcePruningEnumerationCachedOwn
