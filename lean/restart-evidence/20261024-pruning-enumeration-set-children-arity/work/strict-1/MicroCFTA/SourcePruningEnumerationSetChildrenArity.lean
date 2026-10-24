import MicroCFTA.SourcePruningEnumerationOwnArity
import MicroCFTA.EqualityLeafProjectionSetChildren

namespace MicroCFTA.SourcePruningEnumerationSetChildrenArity
open InternedConstructorTemplates EnumerationState EnumerationCorrectness
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Equal-length setChildren retains the checked edge's constraint and projected arity at the current heap. -/
theorem accepted_setChildren_arity [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)]
    (symbol : Symbol) (original : Constraint) (stored : SourceEqualityConstraintAllocation.Value)
    (children replacements : List (InternedConstructorTemplates.Value Symbol Constraint))
    (before : SourceEqualityConstraintMemoAllocation.State)
    (heap current : InternedConstructorTemplates.State Symbol Constraint)
    (fallback : Symbol → List (InternedConstructorTemplates.Value Symbol Constraint) → Constraint →
      InternedConstructorTemplates.Work Symbol Constraint (InternedConstructorTemplates.EdgeValue Symbol Constraint))
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (physical : SourceEqualityPhysicalPayload.read original.equalities = .ok stored.payload)
    (storedReady : SourceEqualityConstraintAllocation.Ready before.constraints stored)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before)
    (heapReady : SourceEqualityRequiredCache.Ready heap)
    (available : InternedNestedProvenance.Values heap children)
    (checked : (SourceEqualityMkEdgeAllocation.check stored original.guard children.length before).1 = .ok true)
    (currentReady : SourceEqualityRequiredCache.Ready current)
    (replacementAvailable : InternedNestedProvenance.Values current replacements)
    (sameLength : replacements.length = children.length) :
    let built := InternedConstructorTemplates.run (InternedConstructorTemplates.makeEdge symbol original children) heap
    let rebuilt := InternedConstructorTemplates.run
      (EqualityLeafProjectionSetChildren.setChildren fallback built.1 replacements) current
    SourceEqualityMkEdgeAllocation.build symbol stored original.guard children before heap =
      (.ok built.1, (SourceEqualityMkEdgeAllocation.check stored original.guard children.length before).2, built.2) ∧
    SourceEqualityConstraintMemoAllocation.Valid
      (SourceEqualityMkEdgeAllocation.check stored original.guard children.length before).2 ∧
    SourceEqualityConstraintMemoAllocation.Grows before
      (SourceEqualityMkEdgeAllocation.check stored original.guard children.length before).2 ∧
    SourceEqualityRequiredCache.Keeps heap built.2 ∧
    built.1.entry.key.symbol = symbol ∧ built.1.entry.key.constraint = original ∧ built.1.children = children ∧
    EqualityLeafProjectionSetChildren.setChildren fallback built.1 replacements =
      InternedConstructorTemplates.makeEdge symbol original replacements ∧
    rebuilt = InternedConstructorTemplates.run (InternedConstructorTemplates.makeEdge symbol original replacements) current ∧
    SourceEqualityRequiredCache.Keeps current rebuilt.2 ∧
    InternedEdgeResidency.EdgeResident rebuilt.2 rebuilt.1 ∧
    rebuilt.1.entry.key.symbol = symbol ∧ rebuilt.1.entry.key.constraint = original ∧ rebuilt.1.children = replacements ∧
    ∃ classes : EqualityNormalize.Constraints,
      SourceCompactGuards.sourceEqualities built.1.entry.key.constraint = some classes ∧
      SourceCompactGuards.sourceEqualities rebuilt.1.entry.key.constraint = some classes ∧
      SourcePruningEnumerationConstraint.project built.1.entry.key.constraint =
        some (EnumerationEquality.readClasses classes,
          if (SourceCompactGuards.positive original.guard).isSome then none else some original) ∧
      SourcePruningEnumerationConstraint.project rebuilt.1.entry.key.constraint =
        some (EnumerationEquality.readClasses classes,
          if (SourceCompactGuards.positive original.guard).isSome then none else some original) ∧
      (∀ trie ∈ EnumerationEquality.readClasses classes, EqualityTrie.Valid trie) ∧
      (∀ paths ∈ classes, ∀ path,
        path ∈ EqualityTrie.fromPathTrie (EnumerationEquality.classTrie paths) ↔ path ∈ paths) ∧
      ∀ start : Nat, arityAllows built.1.children.length
        (suspendedVars start (EnumerationEquality.readClasses classes)) = true ∧
        arityAllows rebuilt.1.children.length
          (suspendedVars start (EnumerationEquality.readClasses classes)) = true := by
  let actualBuilt : InternedConstructorTemplates.EdgeValue Symbol Constraint ×
        InternedConstructorTemplates.State Symbol Constraint :=
      InternedConstructorTemplates.run (InternedConstructorTemplates.makeEdge symbol original children) heap
  let actualRebuilt : InternedConstructorTemplates.EdgeValue Symbol Constraint ×
        InternedConstructorTemplates.State Symbol Constraint :=
      InternedConstructorTemplates.run
        (EqualityLeafProjectionSetChildren.setChildren fallback actualBuilt.1 replacements) current
  obtain ⟨receipt, checkedValid, checkedGrowth, oldKept, oldSymbol, oldGuard,
    oldChildren, classes, oldSource, oldProjected, validTries, pathReadback, oldArity⟩ :=
    SourcePruningEnumerationOwnArity.accepted_projected_arity symbol original stored children
      before heap cached physical storedReady valid heapReady available checked
  have direct : EqualityLeafProjectionSetChildren.setChildren fallback actualBuilt.1 replacements =
        InternedConstructorTemplates.makeEdge symbol original replacements := by
    rw [EqualityLeafProjectionSetChildren.same_arity fallback actualBuilt.1 replacements
      (by rw [oldChildren]; exact sameLength), oldSymbol, oldGuard]
  have rebuiltSame : actualRebuilt =
        InternedConstructorTemplates.run (InternedConstructorTemplates.makeEdge symbol original replacements) current := by
    dsimp only [actualRebuilt]
    rw [direct]
  obtain ⟨newKept, newResident, newChildren⟩ :=
    SourceEqualityRequiredCache.edge symbol original replacements current currentReady replacementAvailable
  obtain ⟨newSymbol, newGuard, _sameChildren⟩ :=
    MergedPhysicalGroupEdges.makeEdge_fields current currentReady.semantic.1.normal.facts
      symbol original replacements replacementAvailable
  rw [← rebuiltSame] at newKept newResident newChildren newSymbol newGuard _sameChildren
  change SourceEqualityMkEdgeAllocation.build symbol stored original.guard children before heap =
    (.ok actualBuilt.1, (SourceEqualityMkEdgeAllocation.check stored original.guard children.length before).2, actualBuilt.2) ∧ _
  refine ⟨receipt, checkedValid, checkedGrowth, oldKept, oldSymbol, oldGuard, oldChildren,
    direct, rebuiltSame, newKept, newResident, newSymbol, newGuard, newChildren,
    classes, oldSource, ?_, oldProjected, ?_, validTries, pathReadback, ?_⟩
  · rw [newGuard]
    simpa only [oldGuard] using oldSource
  · rw [newGuard]
    simpa only [oldGuard] using oldProjected
  · intro start
    refine ⟨oldArity start, ?_⟩
    simpa only [newChildren, sameLength, oldChildren] using oldArity start

end MicroCFTA.SourcePruningEnumerationSetChildrenArity
