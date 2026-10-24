import MicroCFTA.SourceEqualityMkEdgeArity
import MicroCFTA.MergedPhysicalGroupEdges
import MicroCFTA.SourcePruningEnumerationConstraint
import MicroCFTA.SourcePruningTemplates

namespace MicroCFTA.SourcePruningEnumerationOwnArity
open InternedConstructorTemplates EnumerationState EnumerationCorrectness
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- The same accepted checked edge supplies valid own tries within its actual returned arity. -/
theorem accepted_projected_arity [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)]
    (symbol : Symbol) (original : Constraint) (stored : SourceEqualityConstraintAllocation.Value)
    (children : List (InternedConstructorTemplates.Value Symbol Constraint))
    (before : SourceEqualityConstraintMemoAllocation.State)
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (physical : SourceEqualityPhysicalPayload.read original.equalities = .ok stored.payload)
    (storedReady : SourceEqualityConstraintAllocation.Ready before.constraints stored)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before)
    (heapReady : SourceEqualityRequiredCache.Ready heap)
    (available : InternedNestedProvenance.Values heap children)
    (checked : (SourceEqualityMkEdgeAllocation.check stored original.guard children.length before).1 = .ok true) :
    let built := InternedConstructorTemplates.run (InternedConstructorTemplates.makeEdge symbol original children) heap
    SourceEqualityMkEdgeAllocation.build symbol stored original.guard children before heap =
      (.ok built.1, (SourceEqualityMkEdgeAllocation.check stored original.guard children.length before).2, built.2) ∧
    SourceEqualityConstraintMemoAllocation.Valid
      (SourceEqualityMkEdgeAllocation.check stored original.guard children.length before).2 ∧
    SourceEqualityConstraintMemoAllocation.Grows before
      (SourceEqualityMkEdgeAllocation.check stored original.guard children.length before).2 ∧
    SourceEqualityRequiredCache.Keeps heap built.2 ∧
    built.1.entry.key.symbol = symbol ∧ built.1.entry.key.constraint = original ∧ built.1.children = children ∧
    ∃ classes : EqualityNormalize.Constraints,
      SourceCompactGuards.sourceEqualities built.1.entry.key.constraint = some classes ∧
      SourcePruningEnumerationConstraint.project built.1.entry.key.constraint =
        some (EnumerationEquality.readClasses classes,
          if (SourceCompactGuards.positive original.guard).isSome then none else some original) ∧
      (∀ trie ∈ EnumerationEquality.readClasses classes, EqualityTrie.Valid trie) ∧
      (∀ paths ∈ classes, ∀ path,
        path ∈ EqualityTrie.fromPathTrie (EnumerationEquality.classTrie paths) ↔ path ∈ paths) ∧
      ∀ start : Nat, arityAllows built.1.children.length
        (suspendedVars start (EnumerationEquality.readClasses classes)) = true := by
  have reconstructed : SourceEqualityAccessorAllocation.constraint stored original.guard = original := by
    exact congrArg
      (fun equalities : Option EqualityNormalize.Constraints =>
        (⟨equalities, original.guard⟩ : Constraint))
      (SourceEqualityConstraintAllocation.read_classes original.equalities cached stored.payload physical)
  obtain ⟨checkedExact, checkedValid, checkedGrowth⟩ :=
    SourceEqualityMkEdgeAllocation.check_correct stored original.guard children.length before valid storedReady
  have accepted : SourceEqualityMkEdgeAllocation.accepted original children.length = true := by
    rw [reconstructed] at checkedExact
    exact Except.ok.inj (checkedExact.symm.trans checked)
  have fits : SourceEqualityMkEdgeAllocation.fits children.length
        (SourceCompactGuards.sourceEqualities original) = true := by
    by_cases rejected : SourceEqualityMkEdgeAllocation.contradictory original = true
    · simp only [SourceEqualityMkEdgeAllocation.accepted, rejected, ↓reduceIte,
        Bool.false_eq_true] at accepted
    · simpa only [SourceEqualityMkEdgeAllocation.accepted, rejected, ↓reduceIte] using accepted
  obtain ⟨classes, source, rootBounds⟩ :=
    (SourceEqualityMkEdgeArity.fits_exact children.length
      (SourceCompactGuards.sourceEqualities original)).mp fits
  let actualBuilt : InternedConstructorTemplates.EdgeValue Symbol Constraint ×
        InternedConstructorTemplates.State Symbol Constraint :=
      InternedConstructorTemplates.run (InternedConstructorTemplates.makeEdge symbol original children) heap
  obtain ⟨receipt, _receiptValid, _receiptGrowth⟩ :=
    SourceEqualityMkEdgeAllocation.build_receipt symbol stored original.guard children before heap valid storedReady
  simp only [reconstructed, accepted, SourceEqualityMkEdgeAllocation.work,
    SourceEqualityMkEdgeAllocation.outputState, ↓reduceIte] at receipt
  rw [receipt] at _receiptValid _receiptGrowth
  dsimp only at _receiptValid _receiptGrowth
  obtain ⟨symbolSame, guardSame, childrenSame⟩ :=
    MergedPhysicalGroupEdges.makeEdge_fields heap heapReady.semantic.1.normal.facts symbol original children available
  obtain ⟨projected, validTries, pathReadback, _meaning⟩ :=
    (source ▸ SourcePruningEnumerationConstraint.project_complete original cached)
  change SourceEqualityMkEdgeAllocation.build symbol stored original.guard children before heap =
    (.ok actualBuilt.1, (SourceEqualityMkEdgeAllocation.check stored original.guard children.length before).2, actualBuilt.2) ∧ _
  refine ⟨receipt, checkedValid, checkedGrowth, ?_, symbolSame, guardSame, childrenSame,
    classes, ?_, ?_, validTries, pathReadback, ?_⟩
  · exact SourceEqualityMkEdgeAllocation.work_keeps symbol original children true heap heapReady available
  · rw [guardSame]
    exact source
  · rw [guardSame]
    exact projected
  · intro start
    rw [childrenSame]
    apply (fresh_arity_iff children.length start (EnumerationEquality.readClasses classes)).mpr
    intro trie trieMember index suffix path
    obtain ⟨paths, pathsMember, same⟩ := List.mem_map.mp trieMember
    subst trie
    exact rootBounds paths pathsMember (index :: suffix)
      ((pathReadback paths pathsMember (index :: suffix)).mp path)

end MicroCFTA.SourcePruningEnumerationOwnArity
