import MicroCFTA.SourcePruningEnumerationOwnArity

namespace MicroCFTA.SourcePruningEnumerationCheckedArity
open InternedConstructorTemplates EnumerationState EnumerationCorrectness
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)

/-- Both checked constructor outcomes supply projected own bounds for their actual returned edge. -/
theorem checked_projected_arity [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)]
    (symbol : Symbol) (original : Constraint) (stored : SourceEqualityConstraintAllocation.Value)
    (children : List (InternedConstructorTemplates.Value Symbol Constraint))
    (before : SourceEqualityConstraintMemoAllocation.State)
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (physical : SourceEqualityPhysicalPayload.read original.equalities = .ok stored.payload)
    (storedReady : SourceEqualityConstraintAllocation.Ready before.constraints stored)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before)
    (heapReady : SourceEqualityRequiredCache.Ready heap)
    (available : SourceEqualityMkEdgeAllocation.accepted original children.length = true →
      InternedNestedProvenance.Values heap children) :
    let keep := SourceEqualityMkEdgeAllocation.accepted original children.length
    let built := InternedConstructorTemplates.run
      (SourceEqualityMkEdgeAllocation.work symbol original children keep) heap
    let operations := SourceEqualityMkEdgeAllocation.outputState
      (SourceEqualityMkEdgeAllocation.check stored original.guard children.length before).2 keep
    (SourceEqualityMkEdgeAllocation.check stored original.guard children.length before).1 = .ok keep ∧
    SourceEqualityMkEdgeAllocation.build symbol stored original.guard children before heap =
      (.ok built.1, operations, built.2) ∧
    SourceEqualityConstraintMemoAllocation.Valid operations ∧
    SourceEqualityConstraintMemoAllocation.Grows before operations ∧
    SourceEqualityRequiredCache.Keeps heap built.2 ∧
    InternedEdgeResidency.EdgeResident built.2 built.1 ∧
    built.1.entry.key.symbol = symbol ∧
    built.1.entry.key.constraint = (if keep then original else top) ∧
    built.1.children = (if keep then children else [.empty]) ∧
    ∃ classes : EqualityNormalize.Constraints,
      SourceCompactGuards.sourceEqualities built.1.entry.key.constraint = some classes ∧
      SourcePruningEnumerationConstraint.project built.1.entry.key.constraint =
        some (EnumerationEquality.readClasses classes,
          if (SourceCompactGuards.positive built.1.entry.key.constraint.guard).isSome
            then none else some built.1.entry.key.constraint) ∧
      (∀ trie ∈ EnumerationEquality.readClasses classes, EqualityTrie.Valid trie) ∧
      (∀ paths ∈ classes, ∀ path,
        path ∈ EqualityTrie.fromPathTrie (EnumerationEquality.classTrie paths) ↔ path ∈ paths) ∧
      ∀ start : Nat, arityAllows built.1.children.length
        (suspendedVars start (EnumerationEquality.readClasses classes)) = true := by
  let actualBuilt : InternedConstructorTemplates.EdgeValue Symbol Constraint ×
        InternedConstructorTemplates.State Symbol Constraint :=
      InternedConstructorTemplates.run (SourceEqualityMkEdgeAllocation.work symbol original children
        (SourceEqualityMkEdgeAllocation.accepted original children.length)) heap
  let actualOperations : SourceEqualityConstraintMemoAllocation.State :=
      SourceEqualityMkEdgeAllocation.outputState
        (SourceEqualityMkEdgeAllocation.check stored original.guard children.length before).2
        (SourceEqualityMkEdgeAllocation.accepted original children.length)
  have reconstructed : SourceEqualityAccessorAllocation.constraint stored original.guard = original := by
    exact congrArg
      (fun equalities : Option EqualityNormalize.Constraints =>
        (⟨equalities, original.guard⟩ : Constraint))
      (SourceEqualityConstraintAllocation.read_classes original.equalities cached stored.payload physical)
  obtain ⟨checkedExact, checkedValid, checkedGrowth⟩ :=
    SourceEqualityMkEdgeAllocation.check_correct stored original.guard children.length before valid storedReady
  rw [reconstructed] at checkedExact
  obtain ⟨receipt, receiptValid, receiptGrowth⟩ :=
    SourceEqualityMkEdgeAllocation.build_receipt symbol stored original.guard children before heap valid storedReady
  rw [reconstructed] at receipt
  rw [receipt] at receiptValid receiptGrowth
  refine ⟨checkedExact, receipt, receiptValid, receiptGrowth, ?_⟩
  cases keepEq : SourceEqualityMkEdgeAllocation.accepted original children.length with
  | true =>
    have checkedTrue : (SourceEqualityMkEdgeAllocation.check stored original.guard children.length before).1 = .ok true := by
      simpa only [keepEq] using checkedExact
    obtain ⟨acceptedReceipt, _acceptedValid, _acceptedGrowth, acceptedKept,
      acceptedSymbol, acceptedGuard, acceptedChildren, classes, source, projected,
      validTries, pathReadback, ownArity⟩ :=
      SourcePruningEnumerationOwnArity.accepted_projected_arity symbol original stored children
        before heap cached physical storedReady valid heapReady (available keepEq) checkedTrue
    simp only [actualBuilt, SourceEqualityMkEdgeAllocation.work, keepEq, ↓reduceIte]
    refine ⟨acceptedKept,
      (SourceEqualityRequiredCache.edge symbol original children heap heapReady (available keepEq)).2.1,
      acceptedSymbol, acceptedGuard, acceptedChildren, classes, source, ?_, validTries, pathReadback, ownArity⟩
    simpa only [acceptedGuard] using projected
  | false =>
    have emptyAvailable : InternedNestedProvenance.Values heap
        ([.empty] : List (InternedConstructorTemplates.Value Symbol Constraint)) := by
      intro child member
      simp only [List.mem_singleton] at member
      subst child
      exact InternedProbeProvenance.empty_available heap
    obtain ⟨rejectedKept, rejectedResident, _rejectedChildReadback⟩ :=
      SourceEqualityRequiredCache.edge symbol (top : Constraint) [.empty] heap heapReady emptyAvailable
    obtain ⟨rejectedSymbol, rejectedGuard, rejectedChildren⟩ :=
      MergedPhysicalGroupEdges.makeEdge_fields heap heapReady.semantic.1.normal.facts
        symbol (top : Constraint) [.empty] emptyAvailable
    have topSource : SourceCompactGuards.sourceEqualities (top : Constraint) = some [] := by rfl
    have topProjected : SourcePruningEnumerationConstraint.project (top : Constraint) = some ([], none) := by rfl
    simp only [actualBuilt, SourceEqualityMkEdgeAllocation.work, keepEq, Bool.false_eq_true, ↓reduceIte]
    refine ⟨rejectedKept, rejectedResident, rejectedSymbol, rejectedGuard, rejectedChildren,
      [], ?_, ?_, ?_, ?_, ?_⟩
    · rw [rejectedGuard]
      exact topSource
    · rw [rejectedGuard]
      simpa only [EnumerationEquality.readClasses, List.map_nil,
        SourceEqualityConstraintConstructors.top, SourceCompactGuards.positive,
        Option.isSome_some, ↓reduceIte] using topProjected
    · simp [EnumerationEquality.readClasses]
    · simp
    · intro start
      rfl

end MicroCFTA.SourcePruningEnumerationCheckedArity
