/-- An actual checked return supplies valid own tries and fresh arity for its observed projection. -/
theorem observed_projected_arity [DecidableEq (EdgeKey Symbol Constraint)]
    (symbol : Symbol) (original : Constraint) (stored : SourceEqualityConstraintAllocation.Value)
    (children : List (Value Symbol Constraint))
    (before : SourceEqualityConstraintMemoAllocation.State)
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (physical : SourceEqualityPhysicalPayload.read original.equalities = .ok stored.payload)
    (storedReady : SourceEqualityConstraintAllocation.Ready before.constraints stored)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before)
    (heapReady : SourceEqualityRequiredCache.Ready heap)
    (available : SourceEqualityMkEdgeAllocation.accepted original children.length = true →
      InternedNestedProvenance.Values heap children)
    (edge : EdgeValue Symbol Constraint)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (after : InternedConstructorTemplates.State Symbol Constraint)
    (observed : SourceEqualityMkEdgeAllocation.build symbol stored original.guard children before heap =
      (.ok edge, operations, after))
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual)) :
    (∀ trie ∈ tries, EqualityTrie.Valid trie) ∧
      ∀ start, arityAllows edge.children.length (suspendedVars start tries) = true := by
  obtain ⟨_checked, receipt, _operationsValid, _operationsGrowth, _kept, _resident,
    _symbol, _guard, _children, classes, _source, actualProjection, validTries,
    _pathReadback, ownArity⟩ :=
    SourcePruningEnumerationCheckedArity.checked_projected_arity symbol original stored children
      before heap cached physical storedReady valid heapReady available
  have edgeSame := Except.ok.inj (congrArg Prod.fst (receipt.symm.trans observed))
  rw [edgeSame] at actualProjection ownArity
  have same := Option.some.inj (actualProjection.symm.trans projected)
  have triesSame : EnumerationEquality.readClasses classes = tries := congrArg Prod.fst same
  rw [← triesSame]
  exact ⟨validTries, ownArity⟩
