/-- The ready prefix and actual child return derive fresh arity without a gate premise. -/
theorem observed_projected_arity
    [DecidableEq (SourceGuards.Guard FullSyntax.Formula)] [DecidableEq (EdgeKey Symbol Constraint)]
    (le : SourceGuards.Guard FullSyntax.Formula → SourceGuards.Guard FullSyntax.Formula → Bool)
    (first second combined : Allocated) (operations : SourceEqualityConstraintMemoAllocation.State)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid operations)
    (firstReady : SourceEqualityConstraintAllocation.Ready operations.constraints first.stored)
    (secondReady : SourceEqualityConstraintAllocation.Ready operations.constraints second.stored)
    (nodes : NodeCall Symbol Constraint) (edges : EdgeCall Symbol Constraint)
    (calls : Calls (fun domain left right => nodes ⟨domain, left, right⟩))
    (domain : Cache.Interned DomainKey) (left right : EdgeValue Symbol Constraint)
    (state : Machine Symbol Constraint) (valid : Valid state) (known : Domain state domain)
    (leftResident : EdgeResident state.heap left) (rightResident : EdgeResident state.heap right)
    (prepared : (SourceEqualityIntersectionEdgeAllocation.run le first second
      left.children.length right.children.length operations).1 = .ok (.ready combined))
    (result : EdgeValue Symbol Constraint) (final : Machine Symbol Constraint)
    (done : interpret nodes edges
      (SourceEqualityNativeCheckedCode.children domain left right combined) state = .done result final)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project result.entry.key.constraint = some (tries, residual)) :
    ∃ values after,
      WalkTrace (fun pair => nodes ⟨domain, pair.1, pair.2⟩)
        (left.children.zip right.children) state values after ∧
      SourceRecursiveIntersectionKernel.work
        (makeEdge left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) values) after =
          .done result final ∧
      result.entry.key.symbol = left.entry.key.symbol ∧
      result.entry.key.constraint = SourceEqualityConjoinAllocation.readback combined ∧
      result.children = values ∧ result.children.length = left.children.length ∧
      (∀ trie ∈ tries, EqualityTrie.Valid trie) ∧
      ∀ start, arityAllows result.children.length (suspendedVars start tries) = true := by
