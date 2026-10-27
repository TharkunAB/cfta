/-- An actual stable completed head retains its opaque child at the same final cache. -/
theorem completed_head_opaque_isolated
    (seed : Seed) (inherited : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (metadata : SourcePruningRecordTypes.Metadata Typing)
    (before : Cached) (checkEmpty : Bool) (uv : Nat) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (bound : Nat) (fragment : Fragment)
    (reached : Caller (bits + 2)) (saved : Queries) (headCache : Cached)
    (returnedInventory : Inventory) (returnedMemos : Memos)
    (head : CompletedHeadReceipt seed inherited formulas solver inventory caller memos metadata before
      checkEmpty uv scs edge bound fragment reached saved headCache returnedInventory returnedMemos)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (consumed suffix : List (Node × List Suspended)) (value : Node) (bucket : List Suspended)
    (location : SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries =
      consumed ++ (value, bucket) :: suffix)
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true)
    (nonterminal : bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = false) :
    ∃ held handle, lookupNode reached.checked.native.machine.heap handle = some value ∧
