theorem completed_incoming_preserved
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (metadata : SourcePruningRecordTypes.Metadata Typing)
    (before : Cached)
    (packet : SourcePruningEnumerationRecursive.Packet formulas solver inventory caller memos metadata before)
    (checkEmpty : Bool) (target handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edge : EdgeValue Symbol Constraint)
    (stored : before.core.values[target]? = some (.unenumerated (some handle) scs))
    (decoded : lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry edges depth free))
    (selected : edge ∈ edges) (pending : EnumerationDependencies.InputsPending before.core scs)
    (allowed : arityAllows edge.children.length scs = true)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (ranges : SourcePruningEnumerationSelectedEdge.Ranges checkEmpty scs edge caller before memos.query)
    (held : Nat) (inside : held < before.core.counter) (root : IsRoot before.core.representatives held)
    (incoming : IncomingAvoid held before.core) (different : held ≠ target)
    {r n p h k : Nat} {fragment : Fragments.Fragment Symbol}
    {reached : Caller width} {saved : Queries} {middle after : Cached} {finishFuel : Nat}
    (observed : ∀ er en P H ek, p ≤ P → h ≤ H →
      SourcePruningEnumerationSelectedEdge.run checkEmpty (r + er) (n + en) P H (k + ek)
        scs edge caller before memos.query = .complete fragment reached saved middle)
    (finalized : SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap
      finishFuel target fragment middle = some after) :
    EnumerationDriver.Protected held before.core after.core ∧ IncomingAvoid held after.core := by
