  | .complete processed _ _ | .stopped processed _ => processed

/-- Actual prefix receipts supply the contexts used to certify completed branch caches. -/
theorem observed_canonical
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller width) (before : Cached) (checkEmpty : Bool)
    (uv handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (storedEdges selectedEdges : List (EdgeValue Symbol Constraint))
    (depth : Nat) (free : List InternedBinderProtocol.Reference) (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory caller memos)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (decoded : lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry storedEdges depth free))
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (selected : ∀ edge ∈ selectedEdges, edge ∈ storedEdges)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (pending : InputsPending before.core scs)
    (canonical : Canonical before.core)
    {r n p h k : Nat} {result : Result width}
    (observed : SourcePruningEnumerationNativeBranches.run checkEmpty r n p h k
      uv scs before selectedEdges caller memos.query = result)
    (receiptPosts : ∀ receipt ∈ processedReceipts result,
      ∃ (reached : Caller width) (saved : Queries) (next : Inventory) (final : Memos),
        SourcePruningEnumerationNativeBranches.advance receipt = some (reached, saved) ∧
        Post formulas solver next caller reached final ∧ final.query = saved) :
    ∀ (fragment : Fragment) (reached : Caller width) (saved : Queries) (after : Cached),
      .complete fragment reached saved after ∈ processedReceipts result → Canonical after.core := by
