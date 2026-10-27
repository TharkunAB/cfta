def OrdinaryHistoryReceipt
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (metadata : Metadata Typing) (checkEmpty : Bool) (workFuel uv : Nat)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (fragment : Fragment) (reached : Caller (bits + 2)) (after : Cached)
    (returnedInventory : Inventory) (returnedMemos : Memos) : Prop :=
  ∃ (entered : Cached) (handle : Nat) (scs : List Suspended) (decoded : Node)
    (edge : EdgeValue Symbol Constraint) (headSeed : Seed) (inherited : Nat)
    (headInventory : Inventory) (headCaller : Caller (bits + 2)) (headMemos : Memos) (headBound : Nat),
    Packet formulas solver inventory caller memos metadata before ∧
    ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap workFuel uv before.core) =
      [.ok ((uv, handle, scs, decoded), entered.core)] ∧
    Packet formulas solver inventory caller memos metadata entered ∧
    Post formulas solver headInventory caller headCaller headMemos ∧
    SourcePruningEnumerationCapturedEdge.run checkEmpty workFuel workFuel workFuel workFuel workFuel
      uv scs edge headCaller entered headMemos.query = some (.complete fragment reached returnedMemos.query after) ∧
    SourcePruningEnumerationNativeHookResources.CompletedHeadReceipt headSeed inherited formulas solver
      headInventory headCaller headMemos metadata entered checkEmpty uv scs edge headBound fragment reached
      returnedMemos.query after returnedInventory returnedMemos