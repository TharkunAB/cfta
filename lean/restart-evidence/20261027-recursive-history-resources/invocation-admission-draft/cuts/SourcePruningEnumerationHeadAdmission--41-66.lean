structure HeadAdmission
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos)
    (metadata : SourcePruningRecordTypes.Metadata Typing) (before : Cached)
    (uv : Nat) (scs : List Suspended) (edge : EdgeValue Symbol Constraint) : Prop where
  /-- The full input memo state and captured cache satisfy the recursive packet. -/
  packet : Packet formulas solver inventory caller memos metadata before
  /-- The captured slot is a live pending root. -/
  ready : EnumerationDriver.Ready uv before.core
  /-- Stored suspended references avoid the captured class. -/
  incoming : EnumerationReferences.IncomingAvoid uv before.core
  /-- The actual native caller fits the original numeric profile. -/
  bounded : Fits seed.2 caller.checked
  /-- Every current native guard belongs to the original carrier. -/
  known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap
  /-- The stored ordinary parent contains this exact edge. -/
  source : ∃ (handle : Nat) (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
      (storedEdges : List (EdgeValue Symbol Constraint)) (depth : Nat)
      (free : List InternedBinderProtocol.Reference),
    before.core.values[uv]? = some (.unenumerated (some handle) scs) ∧
    lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry storedEdges depth free) ∧
    edge ∈ storedEdges
  /-- The same input seed reserves this edge's actual mixed-query cost. -/
  reserved : SourcePruningEnumerationIncomingReservation.Reserved bits seed
    (edgeCost scs before.core.counter edge)
