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

variable [DecidableEq Symbol] [DecidableEq Node]

/-- One actual completed head retains its input admission and both own endpoint packets. -/
structure CompletedHeadReceipt
    (seed : Seed) (inherited : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos)
    (metadata : SourcePruningRecordTypes.Metadata Typing) (before : Cached)
    (checkEmpty : Bool) (uv : Nat) (scs : List Suspended) (edge : EdgeValue Symbol Constraint)
    (bound : Nat) (fragment : Fragments.Fragment Symbol) (reached : Caller (bits + 2))
    (saved : Queries) (after : Cached) (returnedInventory : Inventory) (returnedMemos : Memos) : Prop where
  /-- The certificate starts at the literal head input. -/
  admission : HeadAdmission seed formulas solver inventory caller memos metadata before uv scs edge
  /-- The actual head keeps every native postcondition at its full memo state. -/
  post : Post formulas solver returnedInventory caller reached returnedMemos
  /-- The returned queries are the query field of that full memo state. -/
  query : returnedMemos.query = saved
  /-- Native effects retain the original captured cache at the reached caller. -/
  captured : Packet formulas solver returnedInventory reached returnedMemos metadata before
  /-- The actual completed cache has its own recursive packet at the same caller. -/
  completed : Packet formulas solver returnedInventory reached returnedMemos metadata after
  /-- The reached caller fits the original padded head forecast. -/
  bounded : Fits (afterHead seed inherited).2 reached.checked
  /-- The reached native heap uses the same padded head carrier. -/
  known : Heap (fun guard => guard ∈ (afterHead seed inherited).1) reached.checked.native.machine.heap
  /-- Actual completion passes the original arity check. -/
  allowed : arityAllows edge.children.length scs = true
  /-- Actual completion uses a successful projection of this edge's own constraint. -/
  projected : ∃ (tries : List EqualityTrie.Trie) (residual : Option Constraint),
    SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual)
  /-- Every larger common work bound returns this same actual completed receipt. -/
  running : ∀ extra, SourcePruningEnumerationCapturedEdge.run checkEmpty
    (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
    uv scs edge caller before memos.query = some (.complete fragment reached saved after)

private theorem completed_supported
    (checkEmpty : Bool) (r n p h k uv : Nat) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (caller : Caller (bits + 2)) (before : Cached) (queries : Queries)
