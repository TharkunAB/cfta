/-- One emitted output retains its actual head, original callback admission and recursive history. -/
def InvocationHistoryAt
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (metadata : SourcePruningRecordTypes.Metadata Typing) (recursiveFuel : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (workFuel : Nat) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (uv : Nat) (scs : List Suspended) (edges : List (EdgeValue Symbol Constraint))
    (capturedMass inherited : Nat) (output : Output (bits + 2) Typing) : Prop :=
  ∃ edge ∈ edges, ∃ (headSeed : Seed) (headInventory : Inventory)
    (headCaller : Caller (bits + 2)) (headMemos : Memos) (headBound : Nat)
    (fragment : Fragments.Fragment Symbol) (reached : Caller (bits + 2)) (after : Cached)
    (returnedInventory : Inventory) (returnedMemos : Memos)
    (recorded : SourcePruningRecordTypes.Metadata Typing) (callbackCore : EnumerationState.State Symbol Constraint),
    Post formulas solver headInventory caller headCaller headMemos ∧
    SourcePruningEnumerationHookInvocation.Invocation
      (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel)
        graph templates stop order workFuel metadata uv)
      checkEmpty workFuel workFuel workFuel workFuel workFuel uv scs before edges caller memos.query
        fragment reached returnedMemos.query after ∧
    SourcePruningEnumerationCapturedEdge.run checkEmpty workFuel workFuel workFuel workFuel workFuel
      uv scs edge headCaller before headMemos.query = some (.complete fragment reached returnedMemos.query after) ∧
    SourcePruningEnumerationNativeHookResources.CompletedHeadReceipt headSeed inherited formulas solver
      headInventory headCaller headMemos metadata before checkEmpty uv scs edge headBound fragment reached
      returnedMemos.query after returnedInventory returnedMemos ∧
    SourcePruningEnumerationRecursive.RecursiveCallbackAdmission formulas solver returnedInventory reached returnedMemos
      metadata after uv fragment recursiveFuel (afterHead headSeed inherited) (massCeil headSeed capturedMass inherited) ∧
    ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates workFuel metadata uv (.inl fragment) after.core) =
      [.ok ((false, recorded), callbackCore)] ∧
    SourcePruningEnumerationRecursive.RecursiveCallbackAdmission formulas solver returnedInventory reached returnedMemos
      recorded (EnumerationExpandableIndex.frame callbackCore after) uv fragment recursiveFuel
      (afterHead headSeed inherited) (massCeil headSeed capturedMass inherited) ∧
    SourcePruningEnumerationRecursive.ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver workFuel recursiveFuel returnedInventory reached returnedMemos recorded
      (EnumerationExpandableIndex.frame callbackCore after) (afterHead headSeed inherited)
      (massCeil headSeed capturedMass inherited)
      (SourcePruningEnumerationRestart.decision stop order recorded (EnumerationExpandableIndex.frame callbackCore after)) output
