private theorem eager_opaque_resources
    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat) (recursive : EagerResumeComplete (bits := bits) holeKey keyMatches admits graph templates
      checkEmpty edgesOf stop order formulas solver recursiveDepth)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (bound ceiling uv handle : Nat) (scs : List Suspended) (value : Node)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (available : Available caller.checked.native.machine.heap value) (closed : value.free = [])
    (dispatch : (match (generalizing := false) value with
      | .node .. => !(scs.any (fun sc => EqualityTrie.isTerminal sc.trie)) | _ => false) = false)
    (fits : Fits seed.2 caller.checked) (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling) (bucketBound : scs.length ≤ bound)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (reserved : fallbackReserved bits bound ceiling (fun retained current => eagerReserved bits recursiveDepth current retained) seed) :
    ∃ (fuel : Nat) (receipt : SelectedEdge.Result (bits + 2)) (outcome : Fold),
      (∀ extra, SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty
        (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
        uv scs value caller before memos.query = some receipt) ∧
      (∀ extra, SourcePruningEnumerationSharedReceiptContinuation.run
        (SourcePruningEnumerationSharedPreparedRecursive.continueWith
          (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
            (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
              (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
            holeKey keyMatches admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
          graph templates stop order (fuel + extra) metadata uv) caller memos.query (some receipt) = outcome) ∧
      OutcomeResources formulas solver caller
        (fallbackPlan bound ceiling (fun retained current => eagerFinal recursiveDepth current retained) seed) (finish uv outcome)
    := by
