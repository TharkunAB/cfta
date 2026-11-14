private theorem eager_captured_rows_resources
    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat)
    (recursive : EagerResumeComplete (bits := bits) holeKey keyMatches admits graph templates checkEmpty edgesOf
      stop order formulas solver recursiveDepth)
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat) (count : Nat) :
  ∀ (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (bound ceiling : Nat) (scs : List Suspended) (uv handle : Nat),
    Packet formulas solver inventory caller memos metadata before →
    EnumerationDriver.Ready uv before.core →
    before.core.values[uv]? = some (.unenumerated (some handle) scs) →
    EnumerationReferences.IncomingAvoid uv before.core →
    Fits seed.2 caller.checked → Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap →
    SourceEqualityRequiredCache.Keeps captured caller.checked.native.machine.heap →
    SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling → scs.length ≤ bound →
    ∀ (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
      (rows : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference),
    Available captured (.node parentEntry rows depth free) → free = [] →
    MergedOrdinaryHeight.height (.node parentEntry rows depth free) ≤ height + 1 →
    (∀ sc ∈ scs, sc.var < before.core.counter) → InputsPending before.core scs →
    ∀ (alternatives : List (EdgeValue Symbol Constraint)), alternatives.length ≤ count →
    (∀ edge ∈ alternatives, edge ∈ rows) →
    (∀ entry rows depth free, Available captured (.node entry rows depth free) →
      rows.length ≤ limit ∧ ∀ edge ∈ rows, edge.children.length ≤ limit ∧
        ∀ tries residual, SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
          tries.length ≤ own) →
    (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
    (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
    (∀ index, index < count → tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
      limit (bound + own) ceiling (fun retained current => eagerFinal recursiveDepth current retained)
        (fun retained current => eagerReserved bits recursiveDepth current retained)
        (iterate (fun current => tuplePlan (nodePlan limit own height) limit (bound + own) ceiling
          (fun retained current => eagerFinal recursiveDepth current retained) current) seed index)) →
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedBranching.scan
        (SourcePruningEnumerationSharedChildVisitors.visitCapturedWith
          (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
            (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
          (SourcePruningEnumerationSharedPreparedRecursive.continueWith
            (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
              (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
                (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
              holeKey keyMatches admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
            graph templates stop order (fuel + extra) metadata uv)
          (fuel + extra) uv scs) before alternatives caller memos.query = outcome) ∧
      OutcomeResources formulas solver caller
        (iterate (fun current => tuplePlan (nodePlan limit own height) limit (bound + own) ceiling
          (fun retained current => eagerFinal recursiveDepth current retained) current) seed count) (finish uv outcome)
 := by
