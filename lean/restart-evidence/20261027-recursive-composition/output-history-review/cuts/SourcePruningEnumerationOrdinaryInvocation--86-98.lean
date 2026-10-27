theorem continueWith_output_restart
    (recur : Metadata Typing → Caller width → Queries → Cached → Option Next →
      Result (SourcePruningEnumerationRecursive.Output width Typing) (Failure width Typing) width)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (fuel : Nat) (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller width) (queries : Queries) (before : Cached) :
    ∀ output ∈ hookOutputs (continueWith recur graph templates stop order fuel metadata uv fragment caller queries before),
      ∃ updated core,
        ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates fuel metadata uv (.inl fragment) before.core) =
          [.ok ((false, updated), core)] ∧
        output ∈ hookOutputs (recur updated caller queries (EnumerationExpandableIndex.frame core before)
          (SourcePruningEnumerationRestart.decision stop order updated (EnumerationExpandableIndex.frame core before))) := by
