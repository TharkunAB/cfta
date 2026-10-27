def ResultRelated (flat : Result width) (earlier : SourcePruningEnumerationNativeBranches.Result width) : Prop :=
  match flat, earlier with
  | .complete processed caller queries, .complete oldProcessed oldCaller oldQueries =>
      ReceiptsRelated processed oldProcessed ∧
        caller = oldCaller ∧ queries = oldQueries
  | .stopped processed current, .stopped oldProcessed oldCurrent =>
      ReceiptsRelated processed oldProcessed ∧
        match current, oldCurrent with
        | none, none => True
        | some first, some second => SourceFlatPruningSelectedEdge.ResultRelated first second
        | _, _ => False
  | _, _ => False
