def ResultRelated {OldOutput : Type u'} {OldReason : Type v'}
    (outputsRelated : Output → OldOutput → Prop) (reasonsRelated : Reason → OldReason → Prop)
    (flat : Result Output Reason width)
    (earlier : SourcePruningEnumerationNativeContinuations.Result OldOutput OldReason width) : Prop :=
  match flat, earlier with
  | .complete processed outputs caller queries, .complete oldProcessed oldOutputs oldCaller oldQueries =>
      SourceFlatPruningNativeBranches.ReceiptsRelated processed oldProcessed ∧
        SourceFlatPruningNativeBranches.OrderedRelated outputsRelated outputs oldOutputs ∧
        caller = oldCaller ∧ queries = oldQueries
  | .stopped processed outputs current, .stopped oldProcessed oldOutputs oldCurrent =>
      SourceFlatPruningNativeBranches.ReceiptsRelated processed oldProcessed ∧
        SourceFlatPruningNativeBranches.OrderedRelated outputsRelated outputs oldOutputs ∧
        StopRelated reasonsRelated current oldCurrent
  | _, _ => False
