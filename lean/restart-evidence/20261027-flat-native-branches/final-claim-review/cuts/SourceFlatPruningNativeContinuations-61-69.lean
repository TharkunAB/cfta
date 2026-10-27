def StopRelated {OldReason : Type v'} (reasonsRelated : Reason → OldReason → Prop)
    (flat : Stop Reason width)
    (earlier : SourcePruningEnumerationNativeContinuations.Stop OldReason width) : Prop :=
  match flat, earlier with
  | .edge current, .edge oldCurrent => OptionalReceiptRelated current oldCurrent
  | .continuation current reason reached, .continuation oldCurrent oldReason oldReached =>
      SourceFlatPruningSelectedEdge.ResultRelated current oldCurrent ∧
        reasonsRelated reason oldReason ∧ reached = oldReached
  | _, _ => False
