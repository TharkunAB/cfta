def HookResultRelated {OldOutput : Type u'} {OldReason : Type v'}
    (outputsRelated : Output → OldOutput → Prop) (reasonsRelated : Reason → OldReason → Prop)
    (flat : HookResult Output Reason width)
    (earlier : SourcePruningEnumerationNativeContinuations.HookResult OldOutput OldReason width) : Prop :=
  match flat, earlier with
  | .complete outputs caller queries, .complete oldOutputs oldCaller oldQueries =>
      SourceFlatPruningNativeBranches.OrderedRelated outputsRelated outputs oldOutputs ∧
        caller = oldCaller ∧ queries = oldQueries
  | .stopped outputs reason reached, .stopped oldOutputs oldReason oldReached =>
      SourceFlatPruningNativeBranches.OrderedRelated outputsRelated outputs oldOutputs ∧
        reasonsRelated reason oldReason ∧ reached = oldReached
  | _, _ => False
