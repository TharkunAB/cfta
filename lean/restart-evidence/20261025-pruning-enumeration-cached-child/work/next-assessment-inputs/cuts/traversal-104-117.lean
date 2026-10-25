/-- Run one captured edge prefix and record its residual only after every child completes. -/
noncomputable def prepare (scs : List EnumerationState.Suspended)
    (edge : InternedConstructorTemplates.EdgeValue Symbol Constraint) :
    Option (EnumerateM Symbol Constraint (Option (Fragments.Fragment Symbol)))
 :=
  match SourcePruningEnumerationEdgePrefix.prepare scs edge with
  | none => none
  | some prefixAction => some (prefixAction >>= fun packet =>
      runStaged packet.2.1 >>= fun childrenResult =>
        match childrenResult with
        | none => pure none
        | some fragments =>
            let fragment := Fragments.Fragment.node packet.1 fragments
            EnumerationSchedule.recordResidual packet.2.2 fragment >>= fun _ => pure (some fragment))
