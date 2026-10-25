enumerateNode _ EmptyNode = mzero
enumerateNode scs n =
    let (hereConstraints, descendantConstraints) = Sequence.partition (\(SuspendedConstraint pt _) -> isTerminalPathTrie pt) scs
     in case hereConstraints of
            Sequence.Empty -> case n of
                Mu _ -> TermFragmentUVar <$> addUVarValue (Just n)
                InternedUnion _ -> TermFragmentUVar <$> addUVarValue (Just n)
                Node _ -> do
                    edgesOf <- gets _edgesOf
                    enumerateEdge scs =<< branches (edgesOf n)
                Rec recId ->
                    error $
                        "enumerateNode: unexpected unresolved recursive reference "
                            <> show recId
                            <> " for symbol type "
                            <> show (typeRep @symbol)
            (x :<| xs) -> do
                reps <- mapM (getUVarRepresentative . scGetUVar) hereConstraints
