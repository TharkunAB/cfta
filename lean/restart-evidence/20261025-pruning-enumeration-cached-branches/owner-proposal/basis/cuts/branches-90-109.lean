          exact SourcePruningEnumerationRawExact.prepare_exact scs edge action before after _ prepared observed
        refine ⟨[.ok (some (childrenResult.map (fun fragments =>
          Fragments.Fragment.node edge.entry.key.symbol fragments)), after)] :: tailRows,
          .cons ?_ tailRelated, ?_⟩
        · simp only [allowed, ↓reduceIte, projected]
          exact ⟨action, _, after, prepared, observed, rfl, afterAligned, afterRealized⟩
        · change ExceptT.run (run scs (edge :: rest) before) = _
          rw [consRaw, prepared]
          change ExceptT.run ((action >>= fun result => pure (some result)) before) ++
            ExceptT.run (run scs rest before) = _
          rw [bind_single _ _ before after _ actionRaw, tailRaw]
          rfl
    · refine ⟨[] :: tailRows, .cons ?_ tailRelated, ?_⟩
      · simp only [allowed, Bool.false_eq_true, ↓reduceIte]
      · change ExceptT.run (run scs (edge :: rest) before) = _
        rw [consRaw, tailRaw]
        simp only [SourcePruningEnumerationEdgeTraversal.prepare,
          SourcePruningEnumerationEdgePrefix.prepare, allowed, Bool.false_eq_true, ↓reduceIte]
        rfl

