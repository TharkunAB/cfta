
/-- An actual terminal row preserves old carriers and supplies every returned hole. -/
theorem successful_carriers
    (checkEmpty : Bool) (r n p h : Nat) (first : Suspended) (rest : List Suspended)
    (waiting : EnumerationWaitingIndex.Waiting) (caller : Caller width) (before : Core)
    (incoming : Node) (incomingScs : List Suspended) (queries : Queries)
    (fragment : Fragment) (afterCaller : Caller width) (savedQueries : Queries)
    (outer after : Core) (moved : EnumerationWaitingIndex.Waiting)
    (total : UnionFind.Total before.representatives) (references : ReferencesCarry before)
    (observed : run checkEmpty r n p h first rest waiting caller before incoming incomingScs queries =
      (.ok (some [.ok (fragment, after)]), afterCaller, savedQueries, outer, moved)) :
    UnionFind.Total after.representatives ∧ PreservesCarriers before after ∧
      ReferencesCarry after ∧ FragmentCarries after fragment := by
  unfold run at observed
  split at observed
  next empty => cases observed
  next nonempty =>
    split at observed
    next recorded winner transfer joined prefixObserved =>
      have prefixSuccess : Success (SourcePruningEnumerationTerminalPrefix.run r first rest waiting)
          before (recorded, winner, transfer) joined := by
        rw [Success, prefixObserved]
        exact List.mem_singleton_self _
      have joinedFacts := SourcePruningEnumerationTerminalPrefix.run_carriers r first rest waiting
        before joined recorded winner transfer total references prefixSuccess
      rcases foldObserved : SourcePruningEnumerationFold.run checkEmpty n p h recorded caller joined winner queries with
        ⟨foldResult, foldCaller, foldQueries, foldOuter⟩
      rw [foldObserved] at observed
      have foldFacts := SourcePruningEnumerationFold.run_carriers checkEmpty n p h recorded caller joined
        winner queries foldResult foldCaller foldQueries foldOuter joinedFacts.1 joinedFacts.2.2.2
        joinedFacts.2.2.1 foldObserved
      cases foldResult with
      | error fault => cases observed
      | ok possible =>
        cases possible with
        | none => cases observed
        | some raw =>
          dsimp only at observed
          split at observed
          next empty => cases observed
          next folded =>
            have foldedSame := SourcePruningEnumerationFold.singleton_core checkEmpty n p h recorded
              caller joined winner queries folded foldCaller foldQueries foldOuter foldObserved
            have foldedTotal : UnionFind.Total folded.representatives := by simpa only [foldedSame] using foldFacts.1
            have foldedReferences : ReferencesCarry folded := by simpa only [foldedSame] using foldFacts.2.2
            have foldedPreserves : PreservesCarriers joined folded := by simpa only [foldedSame] using foldFacts.2.1
            have incomingFacts := SourcePruningEnumerationIncomingNode.run_carriers checkEmpty r n p h
              foldCaller folded winner incoming incomingScs foldQueries foldedTotal foldedReferences
            rcases incomingObserved : SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
                foldCaller folded winner incoming incomingScs foldQueries with
              ⟨incomingResult, reached, saved, read⟩
            rw [incomingObserved] at observed incomingFacts
            cases incomingResult with
            | error fault => cases observed
            | ok result =>
              cases result with
              | none => cases observed
              | some incomingRaw =>
                have rowsSame := congrArg Prod.fst observed
                dsimp only at rowsSame
                have mapped := Option.some.inj (Except.ok.inj rowsSame)
                have single : incomingRaw = [.ok ((), after)] := by
                  cases incomingRaw with
                  | nil => cases mapped
                  | cons row rest =>
                    cases row with
                    | error error => cases mapped
                    | ok value =>
                      rcases value with ⟨⟨⟩, returned⟩
                      have fields := List.cons.inj mapped
                      have coreSame : returned = after := (Prod.mk.inj (Except.ok.inj fields.1)).2
                      have restEmpty : rest = [] := List.map_eq_nil_iff.mp fields.2
                      simp only [coreSame, restEmpty]
                have fragmentSame : fragment = .hole winner := by
                  rw [single] at mapped
                  exact (Prod.mk.inj (Except.ok.inj (List.cons.inj mapped).1)).1.symm
                obtain ⟨afterTotal, preserved, afterReferences, carried⟩ := incomingFacts.2 after (by rw [single])
                refine ⟨afterTotal, joinedFacts.2.1.trans (foldedPreserves.trans preserved), afterReferences, ?_⟩
                rw [fragmentSame]
                exact fragmentCarries_hole after winner carried
          next other => cases observed
    next other => cases observed

end MicroCFTA.SourcePruningEnumerationTerminal
