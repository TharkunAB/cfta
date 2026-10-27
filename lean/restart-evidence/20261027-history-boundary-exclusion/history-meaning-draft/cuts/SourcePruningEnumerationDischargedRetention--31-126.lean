/-- A discharged output retains every child restriction of its own completed head. -/
theorem completed_head_output_retained
    (seed : Seed) (inherited : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (checkEmpty : Bool) (uv : Nat) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (bound : Nat) (fragment : Fragment)
    (reached : Caller (bits + 2)) (saved : Queries) (headCache : Cached)
    (returnedInventory : Inventory) (returnedMemos : Memos)
    (head : CompletedHeadReceipt seed inherited formulas solver inventory caller memos metadata before
      checkEmpty uv scs edge bound fragment reached saved headCache returnedInventory returnedMemos)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveFuel : Nat) (recorded : Metadata Typing) (callbackCore : Core)
    (tailSeed : Seed) (tailCeiling : Nat)
    (output : SourcePruningEnumerationRecursive.Output (bits + 2) Typing)
    (callback : ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates workFuel metadata uv
      (.inl fragment) headCache.core) = [.ok ((false, recorded), callbackCore)])
    (tail : SourcePruningEnumerationRecursive.ResourceHistory
      holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver workFuel
      recursiveFuel returnedInventory reached returnedMemos recorded
      (EnumerationExpandableIndex.frame callbackCore headCache) tailSeed tailCeiling
      (SourcePruningEnumerationRestart.decision stop order recorded
        (EnumerationExpandableIndex.frame callbackCore headCache)) output)
    (discharged : SourcePruningEnumerationRendering.Discharged output.cache.core) :
    ∀ tries residual,
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
      ∀ incoming bucket,
        (incoming, bucket) ∈ SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries →
        (match incoming with | .node _ _ _ _ => True | _ => False) ∨
          bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true ∨ bucket = [] := by
  intro tries residual projected
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := head.admission.packet.valid
  obtain ⟨handle, parentEntry, edges, depth, free, stored, decoded, selected⟩ := head.admission.source
  obtain ⟨parent, parentLookup, parentAvailable, parentClosed⟩ := realized uv handle scs stored
  have parentSame : parent = .node parentEntry edges depth free :=
    Option.some.inj (parentLookup.symm.trans decoded)
  subst parent
  have bounded : ∀ sc ∈ scs, sc.var < before.core.counter :=
    head.admission.ready.safe.1.values _ (List.mem_of_getElem? stored)
  have pending := EnumerationReferences.pending_inputs before.core head.admission.packet.pending
    uv (some handle) scs stored
  obtain ⟨_action, own, _prepared, ownRun, _raw, _ownCore, _ownCounter, _ownForest,
    _ownSafe, _ownPaths, _ownRealized, _ownCounts, _ownFlags, _combinedPending, genuine, _ownProtects⟩ :=
    SourcePruningEnumerationEdgeInputs.complete caller.checked.native.machine.heap parentEntry edges depth free
      edge scs roots head.admission.packet.context.ready.semantic.ready parentAvailable parentClosed selected
      before head.admission.packet.safe realized paths counts flags bounded pending head.allowed tries residual projected
  let inputs := SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries
  let staged := inputs.map (fun input => (input.1, input.2,
    SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint) input.2 input.1))
  have stagedInputs : staged.map (fun input => (input.1, input.2.1)) = inputs := by
    simp only [staged, List.map_map]
    exact List.map_id _
  obtain ⟨fragments, childCache, _fragmentShape, trace, _finalized⟩ :=
    captured_complete_trace checkEmpty bound bound bound bound bound uv scs edge caller reached
      before own headCache memos.query saved edge.entry.key.symbol staged residual fragment ownRun
      (by simpa only [Nat.add_zero] using head.running 0)
  rw [stagedInputs] at trace
  intro incoming bucket member
  have closed := (genuine incoming bucket member).2.1
  obtain ⟨consumed, suffix, location⟩ := List.mem_iff_append.mp member
  by_cases terminal : bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
  · exact .inr (.inl terminal)
  · have nonterminal : bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = false := by
      simpa only [Bool.not_eq_true] using terminal
    by_cases boundary : MergedOrdinaryHeight.recursiveBoundary incoming = true
    · obtain ⟨_held, _handle, _decoded, _headIsolated, _callbackIsolated, _outputIsolated,
        _outputDecoded, notDischarged⟩ := completed_head_opaque_output_not_discharged
        seed inherited formulas solver inventory caller memos metadata before checkEmpty uv scs edge bound fragment
        reached saved headCache returnedInventory returnedMemos head tries residual projected consumed suffix
        incoming bucket location boundary nonterminal holeKey fits admits graph templates edgesOf stop order
        workFuel recursiveFuel recorded callbackCore tailSeed tailCeiling output callback tail
      exact False.elim (notDischarged discharged)
    · have ordinary : incoming = .empty ∨
          ∃ entry edges depth free, incoming = .node entry edges depth free :=
        MergedOrdinaryHeight.ordinary_operand incoming closed (by
          simpa only [Bool.not_eq_true] using boundary)
      rcases ordinary with empty | ⟨entry, edges, depth, free, same⟩
      · have currentTrace : SourcePruningEnumerationChildTraversal.Trace checkEmpty bound bound bound bound bound
            (consumed ++ (incoming, bucket) :: suffix) caller own memos.query
            fragments reached childCache saved := by
          simpa only [inputs, location] using trace
        obtain ⟨_prefixFragments, _childFragment, _suffixFragments, eventCaller, _preparedCaller,
          eventBefore, _preparedCache, eventQueries, _preparedQueries, _outer, _waiting,
          _fragmentSplit, _prefixTrace, actualChild, _suffixTrace⟩ :=
          split_event checkEmpty bound bound bound bound bound consumed suffix incoming bucket
            caller reached own childCache memos.query saved fragments currentTrace
        rw [empty, SourcePruningEnumerationChildDispatch.empty] at actualChild
        cases actualChild
      · subst incoming
        exact .inl trivial

end MicroCFTA.SourcePruningEnumerationOpaqueEvent
