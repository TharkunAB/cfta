theorem selected_finite_complete_resources_with_history
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (recursiveFuel : Nat)
    (recursive : CompleteWithHistory (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (metadata : Metadata Typing)
    (uv : Nat) (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (initialMass : mass before.core ≤ ceiling)
    (reserved : SourcePruningEnumerationFiniteReservation.Reserved bits (recursiveFuel + 1) seed ceiling)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv)) :
    ∃ bound outcome,
      (∀ extra, resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) (recursiveFuel + 1)
        metadata caller memos.query before (some (.expand uv)) = outcome) ∧
      OutcomeResources formulas solver caller
        (Forecast (recursiveFuel + 1) seed ceiling) outcome ∧
      ∀ extra output, output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome →
        ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver
          (bound + extra) (recursiveFuel + 1) inventory caller memos metadata before seed ceiling
          (some (.expand uv)) output := by
  rw [SourcePruningEnumerationFiniteReservation.final_succ]
  let start := SourcePruningEnumerationExpansionAdmission.narrowSeed seed
  let inherited := ceiling
  have stageGrowth := SourcePruningEnumerationFiniteReservation.stage_ge
    recursiveFuel start inherited inherited (SourcePruningEnumerationFiniteReservation.rows seed)
  have selection : EnumerationPureSelection.next (order metadata) before = .expand uv := by
    cases stop with
    | none => exact Option.some.inj chosen
    | some rule =>
        simp only [SourcePruningEnumerationRestart.decision] at chosen
        split at chosen
        · cases chosen
        · exact Option.some.inj chosen
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := packet.valid
  obtain ⟨prefixFuel, phases⟩ := SourcePruningEnumerationSelectedStep.prefix_checkpoint_complete
    holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
    caller memos before (order metadata) uv roots packet.context packet.safe packet.pending selection
    realized paths counts flags
  rcases phases with parked | rejected | accepted
  · obtain ⟨checked, phase⟩ := parked
    obtain ⟨bound, outcome, running, resources, histories⟩ := parked_finite_complete_resources_with_history
      holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveFuel recursive inventory
      caller memos before metadata prefixFuel uv checked seed ceiling packet bounded known
      selectionMembers selectionLength initialMass reserved phase
    exact ⟨bound, outcome, running, by
      simpa only [SourcePruningEnumerationFiniteReservation.final_succ] using resources, histories⟩
  · obtain ⟨checked, heap, phase⟩ := rejected
    let reached := SourceCurrentAllocatedPartialState.advance caller
      (SourceCurrentAllocatedQueryMemo.advancePhysical caller.checked ⟨heap, caller.checked.operations⟩)
      caller.fourth caller.merge
    have valid := (phase 0).2
    rw [(phase 0).1] at valid
    have resources := SourcePruningEnumerationSelectedStep.prefix_resources
      holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
      (prefixFuel + 0) uv caller before memos seed.2 (fun guard => guard ∈ seed.1)
      packet.context realized bounded known _ valid
    obtain ⟨final, post, query⟩ := SourcePruningEnumerationPrefixPacket.prefix_context
      holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
      (prefixFuel + 0) uv caller before memos _ valid
    have certificate : OutcomeResources (Typing := Typing) formulas solver caller start (.complete [] reached memos.query) :=
      ⟨reached, inventory, final, post, resources.1, resources.2, rfl, query.symm,
        fun _ member => False.elim (List.not_mem_nil member)⟩
    refine ⟨prefixFuel, .complete [] reached memos.query, ?_, certificate.mono
      stageGrowth.1 stageGrowth.2, ?_⟩
    · intro extra
      rw [resume, (phase extra).1]
    · intro extra output member
      cases member
  · obtain ⟨checked, phaseValue, heap, after, _nonempty, phase⟩ := accepted
    let reached := SourceCurrentAllocatedPartialState.advance caller
      (SourceCurrentAllocatedQueryMemo.advancePhysical caller.checked ⟨heap, caller.checked.operations⟩)
      caller.fourth caller.merge
    obtain ⟨action, prefixAt, valid⟩ := phase 0
    rw [prefixAt] at valid
    have admission := SourcePruningEnumerationPrefixAdmission.narrowed_admission
      holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
      (prefixFuel + 0) uv caller memos before packet chosen seed.2 (fun guard => guard ∈ seed.1)
      bounded known _ valid
    obtain ⟨handle, scs, value, middleMemos, middlePost, middleQuery, middlePacket, ready, stored,
      decoded, _available, _closed, incoming, _pending, _ids, lengths, _counter, _waiting,
      middleFits, middleKnown⟩ := admission
    by_cases ordinary : ∃ entry rows depth free,
        value = .node entry rows depth free ∧ scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false
    · obtain ⟨entry, rows, depth, free, same, nonterminal⟩ := ordinary
      subst value
      have currentMass : mass after.core ≤ inherited :=
        Nat.le_trans (SourcePruningEnumerationPrefixMass.retained_le holeKey fits admits graph templates checkEmpty edgesOf
          stop order metadata formulas solver inventory (prefixFuel + 0) uv caller memos before packet _ valid prefixAt)
          initialMass
      have inheritedBound : scs.length ≤ inherited := Nat.le_trans lengths initialMass
      obtain ⟨scanFuel, entered, _processed, outputs, _afterCaller, _next, _final, result,
        entryRun, _stable, _counter, _values, sameFlags, sameWaiting, enteredPacket,
        outerRun, _scanRun, _post, _captured, _afterFits, _afterKnown, _processedLength,
        _receipts, _outputPackets, scanShape, _finished, _countBound, _finalFits, _finalKnown, certificate, histories⟩ :=
        SourcePruningEnumerationNativeOrdinaryContinuations.ordinary_finite_complete_history_forecast
          holeKey fits admits graph templates checkEmpty edgesOf stop order metadata recursiveFuel start formulas solver recursive inventory
          reached middleMemos after uv handle scs entry rows depth free middlePacket ready stored decoded
          (selectionMembers entry rows depth free) incoming nonterminal middleFits middleKnown
          selectionMembers selectionLength inherited inherited currentMass inheritedBound reserved.scan
      refine ⟨prefixFuel + scanFuel, finish uv result, ?_, certificate.post middlePost, ?_⟩
      · apply resume_depth_stable holeKey fits admits graph templates checkEmpty edgesOf stop order
          prefixFuel scanFuel recursiveFuel uv metadata metadata caller reached memos.query memos.query before after
          [.ok ((uv, handle, scs, .node entry rows depth free), entered.core)] result
        · intro extra
          obtain ⟨currentAction, currentPrefix, _valid⟩ := phase extra
          exact ⟨checked, .done (phaseValue, some currentAction) heap, currentPrefix⟩
        · intro extra
          simpa only [middleQuery] using outerRun extra
      · intro extra output member
        have listed : output ∈ outputs := by
          rw [finish_hook_outputs] at member
          rcases scanShape with completed | ⟨current, stopped, _endpoint, _certificate⟩
          · rw [completed] at member
            exact member
          · rw [stopped] at member
            exact member
        have rich := histories (prefixFuel + extra) output listed
        have entryAt := entryRun (prefixFuel + extra)
        have common : scanFuel + (prefixFuel + extra) = prefixFuel + scanFuel + extra := by omega
        rw [common] at rich entryAt
        obtain ⟨edge, _selected, headSeed, headInventory, headCaller, headMemos, headBound,
          fragment, callbackCaller, headCache, returnedInventory, returnedMemos, recorded, callbackCore,
          headPost, invocation, headRun, headReceipt, originalAdmission, callback,
          _returnedAdmission, tailHistory⟩ := rich
        have framed : EnumerationExpandableIndex.frame entered.core after = entered := by
          cases entered with
          | mk core flags waiting =>
              change ({core := core, expandable := after.expandable, waiting := after.waiting} : Cached) =
                {core := core, expandable := flags, waiting := waiting}
              simp only at sameFlags sameWaiting
              rw [← sameFlags, ← sameWaiting]
        have actualOrdinary : SourcePruningEnumerationHookInvocation.OrdinaryInvocation
            (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
              (prefixFuel + scanFuel + extra) recursiveFuel) graph templates stop order
              (prefixFuel + scanFuel + extra) metadata uv)
            checkEmpty (prefixFuel + scanFuel + extra) (prefixFuel + scanFuel + extra)
              (prefixFuel + scanFuel + extra) (prefixFuel + scanFuel + extra) (prefixFuel + scanFuel + extra)
              uv edgesOf reached after middleMemos.query fragment callbackCaller returnedMemos.query headCache := by
          refine ⟨uv, handle, scs, entry, rows, depth, free, entered.core, entryAt, nonterminal, ?_⟩
          simpa only [framed] using invocation
        have actualReceipt : OrdinaryHistoryReceipt formulas solver metadata checkEmpty
            (prefixFuel + scanFuel + extra) uv inventory reached middleMemos after fragment callbackCaller
              headCache returnedInventory returnedMemos := by
          exact ⟨entered, handle, scs, .node entry rows depth free, edge, headSeed, inherited,
            headInventory, headCaller, headMemos, headBound, middlePacket, entryAt, enteredPacket,
            headPost, headRun, headReceipt⟩
        obtain ⟨currentAction, currentPrefix, currentValid⟩ := phase (scanFuel + extra)
        have prefixSame : prefixFuel + (scanFuel + extra) = prefixFuel + scanFuel + extra := by omega
        rw [prefixSame] at currentPrefix currentValid
        apply ResourceHistory.ordinary ⟨packet, bounded, known, initialMass, reserved⟩ currentValid
          (by simpa only [middleQuery] using currentPrefix) middlePost actualOrdinary actualReceipt
          originalAdmission callback tailHistory
    · have fallback : match value with
        | .node .. => scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
        | _ => True := by
        cases value with
        | node entry rows depth free =>
            change scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
            cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) with
            | false => exact False.elim (ordinary ⟨entry, rows, depth, free, rfl, terminal⟩)
            | true => rfl
        | empty | reference _ | union _ _ _ _ | mu _ _ _ _ => trivial
      obtain ⟨entryFuel, entered, _entryRun, _stable, _counter, _values, _flags, _waiting,
        _enteredPacket, fallbackRun, _post, _fits, _known⟩ :=
        SourcePruningEnumerationNativeOrdinaryContinuations.fallback_complete_resources
          (Output := Output (bits + 2) Typing) (Reason := Failure (bits + 2) Typing)
          formulas solver inventory reached middleMemos after metadata uv handle scs value checkEmpty edgesOf
          middlePacket ready stored decoded (by cases value <;> exact fallback)
          (headProfile seed.2) (fun guard => guard ∈ seed.1)
          middleFits middleKnown
      let raw := [Except.ok (ε := EnumerationState.Error) ((uv, handle, scs, value), entered.core)]
      let outcome := SourcePruningEnumerationNativeContinuations.HookResult.stopped
        (Output := Output (bits + 2) Typing) (Reason := Failure (bits + 2) Typing)
        [] (.ordinary uv raw) (some (reached, memos.query))
      have certificate : OutcomeResources formulas solver reached start outcome := by
        refine ⟨reached, inventory, middleMemos, Post.refl middlePacket.context, middleFits, middleKnown,
          Or.inr ?_, fun _ member => False.elim (List.not_mem_nil member)⟩
        exact congrArg some (congrArg (Prod.mk reached) middleQuery.symm)
      refine ⟨prefixFuel + entryFuel, outcome, ?_, (certificate.mono
        stageGrowth.1 stageGrowth.2).post middlePost, ?_⟩
      · intro extra
        obtain ⟨currentAction, currentPrefix, _valid⟩ := phase (entryFuel + extra)
        have samePrefix : prefixFuel + (entryFuel + extra) = prefixFuel + entryFuel + extra := by omega
        rw [samePrefix] at currentPrefix
        have actual := fallbackRun (prefixFuel + extra)
          (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
            (prefixFuel + entryFuel + extra) recursiveFuel) graph templates stop order
            (prefixFuel + entryFuel + extra) metadata uv)
        have sameEntry : entryFuel + (prefixFuel + extra) = prefixFuel + entryFuel + extra := by omega
        rw [sameEntry, middleQuery] at actual
        rw [resume, currentPrefix]
        dsimp only
        rw [actual]
      · intro extra output member
        cases member
