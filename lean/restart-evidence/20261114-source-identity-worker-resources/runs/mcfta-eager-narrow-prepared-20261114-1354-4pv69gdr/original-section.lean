section ActualPreparedResources
attribute [local irreducible] nodeReserved nodePlan
attribute [local irreducible] SourceCurrentConstrainedCapEditForecast.headProfile
variable {Key : Type}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
open SourcePruningEnumerationFiniteReservation (iterate)

private theorem eager_prepared_resources
    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat) (recursive : EagerResumeComplete (bits := bits) holeKey keyMatches admits graph templates
      checkEmpty edgesOf stop order formulas solver recursiveDepth)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (ceiling uv handle : Nat) (scs : List Suspended)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (fits : Fits (SourcePruningEnumerationSharedRecursiveReservation.narrowSeed seed).2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (bucketBound : scs.length ≤ ceiling)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (reserved : eagerReserved bits (recursiveDepth + 1) seed ceiling) :
    ∃ (fuel : Nat) (observed : SourcePruningEnumerationSharedPreparedContinuations.Preparation) (outcome : Fold),
      (∀ extra, SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
        (SourcePruningEnumerationSharedPreparedRecursive.continueWith
          (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
            (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
              (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
            holeKey keyMatches admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
          graph templates stop order (fuel + extra) metadata uv)
        checkEmpty (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
          (fuel + extra) (fuel + extra) (fuel + extra) uv edgesOf caller before memos.query = (observed, some outcome)) ∧
      OutcomeResources formulas solver caller (eagerFinal (recursiveDepth + 1) seed ceiling) (finish uv outcome) := by
  let start := SourcePruningEnumerationSharedPreparedReservation.preparedSeed seed
  let limit := SourceCurrentConstrainedCapTargetForecast.scalar start.2
  let own := SourcePruningEnumerationGuardWidth.width start.1
  let continuation : Nat → Seed → Seed := fun retained current => eagerFinal recursiveDepth current retained
  let admitted : Nat → Seed → Prop := fun retained current => eagerReserved bits recursiveDepth current retained
  let hook := fun (work : Nat) => SourcePruningEnumerationSharedPreparedRecursive.continueWith
    (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
      (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty work work work work work edgesOf)
      holeKey keyMatches admits graph templates checkEmpty edgesOf stop order work recursiveDepth)
    graph templates stop order work metadata uv
  change ∃ fuel observed outcome,
    (∀ extra, SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild
      (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
        (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
      (hook (fuel + extra)) checkEmpty (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
        (fuel + extra) (fuel + extra) (fuel + extra) uv edgesOf caller before memos.query = (observed, some outcome)) ∧
    OutcomeResources formulas solver caller (eagerFinal (recursiveDepth + 1) seed ceiling) (finish uv outcome)
  have growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧
      current.1 ⊆ (continuation retained current).1 := fun retained current => eagerFinal_ge recursiveDepth current retained
  have planned : nodeReserved bits limit own limit ceiling ceiling continuation admitted start := by
    simpa only [eagerReserved] using reserved
  obtain ⟨preparationFuel, decoded, value, heap, entered, retained,
    preparedFits, _valueMass, preparedKnown, frame, enteredIncoming, sameMass⟩ :=
    SourcePruningEnumerationSelectedPreparation.complete_resources_current
      formulas solver inventory caller memos metadata before uv handle scs packet ready stored
      (SourcePruningEnumerationSharedRecursiveReservation.narrowSeed seed).2 fits incoming
      (fun guard => guard ∈ seed.1) known
  obtain ⟨preparationRun, _decodedLookup, preparationPost, enteredPacket, _stable, enteredReady,
    enteredStored, _counter, _values, _flags, _waiting, available, closed, _meaning, _satisfaction⟩ := retained
  let preparedCaller := SourcePruningEnumerationSelectedValueCaller.advance caller heap
  have currentFits : Fits start.2 preparedCaller.checked := preparedFits
  have currentKnown : Heap (fun guard => guard ∈ start.1) preparedCaller.checked.native.machine.heap := preparedKnown
  have currentMass : SourcePruningEnumerationPrefixAdmission.suspendedBound entered.core ≤ ceiling := by
    rw [sameMass]
    exact mass
  by_cases ordinary : ∃ entry rows depth free,
      value = .node entry rows depth free ∧ scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false
  · obtain ⟨entry, rows, depth, free, same, nonterminal⟩ := ordinary
    subst value
    let captured := preparedCaller.checked.native.machine.heap
    obtain ⟨heights, shapes⟩ := SourcePruningEnumerationSharedEagerCapturedBounds.captured_payload_bounds
      start captured enteredPacket.context.ready.semantic.ready.semantic.1.normal.facts.linked
      (SourceCurrentConstrainedCapRequiredResources.of_checked currentFits) currentKnown
    have nodeHeight := heights (.node entry rows depth free) available
    have positive : 0 < limit := by
      change MergedOrdinaryHeight.edgesHeight rows + 1 ≤ limit at nodeHeight
      omega
    let height := limit - 1
    have heightSame : height + 1 = limit := by dsimp only [height]; omega
    have ranked : MergedOrdinaryHeight.height (.node entry rows depth free) ≤ height + 1 := by
      rw [heightSame]
      exact nodeHeight
    have computed : nodeReserved bits limit own (height + 1) ceiling ceiling continuation admitted start := by
      rw [heightSame]
      exact planned
    unfold nodeReserved at computed
    let first := fallbackPlan ceiling ceiling continuation start
    let row := fun current => tuplePlan (nodePlan limit own height) limit (ceiling + own) ceiling continuation current
    have firstGrowth := fallbackPlan_ge ceiling ceiling continuation growth start
    have firstKnown : Heap (fun guard => guard ∈ first.1) preparedCaller.checked.native.machine.heap := by
      intro key edge found
      exact firstGrowth.2 (currentKnown key edge found)
    have rowReserved : ∀ index, index < limit →
        tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
          limit (ceiling + own) ceiling continuation admitted (iterate row first index) := computed.2
    have length : (edgesOf (.node entry rows depth free)).length ≤ limit :=
      Nat.le_trans (selectionLength entry rows depth free) (shapes entry rows depth free available).1
    have bounded : ∀ sc ∈ scs, sc.var < entered.core.counter :=
      enteredReady.safe.1.values _ (List.mem_of_getElem? enteredStored)
    have pending := EnumerationReferences.pending_inputs entered.core enteredPacket.pending uv (some handle) scs enteredStored
    obtain ⟨branchFuel, outcome, branchRun, certificate⟩ := eager_captured_rows_resources
      holeKey keyMatches admits graph templates checkEmpty edgesOf stop order formulas solver recursiveDepth recursive
      captured limit own height limit inventory preparedCaller memos metadata entered first ceiling ceiling scs uv handle
      enteredPacket enteredReady enteredStored enteredIncoming (currentFits.mono firstGrowth.1) firstKnown
      (SourceEqualityRequiredCache.pure_keeps captured enteredPacket.context.ready.semantic.ready)
      currentMass bucketBound entry rows depth free available closed ranked bounded pending
      (edgesOf (.node entry rows depth free)) length (selectionMembers entry rows depth free) shapes
      selectionMembers selectionLength rowReserved
    have finalSame : eagerFinal (recursiveDepth + 1) seed ceiling = iterate row first limit := by
      change nodePlan limit own limit ceiling ceiling continuation start = _
      calc
        nodePlan limit own limit ceiling ceiling continuation start =
            nodePlan limit own (height + 1) ceiling ceiling continuation start :=
          congrArg (fun h => nodePlan limit own h ceiling ceiling continuation start) heightSame.symm
        _ = iterate row first limit := by
          unfold nodePlan
          rfl
    have resources : OutcomeResources formulas solver caller (eagerFinal (recursiveDepth + 1) seed ceiling)
        (finish uv outcome) := by
      rw [finalSame]
      exact certificate.post preparationPost
    refine ⟨preparationFuel + branchFuel,
      ([.ok ((uv, handle, scs, decoded), entered.core)], some (.done (.node entry rows depth free) heap)),
      outcome, ?_, resources⟩
    intro extra
    have atPreparation := preparationRun (branchFuel + extra)
    have prepSame : preparationFuel + (branchFuel + extra) = preparationFuel + branchFuel + extra := by omega
    rw [prepSame] at atPreparation
    have atBranch := branchRun (preparationFuel + extra)
    have branchSame : branchFuel + (preparationFuel + extra) = preparationFuel + branchFuel + extra := by omega
    rw [branchSame] at atBranch
    unfold SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild
    rw [atPreparation]
    simp only [nonterminal, Bool.false_eq_true, ↓reduceIte]
    rw [frame, atBranch]
  · have dispatch : (match (generalizing := false) value with
        | .node .. => !(scs.any (fun sc => EqualityTrie.isTerminal sc.trie)) | _ => false) = false := by
      cases value with
      | node entry rows depth free =>
          cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) with
          | false => exact (ordinary ⟨entry, rows, depth, free, rfl, terminal⟩).elim
          | true => rfl
      | empty | reference _ | mu _ _ _ _ | union _ _ _ _ => rfl
    obtain ⟨branchFuel, receipt, outcome, rawRun, receiptRun, certificate⟩ := eager_opaque_resources
      holeKey keyMatches admits graph templates checkEmpty edgesOf stop order formulas solver recursiveDepth recursive
      inventory preparedCaller memos metadata entered start ceiling ceiling uv handle scs value enteredPacket enteredReady
      enteredStored enteredIncoming available closed dispatch currentFits currentKnown currentMass bucketBound
      selectionMembers selectionLength (nodeReserved_fallback bits limit own limit ceiling ceiling continuation admitted start planned)
    have enlarged := fallbackPlan_le_nodePlan limit own limit ceiling ceiling continuation growth start
    have resources : OutcomeResources formulas solver caller (eagerFinal (recursiveDepth + 1) seed ceiling)
        (finish uv outcome) := (certificate.mono enlarged.1 enlarged.2).post preparationPost
    refine ⟨preparationFuel + branchFuel,
      ([.ok ((uv, handle, scs, decoded), entered.core)], some (.done value heap)), outcome, ?_, resources⟩
    intro extra
    have atPreparation := preparationRun (branchFuel + extra)
    have prepSame : preparationFuel + (branchFuel + extra) = preparationFuel + branchFuel + extra := by omega
    rw [prepSame] at atPreparation
    have rawAt := rawRun (preparationFuel + extra)
    have continued := receiptRun (preparationFuel + extra)
    have branchSame : branchFuel + (preparationFuel + extra) = preparationFuel + branchFuel + extra := by omega
    rw [branchSame] at rawAt continued
    have composed : SourcePruningEnumerationSharedReceiptContinuation.run
        (hook (preparationFuel + branchFuel + extra)) preparedCaller memos.query
        (SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty
          (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
          (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
          (preparationFuel + branchFuel + extra) uv scs value preparedCaller entered memos.query) = outcome := by
      rw [rawAt]
      exact continued
    have actual : SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
          (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
          (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
          (preparationFuel + branchFuel + extra) edgesOf)
        (hook (preparationFuel + branchFuel + extra)) checkEmpty
        (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
        (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
        (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
        (preparationFuel + branchFuel + extra) uv edgesOf caller before memos.query =
      (([.ok ((uv, handle, scs, decoded), entered.core)], some (.done value heap)),
        some (SourcePruningEnumerationSharedReceiptContinuation.run
          (hook (preparationFuel + branchFuel + extra)) preparedCaller memos.query
          (SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty
            (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
            (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
            (preparationFuel + branchFuel + extra) uv scs value preparedCaller entered memos.query))) := by
      unfold SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild
      rw [atPreparation]
      cases value with
      | node entry rows depth free =>
          have terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true := by
            cases here : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) with
            | false => exact (ordinary ⟨entry, rows, depth, free, rfl, here⟩).elim
            | true => rfl
          simp only [terminal, ↓reduceIte, frame, preparedCaller]
      | empty | reference _ | mu _ _ _ _ | union _ _ _ _ =>
          cases here : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) <;>
            simp only [here, Bool.false_eq_true, ↓reduceIte, frame, preparedCaller]
    rw [composed] at actual
    exact actual
end ActualPreparedResources
