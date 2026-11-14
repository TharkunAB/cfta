section ActualOpaqueResources
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Opaque completion retains the same narrowing operation in its recursive callback. -/
private theorem eager_opaque_resources_with_narrow
    (narrow : Metadata Typing → Nat → Nat → Node →
      InternedConstructorTemplates.State Symbol Constraint →
      MergedSourceComparison.Result Symbol Constraint Node)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat) (recursive : EagerResumeWithNarrowComplete (bits := bits) narrow graph templates
      checkEmpty edgesOf stop order formulas solver recursiveDepth)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (bound ceiling uv handle : Nat) (scs : List Suspended) (value : Node)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (available : Available caller.checked.native.machine.heap value) (closed : value.free = [])
    (dispatch : (match (generalizing := false) value with
      | .node .. => !(scs.any (fun sc => EqualityTrie.isTerminal sc.trie)) | _ => false) = false)
    (fits : Fits seed.2 caller.checked) (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling) (bucketBound : scs.length ≤ bound)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (reserved : fallbackReserved bits bound ceiling (fun retained current => eagerReserved bits recursiveDepth current retained) seed) :
    ∃ (fuel : Nat) (receipt : SelectedEdge.Result (bits + 2)) (outcome : Fold),
      (∀ extra, SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty
        (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
        uv scs value caller before memos.query = some receipt) ∧
      (∀ extra, SourcePruningEnumerationSharedReceiptContinuation.run
        (SourcePruningEnumerationSharedPreparedRecursive.continueWith
          (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow (width := bits + 2)
            (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
              (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
            narrow graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
          graph templates stop order (fuel + extra) metadata uv) caller memos.query (some receipt) = outcome) ∧
      OutcomeResources formulas solver caller
        (fallbackPlan bound ceiling (fun retained current => eagerFinal recursiveDepth current retained) seed) (finish uv outcome)
    := by
  have cost : scs.length + 1 ≤ bound + 1 := by omega
  obtain ⟨headFuel, receipt, reached, saved, final, next, headRun, headPost, headQuery,
    _advanced, admitted, _pending, _history, headFits, headKnown, shape, _finalization⟩ :=
    SourcePruningEnumerationSharedSelectedOpaqueDispatch.opaque_complete_resources seed formulas solver inventory
      caller memos metadata before checkEmpty uv handle scs value packet ready stored incoming available closed
      dispatch fits (reserved.1.prefix cost) known
  have padding : Le (advance seed (scs.length + 1)).2 (advance seed (bound + 1)).2 ∧
      (advance seed (scs.length + 1)).1 ⊆ (advance seed (bound + 1)).1 :=
    ⟨SourcePruningEnumerationSharedIncomingReservation.advance_count_profile_mono seed cost,
      SourcePruningEnumerationSharedIncomingReservation.advance_count_alphabet_mono seed cost⟩
  have paddedFits := headFits.mono padding.1
  have paddedKnown : Heap (fun guard => guard ∈ (advance seed (bound + 1)).1)
      reached.checked.native.machine.heap := fun key edge resident => padding.2 (headKnown key edge resident)
  subst saved
  rcases shape with completed | stopped | rejected
  · obtain ⟨fragment, after, rfl, afterPacket, _counter, afterMass⟩ := completed
    have actualMass : SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤ ceiling + bound := by omega
    obtain ⟨callbackFuel, continued, callbackRun, resources⟩ :=
      callback_eager_induction_resources_with_narrow narrow formulas solver next graph templates metadata uv
        fragment reached final after checkEmpty edgesOf stop order recursiveDepth recursive
        (advance seed (bound + 1)) (ceiling + bound) afterPacket admitted.2.2.1 paddedFits paddedKnown
        selectionMembers selectionLength actualMass reserved.2
    let folded : Fold := match continued with
      | .complete outputs actual queries =>
          .complete [.complete fragment reached final.query after] outputs actual queries
      | .stopped outputs reason endpoint =>
          .stopped [] outputs (.continuation (.complete fragment reached final.query after) reason endpoint)
    have fullResources := resources.post headPost
    have finished : OutcomeResources formulas solver caller
        (fallbackPlan bound ceiling (fun retained current => eagerFinal recursiveDepth current retained) seed)
        (finish uv folded) := by
      cases continued <;>
        simpa only [folded, finish, SourcePruningEnumerationSharedPreparedRecursive.endpoint,
          OutcomeResources, fallbackPlan] using fullResources
    refine ⟨headFuel + callbackFuel, .complete fragment reached final.query after, folded, ?_, ?_, finished⟩
    · intro extra
      have actual := headRun (callbackFuel + extra)
      rw [← Nat.add_assoc] at actual
      exact actual
    · intro extra
      have actual := callbackRun (headFuel + extra)
      have common : callbackFuel + (headFuel + extra) = headFuel + callbackFuel + extra := by omega
      rw [common] at actual
      simp only [SourcePruningEnumerationSharedReceiptContinuation.run, actual]
      cases continued <;> rfl
  · obtain ⟨after, outer, waiting, rfl, _counter, _mass⟩ := stopped
    have resources : OutcomeResources (Typing := Typing) formulas solver caller (advance seed (bound + 1))
        (.complete [] reached final.query) := by
      refine ⟨reached, next, final, headPost, paddedFits, paddedKnown, rfl, rfl, ?_⟩
      intro output member
      exact (List.not_mem_nil member).elim
    have growth := eagerFinal_ge recursiveDepth (advance seed (bound + 1)) (ceiling + bound)
    refine ⟨headFuel, .stopped [] (.ok (some []), reached, final.query, outer, waiting) (some after),
      .complete [.stopped [] (.ok (some []), reached, final.query, outer, waiting) (some after)] [] reached final.query,
      headRun, ?_, ?_⟩
    · intro extra
      simp only [SourcePruningEnumerationSharedReceiptContinuation.run,
        SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance]
    · simpa only [finish, fallbackPlan] using resources.mono growth.1 growth.2
  · subst receipt
    have resources : OutcomeResources (Typing := Typing) formulas solver caller (advance seed (bound + 1))
        (.complete [] reached final.query) := by
      refine ⟨reached, next, final, headPost, paddedFits, paddedKnown, rfl, rfl, ?_⟩
      intro output member
      exact (List.not_mem_nil member).elim
    have growth := eagerFinal_ge recursiveDepth (advance seed (bound + 1)) (ceiling + bound)
    have endpoints : (caller, memos.query) = (reached, final.query) := by
      exact Option.some.inj _advanced
    obtain ⟨callerSame, querySame⟩ := Prod.mk.inj endpoints
    refine ⟨headFuel, .rejected caller memos.query before,
      .complete [.rejected caller memos.query before] [] caller memos.query, headRun, ?_, ?_⟩
    · intro extra
      simp only [SourcePruningEnumerationSharedReceiptContinuation.run,
        SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance]
    · have fullResources := resources.mono growth.1 growth.2
      simpa only [finish, fallbackPlan, callerSame, querySame] using fullResources

variable {Key : Type}

private theorem eager_opaque_resources
    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat) (recursive : EagerResumeComplete (bits := bits) holeKey keyMatches admits graph templates
      checkEmpty edgesOf stop order formulas solver recursiveDepth)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (bound ceiling uv handle : Nat) (scs : List Suspended) (value : Node)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (available : Available caller.checked.native.machine.heap value) (closed : value.free = [])
    (dispatch : (match (generalizing := false) value with
      | .node .. => !(scs.any (fun sc => EqualityTrie.isTerminal sc.trie)) | _ => false) = false)
    (fits : Fits seed.2 caller.checked) (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling) (bucketBound : scs.length ≤ bound)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (reserved : fallbackReserved bits bound ceiling (fun retained current => eagerReserved bits recursiveDepth current retained) seed) :
    ∃ (fuel : Nat) (receipt : SelectedEdge.Result (bits + 2)) (outcome : Fold),
      (∀ extra, SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty
        (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
        uv scs value caller before memos.query = some receipt) ∧
      (∀ extra, SourcePruningEnumerationSharedReceiptContinuation.run
        (SourcePruningEnumerationSharedPreparedRecursive.continueWith
          (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
            (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
              (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
            holeKey keyMatches admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
          graph templates stop order (fuel + extra) metadata uv) caller memos.query (some receipt) = outcome) ∧
      OutcomeResources formulas solver caller
        (fallbackPlan bound ceiling (fun retained current => eagerFinal recursiveDepth current retained) seed) (finish uv outcome)
    := by
  exact eager_opaque_resources_with_narrow (bits := bits)
    (SourcePruningOuterNarrow.narrow holeKey keyMatches admits)
    graph templates checkEmpty edgesOf stop order formulas solver recursiveDepth recursive
    inventory caller memos metadata before seed bound ceiling uv handle scs value
    packet ready stored incoming available closed dispatch fits known mass bucketBound
    selectionMembers selectionLength reserved

end ActualOpaqueResources
