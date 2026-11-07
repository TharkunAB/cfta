import MicroCFTA.SourceRecursiveIntersectionLeafIdentity

/-!
# Physical marker result of the actual universe intersection

The ordered leaf-row walk keeps all dead-edge and cache effects.
Each live output reuses the original marker edge. The normalized node
therefore returns the original marker or Empty. Both operand orders
follow the actual source ordering. The unused optional Mu keeps that result.
-/
namespace MicroCFTA.SourceSynthesisUniverseMarkerIdentity
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedFreshProbeKeys InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionControl

variable {Symbol Guard : Type}

private theorem pair_right_cancel (first second third : Nat)
    (same : pair first second = pair first third) : second = third := by
  have lower := congrArg Prod.fst same
  have upper := congrArg Prod.snd same
  simp only [pair] at lower upper
  omega

private theorem leaf_pair_identity [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (top : Guard)
    (conjoinTop : conjoin top top = top) (fuel : Nat)
    (domain : Interned DomainKey) (first second : Interned NodeKey)
    (markerRow : EdgeValue Symbol Guard) (secondRows : List (EdgeValue Symbol Guard)) (secondDepth : Nat)
    (name : Reference) (state : Machine Symbol Guard) (facts : Facts state.heap)
    (markerAvailable : Available state.heap (.node first [markerRow] 0 []))
    (leaf : markerRow.children = []) (markerTop : markerRow.entry.key.constraint = top)
    (secondTop : ∀ row ∈ secondRows, row.entry.key.constraint = top)
    (different : first.identity ≠ second.identity)
    (fresh : pair first.identity second.identity ∉ domain.key.seen) :
    ∃ value final,
      execute emptyGuard conjoin (fuel + 2) domain
        (.node first [markerRow] 0 []) (.node second secondRows secondDepth [name]) state =
        .done value final ∧ Facts final.heap ∧ Available final.heap value ∧ (value = .empty ∨ value = .node first [markerRow] 0 []) := by
  let left : Value Symbol Guard := .node first [markerRow] 0 []
  let right : Value Symbol Guard := .node second secondRows secondDepth [name]
  have firstTop : ∀ row ∈ [markerRow], row.entry.key.constraint = top := by
    intro row present
    simpa only [List.mem_singleton.mp present] using markerTop
  have noEmpty : hasEmpty left right = false := rfl
  have noEmptyReverse : hasEmpty right left = false := rfl
  have noReset : reset domain.key left right = false := by
    change (([] : List Reference).isEmpty && [name].isEmpty && !domain.key.free.isEmpty) = false
    rfl
  have noResetReverse : reset domain.key right left = false := by
    change ([name].isEmpty && ([] : List Reference).isEmpty && !domain.key.free.isEmpty) = false
    rfl
  have noSelf : closedSelf left right = false := by
    change ((NodeRef.node first.identity == NodeRef.node second.identity) && true) = false
    simp [different]
  have noSelfReverse : closedSelf right left = false := by
    change (_ && false) = false
    exact Bool.and_false _
  have freshReverse : pair second.identity first.identity ∉ domain.key.seen := by
    simpa only [pair, Nat.min_comm, Nat.max_comm] using fresh
  by_cases swapped : greater left right = true
  · have reverseOrder : greater right left = false :=
      SourceRecursiveIntersectionSchedule.swap_once left right
        (.node first.identity) (.node second.identity) rfl rfl swapped
    have selected : decision domain.key left right = .swap :=
      swap_first domain.key left right noEmpty noReset noSelf swapped
    have selectedReverse : decision domain.key right left = .ordinary := by
      simp only [decision, noEmptyReverse, noResetReverse, noSelfReverse, reverseOrder,
        Bool.false_eq_true, ite_false, left, right, identity, freshReverse, payload]
    obtain ⟨value, final, done, finalFacts, available, _, classified⟩ :=
      SourceRecursiveIntersectionLeafIdentity.node_marker_complete emptyGuard conjoin top conjoinTop
        (execute emptyGuard conjoin fuel domain) first markerRow secondRows [markerRow] state facts
        markerAvailable leaf (Or.inr rfl) secondTop firstTop
    have reverseDone : execute emptyGuard conjoin (fuel + 1) domain right left state = .done value final := by
      change onNode emptyGuard conjoin (execute emptyGuard conjoin fuel) domain right left state = _
      simpa only [onNode, selectedReverse] using done
    refine ⟨value, final, ?_, finalFacts, available, classified⟩
    change onNode emptyGuard conjoin (execute emptyGuard conjoin (fuel + 1)) domain left right state = _
    simpa only [onNode, selected] using reverseDone
  · have ordered : greater left right = false := Bool.eq_false_iff.mpr swapped
    have selected : decision domain.key left right = .ordinary := by
      simp only [decision, noEmpty, noReset, noSelf, ordered,
        Bool.false_eq_true, ite_false, left, right, identity, fresh, payload]
    obtain ⟨value, final, done, finalFacts, available, _, classified⟩ :=
      SourceRecursiveIntersectionLeafIdentity.node_marker_complete emptyGuard conjoin top conjoinTop
        (execute emptyGuard conjoin (fuel + 1) domain) first markerRow [markerRow] secondRows state facts
        markerAvailable leaf (Or.inl rfl) firstTop secondTop
    refine ⟨value, final, ?_, finalFacts, available, classified⟩
    change onNode emptyGuard conjoin (execute emptyGuard conjoin (fuel + 1)) domain left right state = _
    simpa only [onNode, selected] using done

/-- The actual five-level marker request returns Empty or the original cached marker. -/
theorem marker_universe_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (top : Guard)
    (conjoinTop : conjoin top top = top)
    (markerEntry bodyEntry universeEntry : Interned NodeKey)
    (markerRow : EdgeValue Symbol Guard) (bodyRows : List (EdgeValue Symbol Guard))
    (depth ordinary : Value Symbol Guard) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state)
    (markerAvailable : Available state.heap (.node markerEntry [markerRow] 0 []))
    (universeAvailable : Available state.heap
      (.mu universeEntry (.node bodyEntry bodyRows 0 [.interned universeEntry.identity]) depth ordinary))
    (leaf : markerRow.children = []) (markerTop : markerRow.entry.key.constraint = top)
    (bodyTop : ∀ row ∈ bodyRows, row.entry.key.constraint = top) :
    ∃ value final,
      execute emptyGuard conjoin 5 IntersectionEmptyDomain.emptyDomain
        (.node markerEntry [markerRow] 0 [])
        (.mu universeEntry (.node bodyEntry bodyRows 0 [.interned universeEntry.identity]) depth ordinary) state =
        .done value final ∧ Facts final.heap ∧ Available final.heap value ∧ (value = .empty ∨ value = .node markerEntry [markerRow] 0 []) := by
  let marker : Value Symbol Guard := .node markerEntry [markerRow] 0 []
  let storedBody : Value Symbol Guard := .node bodyEntry bodyRows 0 [.interned universeEntry.identity]
  let universeValue : Value Symbol Guard := .mu universeEntry storedBody depth ordinary
  have bodyAvailable : Available state.heap storedBody :=
    universeAvailable.children storedBody (by simp [InternedProbeProvenance.children, storedBody])
  have different : markerEntry.identity ≠ bodyEntry.identity := by
    intro same
    have equal := resident_identity_unique state.heap valid.1.coherent marker storedBody
      markerAvailable.resident bodyAvailable.resident markerEntry bodyEntry rfl rfl same
    have impossible : ([] : List Reference) = [.interned universeEntry.identity] := congrArg Value.free equal
    cases impossible
  have bodyDifferent : bodyEntry.identity ≠ universeEntry.identity := by
    intro same
    have impossible := resident_identity_unique state.heap valid.1.coherent storedBody universeValue
      bodyAvailable.resident universeAvailable.resident bodyEntry universeEntry rfl rfl same
    change Value.node bodyEntry bodyRows 0 [.interned universeEntry.identity] =
      Value.mu universeEntry (.node bodyEntry bodyRows 0 [.interned universeEntry.identity]) depth ordinary at impossible
    cases impossible
  let entered := SourceRecursiveIntersectionEnvironment.enter state.domains
    IntersectionEmptyDomain.emptyDomain.key marker universeValue markerEntry.identity universeEntry.identity
  let afterEnter : Machine Symbol Guard := {state with domains := entered.2}
  have enteredKey : entered.1.key = SourceRecursiveIntersectionDomain.extend
      IntersectionEmptyDomain.emptyDomain.key
      ((SourceRecursiveIntersectionEnvironment.bindings marker universeValue).map Prod.fst)
      (pair markerEntry.identity universeEntry.identity) :=
    (IntersectionEmptyDomain.make_correct state.domains valid.2 _).2.1
  have fresh : pair markerEntry.identity bodyEntry.identity ∉ entered.1.key.seen := by
    rw [enteredKey]
    intro present
    rcases (SourceRecursiveIntersectionDomain.extend_seen _ _ _ _).mp present with same | old
    · exact bodyDifferent (pair_right_cancel markerEntry.identity bodyEntry.identity universeEntry.identity same)
    · cases old
  obtain ⟨value, final, bodyDone, finalFacts, available, classified⟩ :=
    leaf_pair_identity emptyGuard conjoin top conjoinTop 2 entered.1 markerEntry bodyEntry markerRow bodyRows
      0 (.interned universeEntry.identity) afterEnter valid.1 markerAvailable leaf markerTop bodyTop different fresh
  have selected : decision IntersectionEmptyDomain.emptyDomain.key marker universeValue = .rightMu := by
    simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag, identity, payload,
      IntersectionEmptyDomain.emptyDomain, IntersectionEmptyDomain.emptyKey,
      marker, universeValue, storedBody, Value.referenceOf, Value.free]
    decide
  have closed : value.free = [] := by
    rcases classified with rfl | rfl <;> rfl
  refine ⟨value, final, ?_, finalFacts, available, classified⟩
  change onNode emptyGuard conjoin (execute emptyGuard conjoin 4)
    IntersectionEmptyDomain.emptyDomain marker universeValue state = _
  unfold onNode
  rw [selected]
  change (execute emptyGuard conjoin 4 entered.1 marker storedBody afterEnter).bind
    (fun value after => construction
      (SourceRecursiveIntersectionMaybeMu.maybeMu
        (pair markerEntry.identity universeEntry.identity) value after.heap) after) = .done value final
  rw [bodyDone]
  simp only [Result.bind, SourceRecursiveIntersectionMaybeMu.unused _ value final.heap (by simp [closed]),
    construction]

end MicroCFTA.SourceSynthesisUniverseMarkerIdentity
