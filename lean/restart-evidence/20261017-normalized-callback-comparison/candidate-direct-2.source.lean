import MicroCFTA.SourceCurrentNativeMuPublicationCallbacks
import MicroCFTA.SourceCurrentNativeNormalizedComparisonFinite
import MicroCFTA.SourceCurrentNativeNormalizedComparisonInactive
import MicroCFTA.SourceCurrentNativeNormalizedErasure
import MicroCFTA.SourceCurrentNativeLocalRecordErasure

/-!
# Unused candidate cleanup from the actual smaller body comparison

The two raw calls use the publication's ordinary and reserved arguments.
Their actual filters return the stored probes and candidate body. The
comparison premise concerns only that smaller source body before publication.
-/
set_option maxHeartbeats 1600000
namespace MicroCFTA.SourceCurrentNativeNormalizedComparisonCandidate
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome finish work)
open InternedNestedFacts InternedNestedProvenance InternedFreshProbeKeys InternedConstructionProvenance
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryContext InternedFreshOrdinaryLiveInputs
open InternedDeepFreeDepth InternedStoredMuOrigins
open SourceCurrentNativeNormalizedComparison SourceCurrentNativeNormalizedComparisonFinite
open SourceCurrentNativeNormalizedComparisonInactive SourceCurrentNativeNormalizedErasure
open SourceCurrentNativeStrippedAlternatives SourceCurrentNativeCallbackErasure
open SourceCurrentNativeNormalizationInputs (support)
open SourceCurrentNativeMuPublication (Publication)
open InternedBinderProtocol (Reference)

private theorem filter_absent [DecidableEq (EdgeKey Symbol Guard)]
    (own : Reference) (value : Value Symbol Guard) (state : State Symbol Guard)
    (normal : Normal state) (available : Available state value) (absent : own ∉ value.free) :
    run (withoutSelfReference own value) state = (value, state) := by
  cases value with
  | empty | reference | node | mu => rfl
  | union entry members depth free =>
      rw [withoutSelfReference_absent own entry members depth free]
      · rfl
      · intro member
        exact absent ((InternedNormalizationFree.unionMembers_free state normal.facts.coherent
          (.union entry members depth free) available own).mpr
            ⟨.reference own, member, by simp only [Value.free, List.mem_singleton]⟩)

private theorem erase_absent (own : Reference) (value : Value Symbol Guard)
    (absent : own ∉ value.free) : eraseSelf own value = value := by
  have different : value.referenceOf ≠ .ref own := by
    intro same
    have bare := (referenceOf_self_iff own value).mp same
    simp [bare, Value.free] at absent
  simp only [eraseSelf, different, ↓reduceIte]

/-- The actual smaller source comparison proves the unused law for this publication candidate. -/
theorem candidate [DecidableEq (EdgeKey Symbol Guard)]
    (event : Publication (Symbol := Symbol) (Guard := Guard))
    (compared : Compared event.expression
      (.inr (.inl ()) ::
        (event.environment.map (fun value => (Sum.inl value : Sum (Value Symbol Guard) Unit))).map liftInput)
      [(.inl () : Sum Unit Unit)]
      (Sum.elim (fun _ : Unit => .uninterned (ordinaryLevel event.depth)) (fun _ : Unit => .depth))
      (Sum.elim (fun _ : Unit => .interned event.entry.identity) (fun _ : Unit => .depth)) event.afterBody)
    (unused : InternedFreshOrdinaryDepthHeap.usesLocal event.depth event.ordinary = false) :
    finish true (.mu event.entry event.body event.depth event.ordinary) =
      eraseSelf (.uninterned (ordinaryLevel event.depth)) event.ordinary := by
  let fixedInputs : List (Sum (Value Symbol Guard) Unit) := event.environment.map Sum.inl
  let bodyInputs := .inr (.inl ()) :: fixedInputs.map liftInput
  let atoms : List (Sum Unit Unit) := [.inl ()]
  let ordinaryName : Reference := .uninterned (ordinaryLevel event.depth)
  let reservedName : Reference := .interned event.entry.identity
  let ordinaryNames := Sum.elim (fun _ : Unit => ordinaryName) (fun _ : Unit => Reference.depth)
  let reservedNames := Sum.elim (fun _ : Unit => reservedName) (fun _ : Unit => Reference.depth)
  have fixedMap (names : Unit → Reference) : fixedInputs.map (input names) = event.environment := by
    simp [fixedInputs, input, List.map_map, Function.comp_def]
  have bodyMap (own : Reference) :
      bodyInputs.map (input (Sum.elim (fun _ : Unit => own) (fun _ : Unit => Reference.depth))) =
        .reference own :: event.environment := by
    rw [local_inputs]
    rw [fixedMap]
  obtain ⟨rawOrdinary, afterRawOrdinary, rawBody, afterRawBody,
    ordinaryActual, ordinaryFilter, bodyActual, bodyFilter, ordinaryGrowth, bodyGrowth,
    ordinaryEntry, bodyEntry⟩ := SourceCurrentNativeMuPublicationCallbacks.raw_callbacks event
  have cutContext := (SourceCurrentNativeMuPublicationCallbacks.contexts event).2.1
  have ordinaryArgument : Available event.afterDepth (.reference ordinaryName) := ordinary_available _ _
  have reservedArgument : Available event.allocated (.reference reservedName) :=
    (reserve_available event.key event.cut cutContext.base.normal.facts.coherent
      cutContext.base.normal.facts.cached).2
  have ordinaryContext : Context event.afterDepth (bodyInputs.map (input ordinaryNames)) := by
    simpa only [ordinaryNames, bodyMap] using ordinaryEntry.base.local ordinaryName ordinaryArgument
  have bodyContext : Context event.allocated (bodyInputs.map (input reservedNames)) := by
    simpa only [reservedNames, bodyMap] using bodyEntry.base.local reservedName reservedArgument
  have ordinaryRawActual : build event.expression (bodyInputs.map (input ordinaryNames)) event.afterDepth =
      .done rawOrdinary afterRawOrdinary := by
    simpa only [ordinaryNames, bodyMap] using ordinaryActual
  have bodyRawActual : build event.expression (bodyInputs.map (input reservedNames)) event.allocated =
      .done rawBody afterRawBody := by
    simpa only [reservedNames, bodyMap] using bodyActual
  have ordinaryRawContext : Context afterRawOrdinary (bodyInputs.map (input ordinaryNames)) := by
    simpa only [ordinaryRawActual, Outcome.state] using ordinaryContext.build event.expression
  have bodyRawContext : Context afterRawBody (bodyInputs.map (input reservedNames)) := by
    simpa only [bodyRawActual, Outcome.state] using bodyContext.build event.expression
  have ordinaryAvailable := (InternedFreshOrdinaryFacts.build_verified event.expression _ event.afterDepth ordinaryContext.normal.facts
    ordinaryContext.inputs).result rawOrdinary afterRawOrdinary ordinaryRawActual
  have bodyAvailable := (InternedFreshOrdinaryFacts.build_verified event.expression _ event.allocated bodyContext.normal.facts
    bodyContext.inputs).result rawBody afterRawBody bodyRawActual
  have ordinaryFilterHistory : Extends afterRawOrdinary.nodes.issued event.cut.nodes.issued := by
    simpa only [work, ordinaryFilter, Outcome.state] using
      (filter_verified ordinaryName rawOrdinary afterRawOrdinary ordinaryRawContext.normal.facts
        ordinaryAvailable).history
  have reserveHistory : Extends event.cut.nodes.issued event.allocated.nodes.issued :=
    intern_issued_extends event.cut.nodes event.key cutContext.base.normal.facts.coherent.valid.2
  have bodyCallbackHistory : Extends event.allocated.nodes.issued event.afterBody.nodes.issued := by
    simpa only [event.bodyDone, Outcome.state] using
      (callback_verified event.expression event.environment reservedName event.allocated
        bodyEntry.base.normal.facts (bodyEntry.base.local reservedName reservedArgument).inputs).history
  have ordinaryHistory := extends_trans ordinaryFilterHistory (extends_trans reserveHistory bodyCallbackHistory)
  have bodyCallbackGrowth : Grows event.allocated event.afterBody := by
    simpa only [event.bodyDone, Outcome.state] using
      (callback_verified event.expression event.environment reservedName event.allocated
        bodyEntry.base.normal.facts (bodyEntry.base.local reservedName reservedArgument).inputs).growth
  have reservedGrowth : Grows event.cut event.allocated :=
    ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
  have cutGrowth := grows_trans reservedGrowth bodyCallbackGrowth
  have bodyHistory : Extends afterRawBody.nodes.issued event.afterBody.nodes.issued := by
    simpa only [work, bodyFilter, Outcome.state] using
      (filter_verified reservedName rawBody afterRawBody bodyRawContext.normal.facts bodyAvailable).history
  have ordinaryFixedFresh : .inl ordinaryName ∉ support (.binder true event.expression) fixedInputs :=
    SourceCurrentNativeNormalizationInputs.ordinary_fresh_fixed event.expression fixedInputs
      (fun _ : Unit => .depth) event.before event.afterDepth
      (by simpa only [fixedMap] using event.context.base) event.depth
      (by simpa only [fixedMap] using event.depthDone)
  have reservedFixedFresh : .inl reservedName ∉ support (.binder true event.expression) fixedInputs :=
    SourceCurrentNativeNormalizationInputs.reserved_fresh_fixed (.binder true event.expression) fixedInputs
      (fun _ : Unit => .depth) event.cut (by simpa only [fixedMap] using cutContext.base)
      event.key event.missing
  have ordinaryFresh : ∀ atom ∈ atoms, .inl (ordinaryNames atom) ∉ support event.expression bodyInputs := by
    simpa only [atoms, ordinaryNames, bodyInputs, List.map_nil] using
      extend_fresh_on event.expression fixedInputs [] (fun _ : Unit => .depth) ordinaryName
        (by intro atom impossible; cases impossible) ordinaryFixedFresh
  have reservedFresh : ∀ atom ∈ atoms, .inl (reservedNames atom) ∉ support event.expression bodyInputs := by
    simpa only [atoms, reservedNames, bodyInputs, List.map_nil] using
      extend_fresh_on event.expression fixedInputs [] (fun _ : Unit => .depth) reservedName
        (by intro atom impossible; cases impossible) reservedFixedFresh
  have covered : ∀ atom, .inr atom ∈ bodyInputs → atom ∈ atoms := by
    intro atom member
    rcases List.mem_cons.mp member with same | member
    · exact (Sum.inr.inj same) ▸ List.mem_singleton_self
    · obtain ⟨selected, present, same⟩ := List.mem_map.mp member
      obtain ⟨value, _, rfl⟩ := List.mem_map.mp present
      cases same
  have ordinaryUnused : ordinaryName ∉ deepNames event.ordinary := by
    simpa only [InternedFreshOrdinaryDepthHeap.usesLocal, decide_eq_false_iff_not] using unused
  have ordinaryRawUnused : ordinaryName ∉ deepNames rawOrdinary := by
    intro member
    have retained := (InternedDeepFreeNormalization.filter_deep ordinaryName ordinaryName rawOrdinary
      afterRawOrdinary ordinaryRawContext.normal ordinaryAvailable).mpr member
    exact ordinaryUnused (by simpa only [ordinaryFilter] using retained)
  have ordinaryShallow : ∀ atom ∈ atoms, ordinaryNames atom ∉ deepNames rawOrdinary := by
    intro atom selected
    have same := List.mem_singleton.mp selected
    subst atom
    exact ordinaryRawUnused
  have bodyShallow := deep_transport_on event.expression bodyInputs atoms ordinaryNames reservedNames
    event.afterDepth afterRawOrdinary event.allocated afterRawBody ordinaryContext bodyContext
    ordinaryEntry.depth bodyEntry.depth rawOrdinary rawBody ordinaryRawActual bodyRawActual
    covered ordinaryShallow reservedFresh
  have stripped := compared event.afterDepth event.allocated afterRawOrdinary afterRawBody
    ordinaryContext bodyContext ordinaryEntry.depth bodyEntry.depth rawOrdinary rawBody
    ordinaryRawActual bodyRawActual ordinaryGrowth bodyGrowth ordinaryHistory bodyHistory
    ordinaryFresh reservedFresh ordinaryShallow
  have bodyRawUnused : reservedName ∉ deepNames rawBody := bodyShallow (.inl ()) List.mem_singleton_self
  have bodyUnused : reservedName ∉ deepNames event.body := by
    intro member
    exact bodyRawUnused ((InternedDeepFreeNormalization.filter_deep reservedName reservedName rawBody
      afterRawBody bodyRawContext.normal bodyAvailable).mp (by simpa only [bodyFilter] using member))
  have erasedSame : eraseSelf ordinaryName event.ordinary = eraseSelf reservedName event.body := by
    by_cases live : .inr (.inl ()) ∈ support event.expression bodyInputs
    · have ordinaryRoot := live_root event.expression bodyInputs ordinaryNames event.afterDepth afterRawOrdinary
        ordinaryContext rawOrdinary ordinaryRawActual (.inl ()) live ordinaryRawUnused
      have bodyRoot := live_root event.expression bodyInputs reservedNames event.allocated afterRawBody
        bodyContext rawBody bodyRawActual (.inl ()) live bodyRawUnused
      have rootSame : InternedRootAlternativeLists.remove ordinaryName (unionMembers rawOrdinary) =
          InternedRootAlternativeLists.remove reservedName (unionMembers rawBody) := by
        simpa only [atoms, ordinaryNames, reservedNames, List.map_cons, List.map_nil,
          Sum.elim_inl, stripMany] using stripped
      have result := SourceCurrentNativeLocalRecordErasure.same ordinaryName reservedName rawOrdinary rawBody
        afterRawOrdinary afterRawBody event.afterBody ordinaryRawContext.normal bodyRawContext.normal
        (SourceCurrentNativeLocalRecordErasure.root_reference rawOrdinary ordinaryName ordinaryRoot)
        (SourceCurrentNativeLocalRecordErasure.root_reference rawBody reservedName bodyRoot)
        ordinaryAvailable bodyAvailable rootSame
        (by simpa only [ordinaryFilter] using cutGrowth)
        (by simpa only [bodyFilter] using grows_refl event.afterBody)
      simpa only [ordinaryFilter, bodyFilter] using result
    · have inactive : ∀ atom, .inr atom ∉ support event.expression bodyInputs := by
        intro atom supported
        have same := List.mem_singleton.mp (covered atom
          (support_varying_member event.expression bodyInputs atom supported))
        exact live (same ▸ supported)
      have finalContext : Context event.afterBody event.environment := by
        simpa only [event.bodyDone, Outcome.state] using
          bodyEntry.base.callback event.expression reservedName reservedArgument
      have rawSame := InternedFreshOrdinaryLiveInputReplay.build_same event.expression bodyInputs
        ordinaryNames reservedNames (by
          intro label member
          cases label with
          | inl fixed => rfl
          | inr atom => exact False.elim (inactive atom (live_support event.expression bodyInputs (.inr atom) member)))
        event.afterDepth event.allocated event.afterBody afterRawOrdinary afterRawBody
        ordinaryContext bodyContext finalContext.normal.facts.coherent rawOrdinary rawBody
        ordinaryRawActual bodyRawActual ordinaryGrowth bodyGrowth
      have ordinaryAbsent : ordinaryName ∉ rawOrdinary.free := by
        intro named
        obtain ⟨label, present, same⟩ := List.mem_map.mp
          ((SourceCurrentNativeNormalizationInputs.actual_free event.expression bodyInputs ordinaryNames
            event.afterDepth afterRawOrdinary ordinaryContext rawOrdinary ordinaryRawActual _).mp named)
        cases label with
        | inl fixed => exact ordinaryFresh (.inl ()) List.mem_singleton_self (same ▸ present)
        | inr atom => exact inactive atom present
      have bodyAbsent : reservedName ∉ rawBody.free := by
        intro named
        obtain ⟨label, present, same⟩ := List.mem_map.mp
          ((SourceCurrentNativeNormalizationInputs.actual_free event.expression bodyInputs reservedNames
            event.allocated afterRawBody bodyContext rawBody bodyRawActual _).mp named)
        cases label with
        | inl fixed => exact reservedFresh (.inl ()) List.mem_singleton_self (same ▸ present)
        | inr atom => exact inactive atom present
      have ordinaryIdentity := filter_absent ordinaryName rawOrdinary afterRawOrdinary
        ordinaryRawContext.normal ordinaryAvailable ordinaryAbsent
      have bodyIdentity := filter_absent reservedName rawBody afterRawBody bodyRawContext.normal bodyAvailable bodyAbsent
      have ordinarySame : event.ordinary = rawOrdinary :=
        congrArg Prod.fst (ordinaryFilter.symm.trans ordinaryIdentity)
      have bodySame : event.body = rawBody := congrArg Prod.fst (bodyFilter.symm.trans bodyIdentity)
      rw [ordinarySame, bodySame, erase_absent ordinaryName rawOrdinary ordinaryAbsent,
        erase_absent reservedName rawBody bodyAbsent]
      exact rawSame
  have localNormal := InternedDeepLocalNormal.callback_local event.expression event.environment reservedName
    event.allocated bodyEntry.base.normal (bodyEntry.base.local reservedName reservedArgument).inputs
    event.body event.afterBody event.bodyDone
  exact (finish_true_eq_erase event.entry event.body event.depth event.ordinary localNormal bodyUnused).trans erasedSame.symm

end MicroCFTA.SourceCurrentNativeNormalizedComparisonCandidate
