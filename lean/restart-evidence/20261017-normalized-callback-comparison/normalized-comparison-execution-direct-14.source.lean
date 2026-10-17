import MicroCFTA.SourceCurrentNativeNormalizedComparisonUnion
import MicroCFTA.SourceCurrentNativeNormalizedErasure
import MicroCFTA.SourceCurrentNativeMuPublicationCallbacks
import MicroCFTA.SourceCurrentNativeRequestProbes
import MicroCFTA.SourceCurrentNativeBinderExecution
import MicroCFTA.SourceCurrentNativeNormalizedComparisonCandidate

/-!
# Actual normalized source comparison and causal Mu payloads

The source comparison uses a pure law of the common record table. The
publication-history induction establishes that law before each new write.
-/
set_option maxHeartbeats 1600000
namespace MicroCFTA.SourceCurrentNativeNormalizedComparisonExecution
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome finish)
open InternedNestedFacts (Facts)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryContext InternedFreshOrdinaryLiveInputs
open InternedDeepFreeDepth InternedDepthSemantics InternedStoredMuOrigins
open SourceCurrentNativeNormalizedComparison SourceCurrentNativeNormalizedComparisonFinite
open SourceCurrentNativeNormalizedComparisonInactive SourceCurrentNativeNormalizedErasure
open SourceCurrentNativeStrippedAlternatives SourceCurrentNativeCallbackErasure
open SourceCurrentNativeNormalizationInputs (support)
open InternedBinderProtocol (Reference NodeKey)
variable {Atom : Type}

private def MuLaw (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) : Prop :=
  InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = false →
    finish true (.mu entry body depth ordinary) = eraseSelf (.uninterned (ordinaryLevel depth)) ordinary

private def MuHeap (state : State Symbol Guard) : Prop :=
  ∀ key entry body depth ordinary, state.nodeRecords key = some (.mu entry body depth ordinary) →
    MuLaw entry body depth ordinary

private theorem muHeap_empty : MuHeap (empty (Symbol := Symbol) (Guard := Guard)) := by
  intro key entry body depth ordinary present
  cases present

private theorem muHeap_retain (before after : State Symbol Guard) (known : MuHeap before)
    (old : InternedShallowHeap.NoNewMu before after) : MuHeap after := by
  intro key entry body depth ordinary present
  exact known key entry body depth ordinary (old key entry body depth ordinary present)

private theorem muHeap_complete (smart : Bool) (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (before : State Symbol Guard)
    (known : MuHeap before) (candidate : MuLaw entry body depth ordinary) :
    MuHeap (InternedNestedRequestFacts.complete smart entry body depth ordinary before).state := by
  intro key selected selectedBody selectedDepth selectedOrdinary present
  rcases InternedRecordCoherence.record_cases before.nodeRecords (muKey depth ordinary) key
    (.mu entry body depth ordinary) (.mu selected selectedBody selectedDepth selectedOrdinary) present with old | ⟨_, same⟩
  · exact known key selected selectedBody selectedDepth selectedOrdinary old
  · cases same
    exact candidate

private theorem request_unused [DecidableEq (EdgeKey Symbol Guard)]
    (depth ordinary : Value Symbol Guard)
    (callback : Reference → State Symbol Guard → Outcome Symbol Guard (Value Symbol Guard))
    (before after common : State Symbol Guard) (value : Value Symbol Guard)
    (actual : InternedNestedConstruction.request true depth ordinary callback before = .done value after)
    (facts : Facts after) (depthAvailable : Available after depth) (ordinaryAvailable : Available after ordinary)
    (growth : Grows after common) (known : MuHeap common)
    (unused : InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = false) :
    value = eraseSelf (.uninterned (ordinaryLevel depth)) ordinary := by
  obtain ⟨entry, body, present, returned⟩ := SourceCurrentNativeRequestProbes.request_probes true depth ordinary
    callback before value after actual facts depthAvailable ordinaryAvailable
  exact returned.trans (known _ entry body depth ordinary (growth.nodeRecords _ _ present) unused)

private theorem roots_edges (edges : List (InternedNestedConstruction.EdgeSyntax Symbol Guard))
    (environment : List (Shape Label)) : (evaluateEdges edges environment).roots = [] := by
  induction edges with
  | nil => simp only [evaluateEdges]
  | cons edge rest ih =>
      cases edge with
      | mk symbol guard children =>
          simp only [evaluateEdges, combine, ih]
          unfold InternedDepthSemantics.edge
          split <;> rfl

private theorem empty_compared [DecidableEq (EdgeKey Symbol Guard)]
    (inputs : List (Sum (Value Symbol Guard) Atom)) (atoms : List Atom)
    (firstNames secondNames : Atom → Reference) (common : State Symbol Guard)
    (normal : Normal common) : Compared .empty inputs atoms firstNames secondNames common := by
  apply inactive_compared .empty inputs atoms firstNames secondNames common normal
  intro atom member
  simp only [support, InternedFreeNameSemantics.evaluate, List.not_mem_nil] at member

private theorem strip_nil (names : List Reference) : stripMany names ([] : List (Value Symbol Guard)) = [] := by
  induction names with
  | nil => rfl
  | cons name rest ih => simpa only [stripMany, InternedRootAlternativeLists.remove, List.filter_nil] using ih

private theorem strip_reference (names : List Reference) (own : Reference) (selected : own ∈ names) :
    stripMany names (unionMembers (Value.reference (Symbol := Symbol) (Guard := Guard) own)) = [] := by
  have result := strip_eraseSelf names own (Value.reference (Symbol := Symbol) (Guard := Guard) own) selected
  simpa only [eraseSelf, Value.referenceOf, ↓reduceIte, unionMembers, strip_nil] using result.symm

private theorem var_compared [DecidableEq (EdgeKey Symbol Guard)]
    (index : Nat) (inputs : List (Sum (Value Symbol Guard) Atom)) (atoms : List Atom)
    (firstNames secondNames : Atom → Reference) (common : State Symbol Guard)
    (normal : Normal common) (covered : ∀ atom, .inr atom ∈ inputs → atom ∈ atoms) :
    Compared (.var index) inputs atoms firstNames secondNames common := by
  cases found : inputs[index]? with
  | none =>
      apply inactive_compared (.var index) inputs atoms firstNames secondNames common normal
      intro atom member
      simp [support, InternedFreeNameSemantics.evaluate, List.getElem?_map, found] at member
  | some selected =>
      cases selected with
      | inl value =>
          apply inactive_compared (.var index) inputs atoms firstNames secondNames common normal
          intro atom member
          simp [support, InternedFreeNameSemantics.evaluate, List.getElem?_map, found,
            SourceCurrentNativeNormalizationInputs.inputNames] at member
      | inr atom =>
          intro before later after final _context _laterContext _heap _laterHeap first second
            leftActual rightActual _growth _laterGrowth _history _laterHistory _leftFresh _rightFresh _shallow
          have selected := covered atom (List.mem_of_getElem? found)
          simp only [build, List.getElem?_map, found, Option.map_some, Option.getD_some, input,
            Outcome.done.injEq] at leftActual rightActual
          rw [← leftActual.1, ← rightActual.1,
            strip_reference _ _ (List.mem_map.mpr ⟨atom, selected, rfl⟩),
            strip_reference _ _ (List.mem_map.mpr ⟨atom, selected, rfl⟩)]

private theorem node_compared [DecidableEq (EdgeKey Symbol Guard)]
    (edges : List (InternedNestedConstruction.EdgeSyntax Symbol Guard))
    (inputs : List (Sum (Value Symbol Guard) Atom)) (atoms : List Atom)
    (firstNames secondNames : Atom → Reference) (common : State Symbol Guard)
    (normal : Normal common) (covered : ∀ atom, .inr atom ∈ inputs → atom ∈ atoms) :
    Compared (.node edges) inputs atoms firstNames secondNames common := by
  intro before later after final context laterContext heap laterHeap first second
    leftActual rightActual growth laterGrowth history laterHistory leftFresh rightFresh shallow
  by_cases live : ∃ atom, .inr atom ∈ support (.node edges) inputs
  · obtain ⟨atom, supported⟩ := live
    have selected := covered atom (support_varying_member (.node edges) inputs atom supported)
    have root := active_roots (.node edges) inputs firstNames before after context heap first leftActual
      atom supported (shallow atom selected)
    simp only [symbolic, evaluate, roots_edges, List.not_mem_nil] at root
  · exact inactive_compared (.node edges) inputs atoms firstNames secondNames common normal
      (fun atom member => live ⟨atom, member⟩) before later after final context laterContext heap laterHeap
      first second leftActual rightActual growth laterGrowth history laterHistory leftFresh rightFresh shallow

private theorem strip_callback [DecidableEq (EdgeKey Symbol Guard)]
    (body : Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (own : Reference) (before rawAfter after : State Symbol Guard)
    (context : Context before environment) (argument : Available before (.reference own))
    (raw value : Value Symbol Guard)
    (rawActual : build body (.reference own :: environment) before = .done raw rawAfter)
    (filtered : run (withoutSelfReference own raw) rawAfter = (value, after))
    (actual : callback body environment own before = .done value after)
    (unused : own ∉ deepNames value) (names : List Reference)
    (outer : ∃ name, name ≠ own ∧ Value.reference name ∈ unionMembers raw) :
    stripMany names (unionMembers (eraseSelf own value)) =
      stripMany (own :: names) (unionMembers raw) := by
  have returned := callback_result body environment own before context argument value after actual unused
  have removed := strip_absent [own] (eraseSelf own value) after returned.1.normal returned.2.1
    (by intro name member; have same := List.mem_singleton.mp member; exact same ▸ returned.2.2)
  have removeErased : InternedRootAlternativeLists.remove own (unionMembers (eraseSelf own value)) =
      unionMembers (eraseSelf own value) := by
    simpa only [stripMany] using removed
  have rawContext : Context rawAfter (.reference own :: environment) := by
    simpa only [rawActual, Outcome.state] using (context.local own argument).build body
  have rawAvailable := (build_verified body _ before context.normal.facts
    (context.local own argument).inputs).result raw rawAfter rawActual
  calc
    stripMany names (unionMembers (eraseSelf own value)) =
        stripMany (own :: names) (unionMembers (eraseSelf own value)) := by
      rw [stripMany, removeErased]
    _ = stripMany (own :: names) (unionMembers value) :=
      strip_eraseSelf (own :: names) own value List.mem_cons_self
    _ = stripMany (own :: names) (unionMembers raw) := by
      have result := SourceCurrentNativeStrippedFilter.filter (own :: names) own raw rawAfter
        rawContext.normal rawAvailable List.mem_cons_self outer
      simpa only [filtered] using result

private theorem extended_covered (inputs : List (Sum (Value Symbol Guard) Atom)) (atoms : List Atom)
    (covered : ∀ atom, .inr atom ∈ inputs → atom ∈ atoms) :
    ∀ atom, .inr atom ∈ (.inr (.inl ()) :: inputs.map liftInput) →
      atom ∈ (.inl () :: atoms.map Sum.inr) := by
  intro atom member
  rcases List.mem_cons.mp member with same | member
  · have equal := Sum.inr.inj same
    exact equal ▸ List.mem_cons_self
  · obtain ⟨selected, present, same⟩ := List.mem_map.mp member
    cases selected with
    | inl value => cases same
    | inr original =>
        have equal := Sum.inr.inj same
        exact equal ▸ List.mem_cons_of_mem _ (List.mem_map.mpr ⟨original, covered original present, rfl⟩)

private theorem ordinary_compared [DecidableEq (EdgeKey Symbol Guard)]
    (body : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom)) (atoms : List Atom)
    (firstNames secondNames : Atom → Reference) (firstOwn secondOwn : Reference)
    (before later rawAfter rawFinal after final common : State Symbol Guard)
    (context : Context before (inputs.map (input firstNames)))
    (laterContext : Context later (inputs.map (input secondNames)))
    (heap : InternedFreshOrdinaryDepthHeap.Heap before)
    (laterHeap : InternedFreshOrdinaryDepthHeap.Heap later)
    (firstArgument : Available before (.reference firstOwn))
    (secondArgument : Available later (.reference secondOwn))
    (firstRaw secondRaw first second : Value Symbol Guard)
    (firstRawActual : build body (.reference firstOwn :: inputs.map (input firstNames)) before = .done firstRaw rawAfter)
    (secondRawActual : build body (.reference secondOwn :: inputs.map (input secondNames)) later = .done secondRaw rawFinal)
    (firstFilter : run (withoutSelfReference firstOwn firstRaw) rawAfter = (first, after))
    (secondFilter : run (withoutSelfReference secondOwn secondRaw) rawFinal = (second, final))
    (firstActual : callback body (inputs.map (input firstNames)) firstOwn before = .done first after)
    (secondActual : callback body (inputs.map (input secondNames)) secondOwn later = .done second final)
    (growth : Grows rawAfter common) (laterGrowth : Grows rawFinal common)
    (history : Extends rawAfter.nodes.issued common.nodes.issued)
    (laterHistory : Extends rawFinal.nodes.issued common.nodes.issued)
    (covered : ∀ atom, .inr atom ∈ inputs → atom ∈ atoms)
    (leftFresh : ∀ atom ∈ atoms, .inl (firstNames atom) ∉ support (.binder true body) inputs)
    (rightFresh : ∀ atom ∈ atoms, .inl (secondNames atom) ∉ support (.binder true body) inputs)
    (leftOwnFresh : firstOwn ∉ (support (.binder true body) inputs).map (Sum.elim id firstNames))
    (rightOwnFresh : secondOwn ∉ (support (.binder true body) inputs).map (Sum.elim id secondNames))
    (unused : firstOwn ∉ deepNames first)
    (shallow : ∀ atom ∈ atoms, firstNames atom ∉ deepNames (eraseSelf firstOwn first))
    (live : ∃ atom, .inr atom ∈ support (.binder true body) inputs)
    (recurse : Compared body (.inr (.inl ()) :: inputs.map liftInput) (.inl () :: atoms.map Sum.inr)
      (Sum.elim (fun _ => firstOwn) firstNames) (Sum.elim (fun _ => secondOwn) secondNames) common) :
    stripMany (atoms.map firstNames) (unionMembers (eraseSelf firstOwn first)) =
      stripMany (atoms.map secondNames) (unionMembers (eraseSelf secondOwn second)) := by
  let extendedInputs := .inr (.inl ()) :: inputs.map liftInput
  let extendedAtoms := .inl () :: atoms.map Sum.inr
  let leftNames := Sum.elim (fun _ : Unit => firstOwn) firstNames
  let rightNames := Sum.elim (fun _ : Unit => secondOwn) secondNames
  have leftContext : Context before (extendedInputs.map (input leftNames)) := by
    simpa only [extendedInputs, leftNames, local_inputs] using context.local firstOwn firstArgument
  have rightContext : Context later (extendedInputs.map (input rightNames)) := by
    simpa only [extendedInputs, rightNames, local_inputs] using laterContext.local secondOwn secondArgument
  have leftActual : build body (extendedInputs.map (input leftNames)) before = .done firstRaw rawAfter := by
    simpa only [extendedInputs, leftNames, local_inputs] using firstRawActual
  have rightActual : build body (extendedInputs.map (input rightNames)) later = .done secondRaw rawFinal := by
    simpa only [extendedInputs, rightNames, local_inputs] using secondRawActual
  have leftFixedFresh : .inl firstOwn ∉ support (.binder true body) inputs := by
    intro member
    exact leftOwnFresh (List.mem_map.mpr ⟨.inl firstOwn, member, rfl⟩)
  have rightFixedFresh : .inl secondOwn ∉ support (.binder true body) inputs := by
    intro member
    exact rightOwnFresh (List.mem_map.mpr ⟨.inl secondOwn, member, rfl⟩)
  have lf := extend_fresh_on body inputs atoms firstNames firstOwn leftFresh leftFixedFresh
  have rf := extend_fresh_on body inputs atoms secondNames secondOwn rightFresh rightFixedFresh
  have rawContext : Context rawAfter (.reference firstOwn :: inputs.map (input firstNames)) := by
    simpa only [firstRawActual, Outcome.state] using (context.local firstOwn firstArgument).build body
  have rawAvailable := (build_verified body _ before context.normal.facts
    (context.local firstOwn firstArgument).inputs).result firstRaw rawAfter firstRawActual
  have rawSecondContext : Context rawFinal (.reference secondOwn :: inputs.map (input secondNames)) := by
    simpa only [secondRawActual, Outcome.state] using (laterContext.local secondOwn secondArgument).build body
  have rawSecondAvailable := (build_verified body _ later laterContext.normal.facts
    (laterContext.local secondOwn secondArgument).inputs).result secondRaw rawFinal secondRawActual
  have leftShallow : ∀ atom ∈ extendedAtoms, leftNames atom ∉ deepNames firstRaw := by
    intro atom selected member
    have filteredMember := (InternedDeepFreeNormalization.filter_deep firstOwn (leftNames atom)
      firstRaw rawAfter rawContext.normal rawAvailable).mpr member
    rw [firstFilter] at filteredMember
    cases atom with
    | inl token => exact unused filteredMember
    | inr atom =>
        have included : atom ∈ atoms := by simpa only [extendedAtoms, List.mem_cons, Sum.inr.injEq,
          reduceCtorEq, false_or, List.mem_map, exists_eq_right] using selected
        exact shallow atom included (by simpa only [eraseSelf_deep, leftNames, Sum.elim_inr] using filteredMember)
  have coverage := extended_covered inputs atoms covered
  have rightShallow := deep_transport_on body extendedInputs extendedAtoms leftNames rightNames
    before rawAfter later rawFinal leftContext rightContext heap laterHeap firstRaw secondRaw
    leftActual rightActual coverage leftShallow rf
  have same := recurse before later rawAfter rawFinal leftContext rightContext heap laterHeap
    firstRaw secondRaw leftActual rightActual growth laterGrowth history laterHistory lf rf leftShallow
  obtain ⟨atom, supported⟩ := live
  have included := covered atom (support_varying_member (.binder true body) inputs atom supported)
  have rawSupported : .inr (.inr atom) ∈ support body extendedInputs :=
    (capture_support body inputs (.inr atom)).mpr supported
  have rawSelected : (.inr atom : Sum Unit Atom) ∈ extendedAtoms :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨atom, included, rfl⟩)
  have leftRoot := live_root body extendedInputs leftNames before rawAfter leftContext firstRaw
    leftActual (.inr atom) rawSupported (leftShallow (.inr atom) rawSelected)
  have rightRoot := live_root body extendedInputs rightNames later rawFinal rightContext secondRaw
    rightActual (.inr atom) rawSupported (rightShallow (.inr atom) rawSelected)
  have leftDifferent : firstNames atom ≠ firstOwn := by
    intro equal
    exact leftOwnFresh (List.mem_map.mpr ⟨.inr atom, supported, equal⟩)
  have rightDifferent : secondNames atom ≠ secondOwn := by
    intro equal
    exact rightOwnFresh (List.mem_map.mpr ⟨.inr atom, supported, equal⟩)
  have rightUnused : secondOwn ∉ deepNames second := by
    intro member
    have rawMember := (InternedDeepFreeNormalization.filter_deep secondOwn secondOwn secondRaw rawFinal
      rawSecondContext.normal rawSecondAvailable).mp (by simpa only [secondFilter] using member)
    exact rightShallow (.inl ()) List.mem_cons_self rawMember
  rw [strip_callback body _ firstOwn before rawAfter after context firstArgument firstRaw first
      firstRawActual firstFilter firstActual unused (atoms.map firstNames) ⟨firstNames atom, leftDifferent, leftRoot⟩,
    strip_callback body _ secondOwn later rawFinal final laterContext secondArgument secondRaw second
      secondRawActual secondFilter secondActual rightUnused (atoms.map secondNames) ⟨secondNames atom, rightDifferent, rightRoot⟩]
  simpa only [extendedAtoms, leftNames, rightNames, List.map_cons, List.map_map, Function.comp_def,
    Sum.elim_inl, Sum.elim_inr] using same

private theorem binder_compared [DecidableEq (EdgeKey Symbol Guard)]
    (smart : Bool) (body : Syntax Symbol Guard)
    (inputs : List (Sum (Value Symbol Guard) Atom)) (atoms : List Atom)
    (firstNames secondNames : Atom → Reference) (common : State Symbol Guard)
    (normal : Normal common) (covered : ∀ atom, .inr atom ∈ inputs → atom ∈ atoms)
    (known : MuHeap common)
    (recurse : ∀ {Other : Type} (localInputs : List (Sum (Value Symbol Guard) Other))
      (localAtoms : List Other) (leftNames rightNames : Other → Reference)
      (_covered : ∀ atom, .inr atom ∈ localInputs → atom ∈ localAtoms),
      Compared body localInputs localAtoms leftNames rightNames common) :
    Compared (.binder smart body) inputs atoms firstNames secondNames common := by
  by_cases live : ∃ atom, .inr atom ∈ support (.binder smart body) inputs
  · intro before later after final context laterContext heap laterHeap first second
      firstActual secondActual growth laterGrowth history laterHistory leftFresh rightFresh shallow
    obtain ⟨atom, supported⟩ := live
    have included := covered atom (support_varying_member (.binder smart body) inputs atom supported)
    obtain ⟨rfl, used⟩ := binder_unused smart body inputs firstNames before after context heap first
      firstActual atom supported (shallow atom included)
    obtain ⟨leftDepth, leftAfterDepth, leftOrdinary, leftCut, leftRaw, leftRawAfter,
      leftDepthDone, leftOrdinaryDone, leftRequest, leftDepthContext, _leftCutContext, leftFinalContext,
      leftRawDone, leftFilter, _leftRawContext, leftRawGrowth, leftRawHistory, leftDepthAvailable, leftOrdinaryAvailable⟩ :=
      SourceCurrentNativeBinderExecution.decompose true body (inputs.map (input firstNames)) before first after
        ⟨context, heap⟩ firstActual
    obtain ⟨rightDepth, rightAfterDepth, rightOrdinary, rightCut, rightRaw, rightRawAfter,
      rightDepthDone, rightOrdinaryDone, rightRequest, rightDepthContext, _rightCutContext, rightFinalContext,
      rightRawDone, rightFilter, _rightRawContext, rightRawGrowth, rightRawHistory, rightDepthAvailable, rightOrdinaryAvailable⟩ :=
      SourceCurrentNativeBinderExecution.decompose true body (inputs.map (input secondNames)) later second final
        ⟨laterContext, laterHeap⟩ secondActual
    have leftUnused : InternedFreshOrdinaryDepthHeap.usesLocal leftDepth leftOrdinary = false :=
      (probes_use body _ before leftAfterDepth leftCut context heap leftDepth leftOrdinary leftDepthDone leftOrdinaryDone).trans used
    have rightUsed := (uses_same body inputs firstNames secondNames).symm.trans used
    have rightUnused : InternedFreshOrdinaryDepthHeap.usesLocal rightDepth rightOrdinary = false :=
      (probes_use body _ later rightAfterDepth rightCut laterContext laterHeap rightDepth rightOrdinary
        rightDepthDone rightOrdinaryDone).trans rightUsed
    have leftReturn := request_unused leftDepth leftOrdinary (callback body _) leftCut after common first
      leftRequest leftFinalContext.base.normal.facts leftDepthAvailable leftOrdinaryAvailable growth known leftUnused
    have rightReturn := request_unused rightDepth rightOrdinary (callback body _) rightCut final common second
      rightRequest rightFinalContext.base.normal.facts rightDepthAvailable rightOrdinaryAvailable laterGrowth known rightUnused
    have localUnused : .uninterned (ordinaryLevel leftDepth) ∉ deepNames leftOrdinary := by
      simpa only [InternedFreshOrdinaryDepthHeap.usesLocal, decide_eq_false_iff_not] using leftUnused
    have localRecurse := recurse (.inr (.inl ()) :: inputs.map liftInput) (.inl () :: atoms.map Sum.inr)
      (Sum.elim (fun _ : Unit => .uninterned (ordinaryLevel leftDepth)) firstNames)
      (Sum.elim (fun _ : Unit => .uninterned (ordinaryLevel rightDepth)) secondNames)
      (extended_covered inputs atoms covered)
    rw [leftReturn, rightReturn]
    apply ordinary_compared body inputs atoms firstNames secondNames
      (.uninterned (ordinaryLevel leftDepth)) (.uninterned (ordinaryLevel rightDepth))
      leftAfterDepth rightAfterDepth leftRawAfter rightRawAfter leftCut rightCut common
      leftDepthContext.base rightDepthContext.base leftDepthContext.depth rightDepthContext.depth
      (InternedNestedProvenance.ordinary_available leftAfterDepth _)
      (InternedNestedProvenance.ordinary_available rightAfterDepth _)
      leftRaw rightRaw leftOrdinary rightOrdinary leftRawDone rightRawDone leftFilter rightFilter
      leftOrdinaryDone rightOrdinaryDone (grows_trans leftRawGrowth growth) (grows_trans rightRawGrowth laterGrowth)
      (extends_trans leftRawHistory history) (extends_trans rightRawHistory laterHistory)
      covered leftFresh rightFresh
      (SourceCurrentNativeNormalizationFreshness.ordinary body inputs firstNames before leftAfterDepth context leftDepth leftDepthDone)
      (SourceCurrentNativeNormalizationFreshness.ordinary body inputs secondNames later rightAfterDepth laterContext rightDepth rightDepthDone)
      localUnused (by simpa only [leftReturn] using shallow) ⟨atom, supported⟩ localRecurse
  · exact inactive_compared (.binder smart body) inputs atoms firstNames secondNames common normal
      (fun atom member => live ⟨atom, member⟩)

private theorem source_compared [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) :
    ∀ {Other : Type} (inputs : List (Sum (Value Symbol Guard) Other)) (atoms : List Other)
      (firstNames secondNames : Other → Reference) (common : State Symbol Guard)
      (_normal : Normal common) (_covered : ∀ atom, .inr atom ∈ inputs → atom ∈ atoms)
      (_known : MuHeap common), Compared expression inputs atoms firstNames secondNames common := by
  intro Other inputs atoms firstNames secondNames common normal covered known
  cases expression with
  | empty => exact empty_compared inputs atoms firstNames secondNames common normal
  | var index => exact var_compared index inputs atoms firstNames secondNames common normal covered
  | node edges => exact node_compared edges inputs atoms firstNames secondNames common normal covered
  | union members =>
      apply SourceCurrentNativeNormalizedComparisonUnion.union_compared members inputs atoms firstNames secondNames common normal covered
      intro expression member
      exact source_compared expression inputs atoms firstNames secondNames common normal covered known
  | binder smart body =>
      apply binder_compared smart body inputs atoms firstNames secondNames common normal covered known
      intro Local localInputs localAtoms leftNames rightNames localCovered
      exact source_compared body localInputs localAtoms leftNames rightNames common normal localCovered known
termination_by sizeOf expression
decreasing_by
  all_goals simp_wf
  all_goals first | omega | exact Nat.lt_trans (List.sizeOf_lt_of_mem member) (by omega)

private theorem history_muHeap [DecidableEq (EdgeKey Symbol Guard)]
    {before after : State Symbol Guard} (history : SourceCurrentNativeMuPublication.History before after) :
    MuHeap before → MuHeap after := by
  induction history with
  | refl state => exact id
  | retain before after old => exact fun known => muHeap_retain before after known old
  | trans first next firstIH nextIH => exact fun known => nextIH (firstIH known)
  | publication event depthHistory ordinaryHistory bodyHistory depthIH ordinaryIH bodyIH =>
      intro known
      have cutKnown := ordinaryIH (depthIH known)
      have allocatedKnown : MuHeap event.allocated := by
        intro key entry body depth ordinary present
        exact cutKnown key entry body depth ordinary present
      have afterBodyKnown := bodyIH allocatedKnown
      have allocatedContext := (SourceCurrentNativeMuPublicationCallbacks.contexts event).2.2
      have cutContext := (SourceCurrentNativeMuPublicationCallbacks.contexts event).2.1
      have argument : Available event.allocated (.reference (.interned event.entry.identity)) :=
        (InternedConstructionProvenance.reserve_available event.key event.cut
          cutContext.base.normal.facts.coherent cutContext.base.normal.facts.cached).2
      have afterBodyContext : SourceCurrentConstrainedCapSourceHistory.Context event.afterBody event.environment := by
        simpa only [event.bodyDone, Outcome.state] using allocatedContext.callback event.expression _ argument
      have candidate : MuLaw event.entry event.body event.depth event.ordinary := by
        apply SourceCurrentNativeNormalizedComparisonCandidate.candidate event
        apply source_compared event.expression _ _ _ _ event.afterBody afterBodyContext.base.normal _ afterBodyKnown
        intro atom member
        rcases List.mem_cons.mp member with same | member
        · exact (Sum.inr.inj same) ▸ List.mem_singleton_self
        · obtain ⟨selected, present, same⟩ := List.mem_map.mp member
          obtain ⟨value, _present, rfl⟩ := List.mem_map.mp present
          cases same
      exact muHeap_complete event.smart event.entry event.body event.depth event.ordinary event.afterBody
        afterBodyKnown candidate

/-- Actual histories from the empty tables establish unused smart readback for every retained Mu. -/
theorem history_unused [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (history : SourceCurrentNativeMuPublication.History empty state)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (present : state.nodeRecords key = some (.mu entry body depth ordinary))
    (unused : InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = false) :
    finish true (.mu entry body depth ordinary) = eraseSelf (.uninterned (ordinaryLevel depth)) ordinary :=
  history_muHeap history muHeap_empty key entry body depth ordinary present unused

/-- A complete closed source constructs its own callback history before the stored readback law is used. -/
theorem closed_unused [DecidableEq (EdgeKey Symbol Guard)] (source : Syntax Symbol Guard)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (present : (build source [] empty).state.nodeRecords key = some (.mu entry body depth ordinary))
    (unused : InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = false) :
    finish true (.mu entry body depth ordinary) = eraseSelf (.uninterned (ordinaryLevel depth)) ordinary :=
  history_unused _ (SourceCurrentNativeMuPublication.closed_history source) key entry body depth ordinary present unused

/-- Closed source construction establishes the common-table law for general original-input comparison. -/
theorem closed_compared [DecidableEq (EdgeKey Symbol Guard)]
    (source expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (atoms : List Atom) (firstNames secondNames : Atom → Reference)
    (covered : ∀ atom, .inr atom ∈ inputs → atom ∈ atoms) :
    Compared expression inputs atoms firstNames secondNames (build source [] empty).state := by
  have actualContext := SourceCurrentConstrainedCapSourceHistory.empty_context.build source
  exact source_compared expression inputs atoms firstNames secondNames _ actualContext.base.normal covered
    (history_muHeap (SourceCurrentNativeMuPublication.closed_history source) muHeap_empty)

end MicroCFTA.SourceCurrentNativeNormalizedComparisonExecution
