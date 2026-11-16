import MicroCFTA.SourcePruningEnumerationRealEagerParkedRawBucketReceipt
import MicroCFTA.SourcePruningEnumerationSharedArrowBucketFragmentWitness
import MicroCFTA.SourceSynthesisCurrentDonePendingTypes
import MicroCFTA.SourcePruningEnumerationRealPrefixContinuingResources
import MicroCFTA.SourcePruningEnumerationParkedLanguage
import MicroCFTA.SourcePruningEnumerationPartialOutput

namespace MicroCFTA.SourceSynthesisCurrentParkedArrowDoneAssignment
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule
open InternedConstructorTemplates InternedProbeProvenance
open Cache EnumerationCompressionFrame
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisUniverseCallerBoundary (ordinarySymbols)
open SourceSynthesisFiniteTypeWitnesses (TypeIn)
open SourcePruningEnumerationNodes (lookupNode)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Core" => EnumerationState.State Symbol Guard
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Memos" => EndpointMemoGateTrace.Memos
set_option autoImplicit false
attribute [local instance] SourcePruningEnumerationRecursion.recursionMonadList
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq FullSyntax.Formula] [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

theorem source_parked_arrow_done_assignment
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok expression)
    (rootValue : Node) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty =
      InternedNestedConstruction.Outcome.done rootValue sourceHeap)
    (key : InternedBinderProtocol.NodeKey) (universeEntry : Interned InternedBinderProtocol.NodeKey)
    (body muDepth ordinary : Node)
    (storedU : sourceHeap.nodeRecords key = some (.mu universeEntry body muDepth ordinary))
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : EnumerationState.Graph Symbol Guard) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Guard))
    (order : Metadata Typing → List Nat → Option Nat) (workFuel depth uv heldHandle : Nat)
    (metadata updated : Metadata Typing) (caller : Caller width) (memos : Memos)
    (before parked : Cached) (checked core : Core)
    (inventory : SourceCurrentAllocatedNativeInventoryState.Inventory)
    (packet : SourcePruningEnumerationRecursive.Packet formulas solver inventory caller memos metadata before)
    (profile : SourceCurrentAllocatedNativeResourceForecast.Profile) (property : Guard → Prop)
    (bounded : SourceCurrentConstrainedCapGeneratedQueryResources.Fits profile caller.checked)
    (known : SourceEqualityAnnotationHeap.Heap property caller.checked.native.machine.heap)
    (growth : Grows sourceHeap caller.checked.native.machine.heap)
    (irreducible : SourceCurrentRequiredUnionNormal.UnionNormal caller.checked.native.machine.heap)
    (selected : SourcePruningEnumerationRestart.decision none order metadata before = some (.expand uv))
    (bucket : List Suspended)
    (atHeld : before.core.values[uv]? = some (.unenumerated (some heldHandle) bucket))
    (arrowPaths : ∀ sc ∈ bucket, ∀ path ∈ EqualityTrie.fromPathTrie sc.trie,
      path = [1] ∨ path = [2])
    (actual : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates none order metadata
      workFuel workFuel workFuel workFuel workFuel workFuel uv caller before memos.query =
      .parked checked (some parked) (some [.ok ((updated, some .done), core)]))
    (onlyU : ∀ (slot handle : Nat) (scs : List Suspended),
      before.core.values[slot]? = some (.unenumerated (some handle) scs) →
      ∀ value, lookupNode caller.checked.native.machine.heap handle = some value →
      ∀ atom ∈ InternedBoundaryAtoms.atoms value, atom = .mu universeEntry.identity)
    (noneBuckets : ∀ (slot : Nat) (scs : List Suspended),
      before.core.values[slot]? = some (.unenumerated none scs) → scs = []) :
    SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow
      (SourcePruningEnumerationSharedEagerChildren.eagerChild
        checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
      (SourcePruningOuterNarrow.narrow holeKey fits admits)
      graph templates checkEmpty edgesOf none order workFuel (depth + 1)
      metadata caller memos.query before (some (.expand uv)) =
      .complete [⟨none, EnumerationExpandableIndex.frame core parked, caller, memos.query⟩]
        caller memos.query ∧
    ∃ (resolved : Core) (rho : Nat → Term Symbol),
      Frame before.core resolved ∧
      resolved.values[uv]? = some (.unenumerated (some heldHandle) bucket) ∧
      Success (setValue uv (.unenumerated (some heldHandle) [])) resolved () checked ∧
      parked.core = checked ∧ core = checked ∧
      SourcePruningPartialRenderingSemantics.StoredEquations rho before.core ∧
      SourcePruningPartialRenderingSemantics.StoredEquations rho resolved ∧
      SourcePruningPartialRenderingSemantics.StoredEquations rho checked ∧
      SourcePruningPartialRenderingSemantics.StoredEquations rho core ∧
      Fragments.stateSatisfies before.core.representatives
        (EnumerationCorrectness.heap (SourcePruningEnumerationNativeLanguage.handles
          (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
          before.core.values) rho ∧
      Fragments.stateSatisfies checked.representatives
        (EnumerationCorrectness.heap (SourcePruningEnumerationNativeLanguage.handles
          (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
          checked.values) rho ∧
      Fragments.stateSatisfies core.representatives
        (EnumerationCorrectness.heap (SourcePruningEnumerationNativeLanguage.handles
          (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
          core.values) rho ∧
      (∀ sc ∈ bucket, Suspended.Holds rho (rho uv) sc) ∧
      (∀ (occurrence : Nat) sc, bucket[occurrence]? = some sc → Suspended.Holds rho (rho uv) sc) ∧
      (∀ slot node scs, before.core.values[slot]? = some (.unenumerated node scs) →
        TypeIn (SourceSynthesisCurrentContext.constructorCatalog lib query) (rho slot)) ∧
      (EnumerationCorrectness.guardsHold
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        rho before.core.obligations →
        EnumerationCorrectness.Satisfies (SourcePruningEnumerationNativeLanguage.handles
          (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true) rho before.core ∧
        EnumerationCorrectness.Satisfies (SourcePruningEnumerationNativeLanguage.handles
          (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true) rho checked ∧
        EnumerationCorrectness.Satisfies (SourcePruningEnumerationNativeLanguage.handles
          (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true) rho core) ∧
      ∀ (readFuel : Nat) (actualPartial : SourcePruningTemplates.PartialTerm) (after : Core),
        Success (SourcePruningEnumerationPartialOutput.rootPartial
          caller.checked.native.machine.heap readFuel) core actualPartial after →
        SourcePruningPartialMatch.Completes rho actualPartial (rho 0)
 := by
  obtain ⟨ready, _incoming, _selectedValue⟩ := SourcePruningEnumerationRestart.selected none order metadata
    caller before uv packet.valid packet.safe selected
  obtain ⟨handle, rawBucket, readAfter, value, root, size, resolved,
      _reading, stored, path, readFrame, _decoded, _boundary, _checking, _represented, representativeFrame,
      _seen, resolvedStored, cleared, checkedEq, parkedEq, _adapted, _restarted,
      _updatedEq, coreEq, nextEq, _notStuck, _targetAliases, eagerRestart⟩ :=
    SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.parked_singleton_removed_bucket_receipt
      holeKey fits admits graph templates checkEmpty edgesOf none order workFuel depth uv
      metadata updated caller memos.query before parked checked core (some .done) packet.safe.1.total actual
  have rootEq : root = uv := (UnionFind.reaches_unique path ready.root.choose_spec).1
  subst root
  have payload := UVarValue.unenumerated.inj (Option.some.inj (atHeld.symm.trans stored))
  have handleEq : heldHandle = handle := Option.some.inj payload.1
  have bucketEq : bucket = rawBucket := payload.2
  subst handle
  subst rawBucket
  have wholeFrame : Frame before.core resolved := readFrame.trans representativeFrame
  have inside : uv < resolved.values.length := by
    rw [wholeFrame.values]
    exact (List.getElem?_eq_some_iff.mp atHeld).1
  have checkedAtHeld : checked.values[uv]? = some (.unenumerated (some heldHandle) []) := by
    rw [checkedEq]
    exact List.getElem?_set_self inside
  have sourceCallerUnchanged : SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow
      (SourcePruningEnumerationSharedEagerChildren.eagerChild
        checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
      (SourcePruningOuterNarrow.narrow holeKey fits admits)
      graph templates checkEmpty edgesOf none order workFuel (depth + 1)
      metadata caller memos.query before (some (.expand uv)) =
      .complete [⟨none, EnumerationExpandableIndex.frame core parked, caller, memos.query⟩]
        caller memos.query := by
    rw [eagerRestart, SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow]
  constructor
  · exact sourceCallerUnchanged
  · have current := SourcePruningEnumerationSharedRecursive.prefix_real_continuing_current_at_original_budget
      holeKey fits admits graph templates none order metadata formulas solver inventory caller memos before packet
      profile property bounded known workFuel uv selected
    dsimp only at current
    rw [actual] at current
    obtain ⟨returned, returnedEq, _returnedCore, _raw, afterPacket⟩ := current.1
    have sameReturned : returned = parked := (Option.some.inj returnedEq).symm
    subst returned
    have normal := packet.context.ready.semantic.ready.semantic.1.normal
    have done : SourcePruningEnumerationRestart.decision none order metadata parked = some .done := nextEq.symm
    have afterOnlyU : ∀ (slot handle : Nat) (scs : List Suspended),
        parked.core.values[slot]? = some (.unenumerated (some handle) scs) →
        ∀ value, lookupNode caller.checked.native.machine.heap handle = some value →
        ∀ atom ∈ InternedBoundaryAtoms.atoms value, atom = .mu universeEntry.identity := by
      intro slot handle scs present node decoded atom occurrence
      rw [parkedEq] at present
      by_cases same : slot = uv
      · subst slot
        have payload := UVarValue.unenumerated.inj (Option.some.inj (checkedAtHeld.symm.trans present))
        have identity : heldHandle = handle := Option.some.inj payload.1
        subst handle
        exact onlyU uv heldHandle bucket atHeld node decoded atom occurrence
      · have old : before.core.values[slot]? = some (.unenumerated (some handle) scs) := by
          rw [checkedEq] at present
          simpa only [List.getElem?_set_ne (Ne.symm same), wholeFrame.values] using present
        exact onlyU slot handle scs old node decoded atom occurrence
    have afterNone : ∀ (slot : Nat) (scs : List Suspended),
        checked.values[slot]? = some (.unenumerated none scs) → scs = [] := by
      intro slot scs present
      by_cases same : slot = uv
      · subst slot
        rw [checkedAtHeld] at present
        cases present
      · have old : before.core.values[slot]? = some (.unenumerated none scs) := by
          rw [checkedEq] at present
          simpa only [List.getElem?_set_ne (Ne.symm same), wholeFrame.values] using present
        exact noneBuckets slot scs old
    have nativeMembers := SourceSynthesisCurrentDonePendingTypes.done_pending_type_members
      formulas solver ambient lib query signed expression accepted rootValue sourceHeap built
      key universeEntry body muDepth ordinary storedU order metadata caller parked afterPacket.valid done
      normal irreducible growth afterOnlyU
    obtain ⟨level, frontier, ordered⟩ := packet.ordered
    obtain ⟨_witnessResolved, rho, _witnessStored, _witnessClear, _witnessParked, _witnessCore,
        aliases, equations, held, indexed, typed⟩ :=
      SourcePruningEnumerationSharedArrowBucketFragmentWitness.selected_parked_arrow_bucket_fragment_assignment
        holeKey fits admits graph templates checkEmpty edgesOf none order workFuel depth uv heldHandle
        metadata updated caller memos.query before parked checked core (some .done)
        packet.safe level frontier ordered packet.pending packet.valid selected bucket atHeld arrowPaths actual
        (SourceSynthesisCurrentContext.constructorCatalog lib query)
    have beforeEquations : SourcePruningPartialRenderingSemantics.StoredEquations rho before.core :=
      ⟨aliases, fun slot fragment present => (equations slot fragment present).symm⟩
    have resolvedEquations : SourcePruningPartialRenderingSemantics.StoredEquations rho resolved :=
      (SourcePruningPartialRenderingSemantics.storedEquations_frame rho before.core resolved wholeFrame).mpr beforeEquations
    have checkedEquations : SourcePruningPartialRenderingSemantics.StoredEquations rho checked := by
      refine ⟨?_, ?_⟩
      · simpa only [checkedEq] using resolvedEquations.1
      · intro slot fragment present
        by_cases same : slot = uv
        · subst slot
          rw [checkedAtHeld] at present
          cases present
        · have old : resolved.values[slot]? = some (.enumerated fragment) := by
            rw [checkedEq] at present
            simpa only [List.getElem?_set_ne (Ne.symm same)] using present
          exact resolvedEquations.2 slot fragment old
    have typedChecked : ∀ slot node scs, checked.values[slot]? = some (.unenumerated node scs) →
        TypeIn (SourceSynthesisCurrentContext.constructorCatalog lib query) (rho slot) := by
      intro slot node scs present
      by_cases same : slot = uv
      · subst slot
        exact typed uv (some heldHandle) bucket atHeld
      · have old : before.core.values[slot]? = some (.unenumerated node scs) := by
          rw [checkedEq] at present
          simpa only [List.getElem?_set_ne (Ne.symm same), wholeFrame.values] using present
        exact typed slot node scs old
    let language := SourcePruningEnumerationNativeLanguage.handles
      (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap
    have checkedModel : Fragments.stateSatisfies checked.representatives
        (EnumerationCorrectness.heap language checked.values) rho := by
      refine ⟨checkedEquations.1, ?_⟩
      intro slot
      cases present : checked.values[slot]? with
      | none =>
          simp only [EnumerationCorrectness.heap, present, Option.getD_none, EnumerationCorrectness.slot,
            Fragments.slotSatisfies]
      | some currentValue =>
          cases currentValue with
          | eliminated =>
              simp only [EnumerationCorrectness.heap, present, Option.getD_some, EnumerationCorrectness.slot,
                Fragments.slotSatisfies]
          | enumerated fragment =>
              simpa only [EnumerationCorrectness.heap, present, Option.getD_some, EnumerationCorrectness.slot,
                Fragments.slotSatisfies] using checkedEquations.2 slot fragment present
          | unenumerated node scs =>
              have termTyped := typedChecked slot node scs present
              cases node with
              | none =>
                  have emptyBucket := afterNone slot scs present
                  subst scs
                  simp only [EnumerationCorrectness.heap, present, Option.getD_some, EnumerationCorrectness.slot]
                  change True ∧ ∀ obligation ∈ ([] : List (Fragments.Obligation Symbol)), obligation rho (rho slot)
                  exact ⟨True.intro, fun _ impossible => by cases impossible⟩
              | some handle =>
                  have actualSlot : parked.core.values[slot]? = some (.unenumerated (some handle) scs) := by
                    rw [parkedEq]
                    exact present
                  obtain ⟨emptyBucket, admitted⟩ := nativeMembers slot handle scs actualSlot
                  have member := admitted (rho slot) termTyped
                  subst scs
                  simp only [EnumerationCorrectness.heap, present, Option.getD_some, EnumerationCorrectness.slot]
                  change language handle (rho slot) ∧
                    ∀ obligation ∈ ([] : List (Fragments.Obligation Symbol)), obligation rho (rho slot)
                  exact ⟨member, fun _ impossible => by cases impossible⟩
    have checkedTrue : Satisfies language (fun _ _ => True) rho checked :=
      ⟨checkedModel, fun _ _ => True.intro⟩
    have resolvedTrue := (SourcePruningEnumerationRecursion.clear_satisfies language (fun _ _ => True)
      rho resolved checked uv (some heldHandle) bucket resolvedStored cleared).mpr ⟨checkedTrue, held⟩
    have beforeTrue := (SourcePruningEnumerationNativeLanguage.satisfies_frame language (fun _ _ => True)
      rho before.core resolved wholeFrame).mp resolvedTrue
    have coreEquations : SourcePruningPartialRenderingSemantics.StoredEquations rho core := by
      rw [coreEq]
      exact checkedEquations
    have coreModel : Fragments.stateSatisfies core.representatives
        (EnumerationCorrectness.heap language core.values) rho := by
      rw [coreEq]
      exact checkedModel
    refine ⟨resolved, rho, wholeFrame, resolvedStored, cleared, parkedEq, coreEq,
      beforeEquations, resolvedEquations, checkedEquations, coreEquations,
      beforeTrue.1, checkedModel, coreModel, held, indexed, typed, ?_, ?_⟩
    · intro guarded
      have beforeModel : Satisfies language
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true) rho before.core :=
        ⟨beforeTrue.1, guarded⟩
      have resolvedModel := (SourcePruningEnumerationNativeLanguage.satisfies_frame language
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        rho before.core resolved wholeFrame).mpr beforeModel
      have currentModel := ((SourcePruningEnumerationRecursion.clear_satisfies language
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        rho resolved checked uv (some heldHandle) bucket resolvedStored cleared).mp resolvedModel).1
      refine ⟨beforeModel, currentModel, ?_⟩
      rw [coreEq]
      exact currentModel
    · intro readFuel actualPartial after observed
      exact SourcePruningEnumerationPartialOutput.rootPartial_completes_of_stored_equations
        caller.checked.native.machine.heap rho readFuel core after actualPartial
        (by rw [coreEq, checkedEq]; exact wholeFrame.total packet.safe.1.total) coreEquations observed

end MicroCFTA.SourceSynthesisCurrentParkedArrowDoneAssignment
