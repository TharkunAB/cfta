import MicroCFTA.SourcePruningEnumerationRecursivePacket
import MicroCFTA.SourcePruningEnumerationRenderFuel
import MicroCFTA.EnumerationPartialCompletion
import MicroCFTA.EnumerationRenderability

/-!
# Concrete markers at a current finished native endpoint

Finished selection excludes every active native slot.
Graph-bearing pending slots therefore decode to empty-bucket recursive boundaries.
Stored fragment references exclude pure unknown holes during rendering.
The renderer keeps one exact result and compression endpoint at every larger bound.
This statement does not provide a ground model below a recursive marker.
-/
namespace MicroCFTA.SourcePruningEnumerationDefaultFinishedRendering
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule
open EnumerationDriver EnumerationCompressionFrame EnumerationOrder EnumerationExecution EnumerationDependencies
open EnumerationCarriers EnumerationGraphReferences EnumerationRenderability
open SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable {NativeGuard EnumGuard : Type}

attribute [local instance] EnumerationObservations.partialTransportMonadList
  EnumerationObservations.partialTransportLawfulMonadList

private def Opaque (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (state : State Symbol EnumGuard) : Prop :=
  ∀ (slot handle : Nat) (scs : List Suspended),
    state.values[slot]? = some (UVarValue.unenumerated (some handle) scs) →
    ∃ value, lookupNode heap handle = some value ∧
      MergedOrdinaryHeight.recursiveBoundary value = true ∧ scs = []

private theorem opaque_read (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before after : State Symbol EnumGuard) (inputBoundary : Opaque heap before)
    (stable : RenderStable before after) : Opaque heap after := by
  intro slot handle scs stored
  exact inputBoundary slot handle scs (by simpa only [stable.values] using stored)

private theorem flags_false (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (finished : EnumerationPureSelection.next (fun _ => none) before = .done) :
    ∀ slot, slot < before.core.counter → before.expandable slot = false := by
  cases seen : EnumerationIndexSelection.candidates before with
  | nil =>
      intro slot inside
      cases flag : before.expandable slot with
      | false => rfl
      | true =>
          have member : slot ∈ EnumerationIndexSelection.candidates before :=
            List.mem_filter.mpr ⟨List.mem_range.mpr inside, flag⟩
          simp only [seen, List.not_mem_nil] at member
  | cons first rest =>
      have scan : EnumerationPureSelection.find before =
          some ((first :: rest).filter fun slot => (before.waiting slot).isNone) := by
        simp only [EnumerationPureSelection.find, seen, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
      change pickNext (fun _ => none) (EnumerationPureSelection.find before) = .done at finished
      rw [scan] at finished
      cases filtered : (first :: rest).filter (fun slot => (before.waiting slot).isNone) <;>
        simp [filtered, pickNext] at finished

private theorem stored_carrier (before : State Symbol EnumGuard) (safe : Safe before)
    (uv root size : Nat) (value : UVarValue Symbol) (carried : CarriesGraph before uv)
    (path : UnionFind.Reaches before.representatives uv root size)
    (stored : before.values[root]? = some value) : GraphValue value := by
  obtain ⟨held, storedValue, related, heldStored, bearing⟩ := carried
  have live : storedValue ≠ .eliminated := by cases storedValue <;> simp_all [GraphValue]
  obtain ⟨heldSize, heldPath⟩ := (safe.2 held storedValue heldStored).mp live
  have same : root = held := (UnionFind.sameClass_iff_roots path heldPath).mp related
  subst root
  have sameValue : storedValue = value := Option.some.inj (heldStored.symm.trans stored)
  simpa only [sameValue] using bearing

private theorem fragment_complete (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (marker : Symbol) (level : Nat → Nat) (frontier : Nat) (fragment : Fragment Symbol)
    (before : State Symbol EnumGuard) (safe : Safe before)
    (ordered : Stratified before level frontier) (references : ReferencesCarry before)
    (inputBoundary : Opaque heap before) (carried : FragmentCarries before fragment) :
    ∃ fuel term after,
      Success (SourcePruningEnumerationRendering.expandFragment heap marker fuel fragment) before term after ∧
      RenderStable before after ∧ Frame before after := by
  have construct : ∀ depth, ∀ fragment (before : State Symbol EnumGuard), Safe before →
      Stratified before level frontier → ReferencesCarry before → Opaque heap before →
      FragmentCarries before fragment →
      (∀ uv, HasHole fragment uv → frontier - level uv < depth) →
      ∃ fuel term after,
        Success (SourcePruningEnumerationRendering.expandFragment heap marker fuel fragment) before term after ∧
        RenderStable before after ∧ Frame before after := by
    intro depth
    induction depth using Nat.strongRecOn with
    | ind depth ih =>
        intro fragment
        induction fragment using Fragment.rec
          (motive_2 := fun fragments => ∀ (before : State Symbol EnumGuard), Safe before →
            Stratified before level frontier → ReferencesCarry before → Opaque heap before →
            (∀ fragment ∈ fragments, FragmentCarries before fragment) →
            (∀ fragment ∈ fragments, ∀ uv, HasHole fragment uv → frontier - level uv < depth) →
            ∃ fuel terms after,
              Success (fragments.mapM (SourcePruningEnumerationRendering.expandFragment heap marker fuel)) before terms after ∧
              RenderStable before after ∧ Frame before after) with
        | hole uv =>
            intro before safe ordered references inputBoundary carried bounded
            have small := bounded uv (.hole uv)
            have carrier := carried uv (.hole uv)
            obtain ⟨readFuel, root, value, resolved, reading, readStable, stored, size, path⟩ :=
              EnumerationPartialCompletion.getValue_complete before safe uv (carrier_inside before safe uv carrier)
            have bearing := stored_carrier before safe uv root size value carrier path stored
            have readFrame := (getValue_frame readFuel uv before resolved value safe.1.total reading).1
            have readingAt : ∀ fuel, readFuel ≤ fuel → Success (getValue fuel uv) before value resolved := by
              intro fuel enough
              obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le enough
              exact EnumerationExecution.getValue_moreFuel readFuel extra uv before value resolved reading
            cases value with
            | eliminated => cases bearing
            | enumerated storedFragment =>
                have sameLevel := ordered.classes uv root (UnionFind.sameClass_root path)
                obtain ⟨rootBound, dependencies⟩ := ordered.expanded root storedFragment stored
                have storedBound : ∀ child, HasHole storedFragment child →
                    frontier - level child < frontier - level uv := by
                  intro child hole
                  have higher := dependencies child hole
                  omega
                obtain ⟨renderFuel, term, after, rendering, renderedStable, renderedFrame⟩ :=
                  ih (frontier - level uv) small storedFragment resolved readStable.safe
                    (stratified_read before resolved level frontier readStable ordered)
                    (references_read before resolved readStable references)
                    (opaque_read heap before resolved inputBoundary readStable)
                    ((references.1 root storedFragment stored).preserve storedFragment
                      (carriers_read before resolved readStable)) storedBound
                let fuel := readFuel + renderFuel
                refine ⟨fuel + 1, term, after, ?_, readStable.trans renderedStable, readFrame.trans renderedFrame⟩
                apply (success_bind _ _ _ _ _).mpr
                refine ⟨.enumerated storedFragment, resolved, readingAt (fuel + 1) (by dsimp [fuel]; omega), ?_⟩
                simpa only [fuel, Nat.add_comm] using
                  SourcePruningEnumerationRendering.expandFragment_moreFuel heap marker renderFuel readFuel
                    storedFragment resolved term after rendering
            | unenumerated node scs =>
                cases node with
                | none => cases bearing
                | some handle =>
                    obtain ⟨decoded, lookup, boundary, _emptyBucket⟩ := inputBoundary root handle scs stored
                    refine ⟨readFuel + 1, .node marker [], resolved, ?_, readStable, readFrame⟩
                    apply (success_bind _ _ _ _ _).mpr
                    refine ⟨.unenumerated (some handle) scs, resolved,
                      readingAt (readFuel + 1) (by omega), ?_⟩
                    simpa only [lookup, boundary, ↓reduceIte] using
                      (success_pure (Term.node marker []) (Term.node marker []) resolved resolved).mpr ⟨rfl, rfl⟩
        | node symbol children childIH =>
            intro before safe ordered references inputBoundary carried bounded
            obtain ⟨fuel, terms, after, traversal, stable, frame⟩ :=
              childIH before safe ordered references inputBoundary
                (fun child member uv hole => carried uv (.child symbol children child uv member hole))
                (fun child member uv hole => bounded uv (.child symbol children child uv member hole))
            exact ⟨fuel + 1, .node symbol terms, after,
              (success_bind _ _ _ _ _).mpr ⟨terms, after, traversal,
                (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩, stable, frame⟩
        | nil =>
            rename_i before safe ordered references inputBoundary carried bounded
            exact ⟨0, [], before, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩, .refl before safe, .refl before⟩
        | cons child children childIH childrenIH =>
            rename_i before safe ordered references inputBoundary carried bounded
            obtain ⟨firstFuel, term, middle, first, firstStable, firstFrame⟩ :=
              childIH before safe ordered references inputBoundary (carried child (by simp)) (bounded child (by simp))
            obtain ⟨restFuel, terms, after, continued, lastStable, lastFrame⟩ :=
              childrenIH middle firstStable.safe
                (stratified_read before middle level frontier firstStable ordered)
                (references_read before middle firstStable references)
                (opaque_read heap before middle inputBoundary firstStable)
                (fun fragment member => (carried fragment (by simp [member])).preserve fragment
                  (carriers_read before middle firstStable))
                (fun fragment member => bounded fragment (by simp [member]))
            refine ⟨firstFuel + restFuel, term :: terms, after, ?_, firstStable.trans lastStable, firstFrame.trans lastFrame⟩
            rw [List.mapM_cons]
            apply (success_bind _ _ _ _ _).mpr
            refine ⟨term, middle, SourcePruningEnumerationRendering.expandFragment_moreFuel heap marker
              firstFuel restFuel child before term middle first, ?_⟩
            apply (success_bind _ _ _ _ _).mpr
            refine ⟨terms, after, ?_, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩
            have more := retains_mapM _ _
              (fun fragment => SourcePruningEnumerationRendering.expandFragment_moreFuel heap marker restFuel firstFuel fragment)
              children middle terms after continued
            simpa only [Nat.add_comm] using more
  exact construct (frontier + 1) fragment before safe ordered references inputBoundary carried (by intro uv _; omega)

private theorem root_complete (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (marker : Symbol) (level : Nat → Nat) (frontier uv : Nat) (before : State Symbol EnumGuard)
    (safe : Safe before) (ordered : Stratified before level frontier)
    (references : ReferencesCarry before) (inputBoundary : Opaque heap before)
    (carried : CarriesGraph before uv) (inside : uv < before.counter) :
    ∃ fuel term after,
      Success (SourcePruningEnumerationRendering.expandUVar heap marker fuel uv) before term after ∧
      RenderStable before after ∧ Frame before after := by
  obtain ⟨readFuel, root, value, middle, reading, readStable, stored, size, path⟩ :=
    EnumerationPartialCompletion.getValue_complete before safe uv inside
  have bearing := stored_carrier before safe uv root size value carried path stored
  have readFrame := (getValue_frame readFuel uv before middle value safe.1.total reading).1
  have readingAt : ∀ fuel, readFuel ≤ fuel → Success (getValue fuel uv) before value middle := by
    intro fuel enough
    obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le enough
    exact EnumerationExecution.getValue_moreFuel readFuel extra uv before value middle reading
  cases value with
  | eliminated => cases bearing
  | enumerated fragment =>
      obtain ⟨renderFuel, term, after, rendering, stable, frame⟩ :=
        fragment_complete heap marker level frontier fragment middle readStable.safe
          (stratified_read before middle level frontier readStable ordered)
          (references_read before middle readStable references)
          (opaque_read heap before middle inputBoundary readStable)
          ((references.1 root fragment stored).preserve fragment (carriers_read before middle readStable))
      let fuel := readFuel + renderFuel
      refine ⟨fuel, term, after, ?_, readStable.trans stable, readFrame.trans frame⟩
      apply (success_bind _ _ _ _ _).mpr
      refine ⟨.enumerated fragment, middle, readingAt (fuel + 1) (by dsimp [fuel]; omega), ?_⟩
      simpa only [fuel, Nat.add_comm] using
        SourcePruningEnumerationRendering.expandFragment_moreFuel heap marker renderFuel readFuel fragment middle term after rendering
  | unenumerated node scs =>
      cases node with
      | none => cases bearing
      | some handle =>
          obtain ⟨decoded, lookup, boundary, _emptyBucket⟩ := inputBoundary root handle scs stored
          refine ⟨readFuel, .node marker [], middle, ?_, readStable, readFrame⟩
          apply (success_bind _ _ _ _ _).mpr
          refine ⟨.unenumerated (some handle) scs, middle, readingAt (readFuel + 1) (by omega), ?_⟩
          simpa only [lookup, boundary, ↓reduceIte] using
            (success_pure (Term.node marker []) (Term.node marker []) middle middle).mpr ⟨rfl, rfl⟩

private theorem pending_complete (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (marker : Symbol) (level : Nat → Nat) (frontier : Nat) (inputs : List (EnumGuard × Fragment Symbol))
    (before : State Symbol EnumGuard) (safe : Safe before) (ordered : Stratified before level frontier)
    (references : ReferencesCarry before) (inputBoundary : Opaque heap before)
    (carried : ∀ input ∈ inputs, FragmentCarries before input.2) :
    ∃ fuel pending after,
      Success (inputs.mapM fun input => do
        pure (input.1, ← SourcePruningEnumerationRendering.expandFragment heap marker fuel input.2)) before pending after ∧
      RenderStable before after ∧ Frame before after := by
  induction inputs generalizing before with
  | nil => exact ⟨0, [], before, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩, .refl before safe, .refl before⟩
  | cons input rest ih =>
      obtain ⟨firstFuel, term, middle, first, firstStable, firstFrame⟩ :=
        fragment_complete heap marker level frontier input.2 before safe ordered references inputBoundary (carried input (by simp))
      obtain ⟨restFuel, pending, after, continued, lastStable, lastFrame⟩ :=
        ih middle firstStable.safe (stratified_read before middle level frontier firstStable ordered)
          (references_read before middle firstStable references) (opaque_read heap before middle inputBoundary firstStable)
          (fun input member => (carried input (by simp [member])).preserve input.2 (carriers_read before middle firstStable))
      let fuel := firstFuel + restFuel
      refine ⟨fuel, (input.1, term) :: pending, after, ?_, firstStable.trans lastStable, firstFrame.trans lastFrame⟩
      rw [List.mapM_cons]
      apply (success_bind _ _ _ _ _).mpr
      refine ⟨(input.1, term), middle, ?_, ?_⟩
      · exact (success_bind _ _ _ _ _).mpr
          ⟨term, middle, SourcePruningEnumerationRendering.expandFragment_moreFuel heap marker firstFuel restFuel
            input.2 before term middle first, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩
      · apply (success_bind _ _ _ _ _).mpr
        refine ⟨pending, after, ?_, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩
        have more := retains_mapM _ _ (fun (input : EnumGuard × Fragment Symbol) =>
          retains_bind _ _ _ _ (SourcePruningEnumerationRendering.expandFragment_moreFuel heap marker restFuel firstFuel input.2)
            (fun _ => retains_refl _)) rest middle pending after continued
        simpa only [fuel, Nat.add_comm] using more

variable {Typing : Type} {width : Nat}
variable [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)]

/-- A current finished native cache renders one exact marker result at every larger bound. -/
theorem default_finished_render
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {caller : SourceCurrentAllocatedPartialState.State width} {memos : EndpointMemoGateTrace.Memos}
    {metadata : SourcePruningRecordTypes.Metadata Typing}
    {before : EnumerationExpandableIndex.Cached Symbol Constraint}
    (packet : SourcePruningEnumerationRecursive.Packet formulas solver inventory caller memos metadata before)
    (canonical : EnumerationValidity.Canonical before.core) (references : ReferencesCarry before.core)
    (root : CarriesGraph before.core 0) (inside : 0 < before.core.counter)
    (finished : EnumerationPureSelection.next (fun _ => none) before = .done) (marker : Symbol) :
    ∃ bound term pending after,
      (∀ extra, Success (SourcePruningEnumerationRendering.render caller.checked.native.machine.heap
        marker (bound + extra) 0) before.core (term, pending) after) ∧
      RenderStable before.core after ∧ Frame before.core after ∧ EnumerationValidity.Canonical after := by
  obtain ⟨_roots, _paths, _storage, realized, _waiting, flags⟩ := packet.valid
  have inactive := flags_false before finished
  have inputBoundary : Opaque caller.checked.native.machine.heap before.core := by
    intro slot handle scs stored
    have allocated : slot < before.core.counter := by
      rw [packet.safe.1.aligned]
      exact (List.getElem?_eq_some_iff.mp stored).1
    have candidate : SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
        (.unenumerated (some handle) scs) = some false := by
      simpa only [stored, Option.getD_some, inactive slot allocated] using flags slot
    obtain ⟨value, decoded, _available, _closed⟩ := realized slot handle scs stored
    cases scs with
    | cons first rest => simp [SourcePruningEnumerationNativeIndex.candidate, decoded] at candidate
    | nil =>
        refine ⟨value, decoded, ?_, rfl⟩
        cases boundary : MergedOrdinaryHeight.recursiveBoundary value with
        | false => simp [SourcePruningEnumerationNativeIndex.candidate, decoded, boundary] at candidate
        | true => rfl
  obtain ⟨level, frontier, ordered⟩ := packet.ordered
  obtain ⟨rootFuel, term, middle, rootRun, rootStable, rootFrame⟩ :=
    root_complete caller.checked.native.machine.heap marker level frontier 0 before.core
      packet.safe ordered references inputBoundary root inside
  have middleReferences := references_read before.core middle rootStable references
  obtain ⟨pendingFuel, pending, after, pendingRun, pendingStable, pendingFrame⟩ :=
    pending_complete caller.checked.native.machine.heap marker level frontier middle.obligations middle
      rootStable.safe (stratified_read before.core middle level frontier rootStable ordered)
      middleReferences (opaque_read caller.checked.native.machine.heap before.core middle inputBoundary rootStable) middleReferences.2
  let bound := rootFuel + pendingFuel
  have actual : Success (SourcePruningEnumerationRendering.render caller.checked.native.machine.heap marker bound 0)
      before.core (term, pending) after := by
    unfold SourcePruningEnumerationRendering.render
    apply (success_bind _ _ _ _ _).mpr
    refine ⟨term, middle, SourcePruningEnumerationRendering.expandUVar_moreFuel caller.checked.native.machine.heap
      marker rootFuel pendingFuel 0 before.core term middle rootRun, ?_⟩
    apply (success_bind _ _ _ _ _).mpr
    refine ⟨middle, middle, (get_success _ _ _).mpr ⟨rfl, rfl⟩, ?_⟩
    apply (success_bind _ _ _ _ _).mpr
    refine ⟨pending, after, ?_, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩
    have more := retains_mapM _ _ (fun (input : Constraint × Fragment Symbol) =>
      retains_bind _ _ _ _ (SourcePruningEnumerationRendering.expandFragment_moreFuel caller.checked.native.machine.heap
        marker pendingFuel rootFuel input.2) (fun _ => retains_refl _))
      middle.obligations middle pending after pendingRun
    simpa only [bound, Nat.add_comm] using more
  have stable := rootStable.trans pendingStable
  refine ⟨bound, term, pending, after, ?_, stable, rootFrame.trans pendingFrame, ?_⟩
  · intro extra
    exact SourcePruningEnumerationRendering.render_moreFuel caller.checked.native.machine.heap marker bound extra 0
      before.core (term, pending) after actual
  · intro value member
    exact canonical value (by simpa only [stable.values] using member)

end MicroCFTA.SourcePruningEnumerationDefaultFinishedRendering
