import MicroCFTA.SourcePruningEnumerationSharedPreparedPartialOutput
import MicroCFTA.SourcePruningEnumerationDefaultPartialAgreement
import MicroCFTA.EnumerationPartialBounds

/-!
# The same prepared output with default concrete and tagged observations

The agreement producer runs once at the current output packet.
The actual tagged root supplies its exact receipt and conditional completion observer.
Native resources and complete memos keep their original witnesses.
Each root and residual observation retains its own compression endpoint.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule
open EnumerationDriver EnumerationCompressionFrame EnumerationOrder EnumerationExecution EnumerationObservations
open SourcePruningEnumerationNodes
open InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed)
open SourcePruningEnumerationRecursive (Packet callback_frame)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "PartialTerm" => SourcePruningTemplates.PartialTerm
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {NativeGuard EnumGuard : Type}
attribute [local instance] EnumerationObservations.partialTransportMonadList
  EnumerationObservations.partialTransportLawfulMonadList

private theorem marker_root_read_exact (fuel : Nat) (before after : EnumerationState.State Symbol EnumGuard)
    (fragment : Fragment Symbol) (actual : Success (EnumerationUntil.rootFragment fuel) before fragment after) :
    ExceptT.run (EnumerationUntil.rootFragment fuel before) = [.ok (fragment, after)] := by
  obtain ⟨value, reading, projected⟩ := (rootFragment_success fuel before after fragment).mp actual
  unfold EnumerationUntil.rootFragment
  rw [bind_single _ _ _ _ _ (EnumerationPartialExact.getValue_exact (fuel + 1) 0 before after value reading)]
  cases value <;> cases projected <;> rfl

private theorem marker_root_exact (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel : Nat) (before after : EnumerationState.State Symbol EnumGuard) (observedTerm : PartialTerm)
    (actual : Success (SourcePruningEnumerationPartialOutput.rootPartial heap fuel) before observedTerm after) :
    ExceptT.run (SourcePruningEnumerationPartialOutput.rootPartial heap fuel before) = [.ok (observedTerm, after)] := by
  unfold SourcePruningEnumerationPartialOutput.rootPartial at actual ⊢
  obtain ⟨fragment, middle, rootRead, rendered⟩ := (success_bind _ _ _ _ _).mp actual
  rw [bind_single _ _ _ _ _ (marker_root_read_exact fuel before middle fragment rootRead)]
  unfold SourcePruningEnumerationPartialOutput.expandPartial at rendered ⊢
  exact EnumerationPartialExact.expandPartial_exact _ fuel fragment middle after observedTerm rendered

private theorem marker_root_stable (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel : Nat) (before after : EnumerationState.State Symbol EnumGuard) (observedTerm : PartialTerm)
    (safe : Safe before) (inside : 0 < before.counter)
    (actual : Success (SourcePruningEnumerationPartialOutput.rootPartial heap fuel) before observedTerm after) :
    RenderStable before after := by
  unfold SourcePruningEnumerationPartialOutput.rootPartial at actual
  obtain ⟨fragment, middle, rootRead, rendered⟩ := (success_bind _ _ _ _ _).mp actual
  obtain ⟨value, reading, projected⟩ := (rootFragment_success fuel before middle fragment).mp rootRead
  obtain ⟨readStable, bounded⟩ := getValue_storage (fuel + 1) 0 before middle value safe inside reading
  have allocated : FragmentBound middle.counter fragment := by
    cases value with
    | enumerated stored =>
        rw [projected]
        exact bounded
    | eliminated | unenumerated _ _ =>
        rw [projected]
        change 0 < middle.counter
        rw [readStable.counter]
        exact inside
  unfold SourcePruningEnumerationPartialOutput.expandPartial at rendered
  have renderStable := (EnumerationPartialBounds.expandPartial_bounded _ fuel fragment middle after observedTerm
    readStable.safe allocated rendered).1
  exact readStable.trans renderStable

private theorem marker_root_completes (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (language : NodeLanguage Symbol) (meaning : EnumGuard → Term Symbol → Prop) (assignment : Nat → Term Symbol)
    (fuel : Nat) (before after : EnumerationState.State Symbol EnumGuard) (observedTerm : PartialTerm)
    (total : UnionFind.Total before.representatives) (satisfied : Satisfies language meaning assignment before)
    (actual : Success (SourcePruningEnumerationPartialOutput.rootPartial heap fuel) before observedTerm after) :
    SourcePruningPartialMatch.Completes assignment observedTerm (assignment 0) := by
  unfold SourcePruningEnumerationPartialOutput.rootPartial at actual
  obtain ⟨fragment, middle, rootRead, rendered⟩ := (success_bind _ _ _ _ _).mp actual
  have frame := rootFragment_frame fuel before middle fragment total rootRead
  have middleModel := (SourcePruningEnumerationNativeLanguage.satisfies_frame
    language meaning assignment before middle frame).mpr satisfied
  unfold SourcePruningEnumerationPartialOutput.expandPartial at rendered
  have completed := SourcePruningPartialRenderingSemantics.expandPartial_completes _
    language meaning assignment fuel fragment middle after observedTerm (frame.total total) middleModel rendered
  have rootFilled : fill assignment fragment = assignment 0 := by
    obtain ⟨value, reading, projected⟩ := (rootFragment_success fuel before middle fragment).mp rootRead
    obtain ⟨_readFrame, root, _size, path, _afterPath, stored⟩ :=
      getValue_frame (fuel + 1) 0 before middle value total reading
    cases value with
    | eliminated | unenumerated _ _ => simp only [projected, fill]
    | enumerated storedFragment =>
        rw [projected]
        have rootEquation : fill assignment storedFragment = assignment root := by
          simpa only [EnumerationCorrectness.heap, stored, Option.getD_some, slot, slotSatisfies]
            using satisfied.1.2 root
        exact rootEquation.trans (satisfied.1.1 0 root (UnionFind.sameClass_root path)).symm
  rw [rootFilled] at completed
  exact completed

private theorem marker_root_observed (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel : Nat) (before after : EnumerationState.State Symbol EnumGuard) (observedTerm : PartialTerm)
    (safe : Safe before) (inside : 0 < before.counter)
    (actual : Success (SourcePruningEnumerationPartialOutput.rootPartial heap fuel) before observedTerm after) :
    (∀ extra,
      Success (SourcePruningEnumerationPartialOutput.rootPartial heap (fuel + extra)) before observedTerm after ∧
      ExceptT.run (SourcePruningEnumerationPartialOutput.rootPartial heap (fuel + extra) before) = [.ok (observedTerm, after)]) ∧
    RenderStable before after ∧ Frame before after ∧
    ∀ (language : NodeLanguage Symbol) (meaning : EnumGuard → Term Symbol → Prop) (assignment : Nat → Term Symbol),
      Satisfies language meaning assignment before →
      Satisfies language meaning assignment after ∧ SourcePruningPartialMatch.Completes assignment observedTerm (assignment 0) := by
  have frame : Frame before after := by
    unfold SourcePruningEnumerationPartialOutput.rootPartial SourcePruningEnumerationPartialOutput.expandPartial at actual
    exact EnumerationObservations.rootPartial_frame _ fuel before after observedTerm safe.1.total actual
  refine ⟨?_, marker_root_stable heap fuel before after observedTerm safe inside actual, frame, ?_⟩
  · intro extra
    have raised : Success (SourcePruningEnumerationPartialOutput.rootPartial heap (fuel + extra)) before observedTerm after := by
      unfold SourcePruningEnumerationPartialOutput.rootPartial SourcePruningEnumerationPartialOutput.expandPartial at actual ⊢
      exact EnumerationObservations.rootPartial_moreFuel _ fuel extra before observedTerm after actual
    exact ⟨raised, marker_root_exact heap (fuel + extra) before after observedTerm raised⟩
  · intro language meaning assignment satisfied
    exact ⟨(SourcePruningEnumerationNativeLanguage.satisfies_frame language meaning assignment before after frame).mpr satisfied,
      marker_root_completes heap language meaning assignment fuel before after observedTerm safe.1.total satisfied actual⟩

variable {Typing : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]
variable {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {original : Caller width} {seed : Seed} {output : Output width Typing}

/-- One current prepared output retains its resources, marker agreement and original conditional completions. -/
theorem OutputResources.default_finished_render_partial_models
    (resources : OutputResources formulas solver original seed output)
    (canonical : EnumerationValidity.Canonical output.cache.core)
    (references : EnumerationGraphReferences.ReferencesCarry output.cache.core)
    (root : EnumerationCarriers.CarriesGraph output.cache.core 0) (inside : 0 < output.cache.core.counter)
    (finished : EnumerationPureSelection.next (fun _ => none) output.cache = .done) :
    ∃ (next : Inventory) (final : Memos) (metadata : Metadata Typing),
      Post formulas solver next original output.caller final ∧ final.query = output.queries ∧
      Packet formulas solver next output.caller final metadata output.cache ∧
      (output.metadata = none ∨ output.metadata = some metadata) ∧
      Fits seed.2 output.caller.checked ∧ Heap (fun guard => guard ∈ seed.1) output.caller.checked.native.machine.heap ∧
      ∃ (level : Nat → Nat) (frontier : Nat), Stratified output.cache.core level frontier ∧
      let heap := output.caller.checked.native.machine.heap
      let tagged := fun fuel => do
        let rootTerm ← SourcePruningEnumerationPartialOutput.rootPartial (EnumGuard := Constraint) heap fuel
        let attached ← (← get).obligations.mapM fun obligation => do
          pure (obligation.1, ← SourcePruningEnumerationPartialOutput.expandPartial heap fuel obligation.2)
        pure (rootTerm, attached)
      ∃ bound term pending concreteAfter partialRoot partialPending partialAfter rootAfter,
        (∀ extra,
          Success (SourcePruningEnumerationRendering.render heap ("Mu", FullSyntax.Formula.top) (bound + extra) 0)
            output.cache.core (term, pending) concreteAfter ∧
          Success (tagged (bound + extra)) output.cache.core (partialRoot, partialPending) partialAfter) ∧
        RenderStable output.cache.core concreteAfter ∧ Frame output.cache.core concreteAfter ∧
        EnumerationValidity.Canonical concreteAfter ∧
        RenderStable output.cache.core partialAfter ∧ Frame output.cache.core partialAfter ∧
        term = SourcePruningPositions.openProgram true partialRoot ∧
        pending = partialPending.map (fun attachment => (attachment.1, SourcePruningPositions.openProgram true attachment.2)) ∧
        (∀ extra,
          Success (SourcePruningEnumerationPartialOutput.rootPartial heap (bound + extra)) output.cache.core partialRoot rootAfter ∧
          ExceptT.run (SourcePruningEnumerationPartialOutput.rootPartial heap (bound + extra) output.cache.core) = [.ok (partialRoot, rootAfter)]) ∧
        RenderStable output.cache.core rootAfter ∧ Frame output.cache.core rootAfter ∧ Stratified rootAfter level frontier ∧
        Packet formulas solver next output.caller final metadata (EnumerationExpandableIndex.frame rootAfter output.cache) ∧
        Stratified concreteAfter level frontier ∧ Stratified partialAfter level frontier ∧
        Packet formulas solver next output.caller final metadata (EnumerationExpandableIndex.frame concreteAfter output.cache) ∧
        Packet formulas solver next output.caller final metadata (EnumerationExpandableIndex.frame partialAfter output.cache) ∧
        ∀ (language : NodeLanguage Symbol) (meaning : Constraint → Term Symbol → Prop) (assignment : Nat → Term Symbol),
          Satisfies language meaning assignment output.cache.core →
          Satisfies language meaning assignment rootAfter ∧ Satisfies language meaning assignment concreteAfter ∧
          Satisfies language meaning assignment partialAfter ∧ SourcePruningPartialMatch.Completes assignment partialRoot (assignment 0) := by
  obtain ⟨next, final, metadata, post, querySame, packet, metadataSame, fits, known⟩ := resources
  obtain ⟨level, frontier, ordered⟩ := packet.ordered
  let heap := output.caller.checked.native.machine.heap
  let tagged : Nat → EnumerateM Symbol Constraint (PartialTerm × List (Constraint × PartialTerm)) := fun fuel => do
    let rootTerm ← SourcePruningEnumerationPartialOutput.rootPartial (EnumGuard := Constraint) heap fuel
    let attached ← (← get).obligations.mapM fun obligation => do
      pure (obligation.1, ← SourcePruningEnumerationPartialOutput.expandPartial heap fuel obligation.2)
    pure (rootTerm, attached)
  obtain ⟨bound, term, pending, concreteAfter, partialRoot, partialPending, partialAfter,
      actual, concreteStable, concreteFrame, concreteCanonical, partialStable, partialFrame, rootSame, pendingSame⟩ :=
    SourcePruningEnumerationDefaultPartialAgreement.default_finished_render_partial packet canonical references root inside finished
  have baseTagged := (actual 0).2
  change Success (tagged (bound + 0)) output.cache.core (partialRoot, partialPending) partialAfter at baseTagged
  dsimp only [tagged] at baseTagged
  obtain ⟨observedRoot, rootAfter, rootActual, continued⟩ := (success_bind _ _ _ _ _).mp baseTagged
  obtain ⟨readState, readAfter, getting, traversed⟩ := (success_bind _ _ _ _ _).mp continued
  obtain ⟨sameState, sameAfter⟩ := (get_success _ _ _).mp getting
  subst readState
  subst readAfter
  obtain ⟨observedPending, last, _remaining, paired⟩ := (success_bind _ _ _ _ _).mp traversed
  obtain ⟨sameOutput, _sameEndpoint⟩ :=
    (success_pure (observedRoot, observedPending) (partialRoot, partialPending) last partialAfter).mp paired
  have sameRoot : observedRoot = partialRoot := congrArg Prod.fst sameOutput.symm
  subst observedRoot
  obtain ⟨rootRuns, rootStable, rootFrame, rootModels⟩ :=
    marker_root_observed heap bound output.cache.core rootAfter partialRoot packet.safe inside rootActual
  have rootOrdered := stratified_read output.cache.core rootAfter level frontier rootStable ordered
  have concreteOrdered := stratified_read output.cache.core concreteAfter level frontier concreteStable ordered
  have partialOrdered := stratified_read output.cache.core partialAfter level frontier partialStable ordered
  have rootPacket : Packet formulas solver next output.caller final metadata (EnumerationExpandableIndex.frame rootAfter output.cache) := by
    apply callback_frame packet metadata rootAfter rootStable.safe rootFrame ⟨level, frontier, rootOrdered⟩
    intro group member entry listed
    rw [rootFrame.counter]
    exact packet.bounded group member entry listed
  have concretePacket : Packet formulas solver next output.caller final metadata (EnumerationExpandableIndex.frame concreteAfter output.cache) := by
    apply callback_frame packet metadata concreteAfter concreteStable.safe concreteFrame ⟨level, frontier, concreteOrdered⟩
    intro group member entry listed
    rw [concreteFrame.counter]
    exact packet.bounded group member entry listed
  have partialPacket : Packet formulas solver next output.caller final metadata (EnumerationExpandableIndex.frame partialAfter output.cache) := by
    apply callback_frame packet metadata partialAfter partialStable.safe partialFrame ⟨level, frontier, partialOrdered⟩
    intro group member entry listed
    rw [partialFrame.counter]
    exact packet.bounded group member entry listed
  refine ⟨next, final, metadata, post, querySame, packet, metadataSame, fits, known,
    level, frontier, ordered, bound, term, pending, concreteAfter, partialRoot, partialPending, partialAfter, rootAfter,
    actual, concreteStable, concreteFrame, concreteCanonical, partialStable, partialFrame, rootSame, pendingSame,
    rootRuns, rootStable, rootFrame, rootOrdered, rootPacket, concreteOrdered, partialOrdered, concretePacket, partialPacket, ?_⟩
  intro language meaning assignment satisfied
  have completed := rootModels language meaning assignment satisfied
  exact ⟨completed.1,
    (SourcePruningEnumerationNativeLanguage.satisfies_frame language meaning assignment output.cache.core concreteAfter concreteFrame).mpr satisfied,
    (SourcePruningEnumerationNativeLanguage.satisfies_frame language meaning assignment output.cache.core partialAfter partialFrame).mpr satisfied,
    completed.2⟩

end MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive
