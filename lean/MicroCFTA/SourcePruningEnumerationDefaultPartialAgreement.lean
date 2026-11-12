import MicroCFTA.SourcePruningEnumerationDefaultFinishedRendering
import MicroCFTA.SourcePruningEnumerationPartialOutput
import MicroCFTA.SourcePruningPositions

/-!
# Default Mu rendering and the actual tagged observations

Both observations read the same current finished packet.
The existing openProgram projection relates their root and ordered residual syntax.
Each observation keeps its own exact compression endpoint.
The statement does not supply a ground completion below a marker.
-/
namespace MicroCFTA.SourcePruningEnumerationDefaultPartialAgreement
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule
open EnumerationDriver EnumerationCompressionFrame EnumerationOrder EnumerationExecution
open EnumerationCarriers EnumerationGraphReferences EnumerationRenderability EnumerationObservations
open SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "PartialTerm" => SourcePruningTemplates.PartialTerm
variable {NativeGuard EnumGuard : Type}
attribute [local instance] EnumerationObservations.partialTransportMonadList
  EnumerationObservations.partialTransportLawfulMonadList

private def marker : Symbol := ("Mu", FullSyntax.Formula.top)

private def Opaque (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (state : State Symbol EnumGuard) : Prop :=
  ∀ (slot handle : Nat) (scs : List Suspended),
    state.values[slot]? = some (UVarValue.unenumerated (some handle) scs) →
    ∃ value, lookupNode heap handle = some value ∧
      MergedOrdinaryHeight.recursiveBoundary value = true ∧ scs = []

private theorem opaque_frame (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before after : State Symbol EnumGuard) (inputBoundary : Opaque heap before)
    (frame : Frame before after) : Opaque heap after := by
  intro slot handle scs stored
  exact inputBoundary slot handle scs (by simpa only [frame.values] using stored)

private theorem partial_frame (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel : Nat) (fragment : Fragment Symbol) (before after : State Symbol EnumGuard)
    (term : PartialTerm) (total : UnionFind.Total before.representatives)
    (actual : Success (SourcePruningEnumerationPartialOutput.expandPartial heap fuel fragment) before term after) :
    Frame before after := by
  unfold SourcePruningEnumerationPartialOutput.expandPartial at actual
  exact EnumerationObservations.expandPartial_frame _ fuel fragment before after term total actual

private theorem fragment_agrees (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (leftFuel rightFuel : Nat) :
    ∀ fragment (left right leftAfter rightAfter : State Symbol EnumGuard) (term : Term Symbol) (taggedTerm : PartialTerm),
      Frame left right → UnionFind.Total left.representatives → Opaque heap left →
      Success (SourcePruningEnumerationRendering.expandFragment heap marker leftFuel fragment) left term leftAfter →
      Success (SourcePruningEnumerationPartialOutput.expandPartial heap rightFuel fragment) right taggedTerm rightAfter →
      Frame leftAfter rightAfter ∧ term = SourcePruningPositions.openProgram true taggedTerm := by
  induction leftFuel generalizing rightFuel with
  | zero =>
      intro fragment left right leftAfter rightAfter term taggedTerm frame total inputBoundary concrete tagged
      exact (success_failure .fuelExhausted left leftAfter term concrete).elim
  | succ leftFuel ih =>
      intro fragment left right leftAfter rightAfter term taggedTerm frame total inputBoundary concrete tagged
      cases rightFuel with
      | zero => exact (success_failure .fuelExhausted right rightAfter taggedTerm tagged).elim
      | succ rightFuel =>
          cases fragment with
          | node symbol children =>
              change Success (children.mapM (SourcePruningEnumerationRendering.expandFragment heap marker leftFuel) >>=
                fun terms => pure (.node symbol terms)) left term leftAfter at concrete
              change Success (children.mapM (SourcePruningEnumerationPartialOutput.expandPartial heap rightFuel) >>=
                fun terms => pure (.node (.concrete symbol) terms)) right taggedTerm rightAfter at tagged
              obtain ⟨terms, middle, traversed, final⟩ := (success_bind _ _ _ _ _).mp concrete
              obtain ⟨partials, reached, observed, finished⟩ := (success_bind _ _ _ _ _).mp tagged
              have lists : ∀ (inputs : List (Fragment Symbol)) (left right leftAfter rightAfter : State Symbol EnumGuard)
                  (terms : List (Term Symbol)) (partials : List PartialTerm),
                  Frame left right → UnionFind.Total left.representatives → Opaque heap left →
                  Success (inputs.mapM (SourcePruningEnumerationRendering.expandFragment heap marker leftFuel)) left terms leftAfter →
                  Success (inputs.mapM (SourcePruningEnumerationPartialOutput.expandPartial heap rightFuel)) right partials rightAfter →
                  Frame leftAfter rightAfter ∧ terms = partials.map (SourcePruningPositions.openProgram true) := by
                intro inputs
                induction inputs with
                | nil =>
                    intro left right leftAfter rightAfter terms partials frame total inputBoundary concrete tagged
                    obtain ⟨rfl, rfl⟩ := (success_pure [] terms left leftAfter).mp concrete
                    obtain ⟨rfl, rfl⟩ := (success_pure [] partials right rightAfter).mp tagged
                    exact ⟨frame, rfl⟩
                | cons input rest listIH =>
                    intro left right leftAfter rightAfter terms allPartials frame total inputBoundary concrete tagged
                    rw [List.mapM_cons] at concrete tagged
                    obtain ⟨term, middle, first, continued⟩ := (success_bind _ _ _ _ _).mp concrete
                    obtain ⟨tail, last, remaining, final⟩ := (success_bind _ _ _ _ _).mp continued
                    obtain ⟨taggedTerm, reached, observed, traversed⟩ := (success_bind _ _ _ _ _).mp tagged
                    obtain ⟨partials, endpoint, restObserved, finished⟩ := (success_bind _ _ _ _ _).mp traversed
                    obtain ⟨cross, same⟩ := ih rightFuel input left right middle reached term taggedTerm frame total inputBoundary first observed
                    have rightFrame := partial_frame heap rightFuel input right reached taggedTerm (frame.total total) observed
                    have leftFrame := frame.trans (rightFrame.trans cross.symm)
                    obtain ⟨lastCross, tailsSame⟩ := listIH middle reached last endpoint tail partials cross
                      (leftFrame.total total) (opaque_frame heap left middle inputBoundary leftFrame) remaining restObserved
                    obtain ⟨rfl, rfl⟩ := (success_pure (term :: tail) terms last leftAfter).mp final
                    obtain ⟨rfl, rfl⟩ := (success_pure (taggedTerm :: partials) allPartials endpoint rightAfter).mp finished
                    exact ⟨lastCross, by simp only [List.map_cons, same, tailsSame]⟩
              obtain ⟨cross, same⟩ := lists children left right middle reached terms partials frame total inputBoundary traversed observed
              obtain ⟨rfl, rfl⟩ := (success_pure (.node symbol terms) term middle leftAfter).mp final
              obtain ⟨rfl, rfl⟩ := (success_pure (.node (.concrete symbol) partials) taggedTerm reached rightAfter).mp finished
              exact ⟨cross, by rw [SourcePruningPositions.openProgram_type_node, same]⟩
          | hole uv =>
              change Success (getValue (leftFuel + 1) uv >>= fun value => match value with
                | .enumerated stored => SourcePruningEnumerationRendering.expandFragment heap marker leftFuel stored
                | .unenumerated (some handle) _ => match lookupNode heap handle with
                  | none => failure .unresolvedReference
                  | some value => if MergedOrdinaryHeight.recursiveBoundary value then pure (.node marker []) else failure .unfinishedFragment
                | _ => failure .unfinishedFragment) left term leftAfter at concrete
              rw [SourcePruningEnumerationPartialOutput.expandPartial_hole] at tagged
              obtain ⟨value, middle, reading, continued⟩ := (success_bind _ _ _ _ _).mp concrete
              obtain ⟨partialValue, reached, observing, final⟩ := (success_bind _ _ _ _ _).mp tagged
              obtain ⟨sameValue, cross⟩ := getValue_agrees (leftFuel + 1) (rightFuel + 1) uv
                left right middle reached value partialValue frame total reading observing
              subst partialValue
              have leftFrame := (getValue_frame (leftFuel + 1) uv left middle value total reading).1
              cases value with
              | eliminated => exact (success_failure .unfinishedFragment middle leftAfter term continued).elim
              | enumerated stored =>
                  exact ih rightFuel stored middle reached leftAfter rightAfter term taggedTerm cross
                    (leftFrame.total total) (opaque_frame heap left middle inputBoundary leftFrame) continued final
              | unenumerated node scs =>
                  cases node with
                  | none => exact (success_failure .unfinishedFragment middle leftAfter term continued).elim
                  | some handle =>
                      obtain ⟨_readFrame, root, _size, _path, _afterPath, stored⟩ :=
                        getValue_frame (leftFuel + 1) uv left middle (.unenumerated (some handle) scs) total reading
                      obtain ⟨decoded, lookup, boundary, rfl⟩ := inputBoundary root handle scs stored
                      simp only [lookup, boundary, ↓reduceIte] at continued final
                      obtain ⟨rfl, rfl⟩ := (success_pure (Term.node marker []) term middle leftAfter).mp continued
                      obtain ⟨rfl, rfl⟩ := (success_pure (Term.node (PartialSymbol.truncated : PartialSymbol Symbol) []) taggedTerm reached rightAfter).mp final
                      exact ⟨cross, by rw [SourcePruningPositions.openProgram_truncated]; rfl⟩

private theorem root_agrees (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (leftFuel rightFuel : Nat) (left right leftAfter rightAfter : State Symbol EnumGuard)
    (term : Term Symbol) (taggedTerm : PartialTerm) (frame : Frame left right)
    (total : UnionFind.Total left.representatives) (inputBoundary : Opaque heap left)
    (concrete : Success (SourcePruningEnumerationRendering.expandUVar heap marker leftFuel 0) left term leftAfter)
    (tagged : Success (SourcePruningEnumerationPartialOutput.rootPartial heap rightFuel) right taggedTerm rightAfter) :
    Frame leftAfter rightAfter ∧ term = SourcePruningPositions.openProgram true taggedTerm := by
  obtain ⟨value, middle, reading, continued⟩ := (success_bind _ _ _ _ _).mp concrete
  unfold SourcePruningEnumerationPartialOutput.rootPartial at tagged
  obtain ⟨fragment, reached, rootRead, rendered⟩ := (success_bind _ _ _ _ _).mp tagged
  obtain ⟨rightValue, observing, projected⟩ := (rootFragment_success rightFuel right reached fragment).mp rootRead
  obtain ⟨sameValue, cross⟩ := getValue_agrees (leftFuel + 1) (rightFuel + 1) 0
    left right middle reached value rightValue frame total reading observing
  subst rightValue
  have leftFrame := (getValue_frame (leftFuel + 1) 0 left middle value total reading).1
  have rightFrame := (getValue_frame (rightFuel + 1) 0 right reached value (frame.total total) observing).1
  cases value with
  | eliminated => exact (reject_unsuccessful middle leftAfter term continued).elim
  | enumerated stored =>
      rw [projected] at rendered
      exact fragment_agrees heap leftFuel rightFuel stored middle reached leftAfter rightAfter term taggedTerm cross
        (leftFrame.total total) (opaque_frame heap left middle inputBoundary leftFrame) continued rendered
  | unenumerated node scs =>
      cases node with
      | none => exact (reject_unsuccessful middle leftAfter term continued).elim
      | some handle =>
          obtain ⟨_readFrame, root, _size, _path, _afterPath, stored⟩ :=
            getValue_frame (leftFuel + 1) 0 left middle (.unenumerated (some handle) scs) total reading
          obtain ⟨decoded, lookup, boundary, rfl⟩ := inputBoundary root handle scs stored
          simp only [lookup, boundary, ↓reduceIte] at continued
          obtain ⟨rfl, rfl⟩ := (success_pure (Term.node marker []) term middle leftAfter).mp continued
          rw [projected] at rendered
          cases rightFuel with
          | zero => exact (success_failure .fuelExhausted reached rightAfter taggedTerm rendered).elim
          | succ rightFuel =>
              rw [SourcePruningEnumerationPartialOutput.expandPartial_hole] at rendered
              obtain ⟨secondValue, endpoint, secondRead, final⟩ := (success_bind _ _ _ _ _).mp rendered
              obtain ⟨sameValue, finalCross⟩ := getValue_agrees (leftFuel + 1) (rightFuel + 1) 0
                left reached leftAfter endpoint (.unenumerated (some handle) []) secondValue
                (frame.trans rightFrame) total reading secondRead
              subst secondValue
              simp only [lookup, boundary, ↓reduceIte] at final
              obtain ⟨rfl, rfl⟩ := (success_pure (Term.node (PartialSymbol.truncated : PartialSymbol Symbol) []) taggedTerm endpoint rightAfter).mp final
              exact ⟨finalCross, by rw [SourcePruningPositions.openProgram_truncated]; rfl⟩

private theorem pending_agrees (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (leftFuel rightFuel : Nat) (inputs : List (EnumGuard × Fragment Symbol))
    (left right leftAfter rightAfter : State Symbol EnumGuard)
    (pending : List (EnumGuard × Term Symbol)) (partials : List (EnumGuard × PartialTerm))
    (frame : Frame left right) (total : UnionFind.Total left.representatives) (inputBoundary : Opaque heap left)
    (concrete : Success (inputs.mapM fun input => do
      pure (input.1, ← SourcePruningEnumerationRendering.expandFragment heap marker leftFuel input.2)) left pending leftAfter)
    (tagged : Success (inputs.mapM fun input => do
      pure (input.1, ← SourcePruningEnumerationPartialOutput.expandPartial heap rightFuel input.2)) right partials rightAfter) :
    Frame leftAfter rightAfter ∧ pending = partials.map (fun input => (input.1, SourcePruningPositions.openProgram true input.2)) := by
  induction inputs generalizing left right leftAfter rightAfter pending partials with
  | nil =>
      obtain ⟨rfl, rfl⟩ := (success_pure [] pending left leftAfter).mp concrete
      obtain ⟨rfl, rfl⟩ := (success_pure [] partials right rightAfter).mp tagged
      exact ⟨frame, rfl⟩
  | cons input rest ih =>
      rw [List.mapM_cons] at concrete tagged
      obtain ⟨output, middle, first, continued⟩ := (success_bind _ _ _ _ _).mp concrete
      obtain ⟨tail, last, remaining, final⟩ := (success_bind _ _ _ _ _).mp continued
      obtain ⟨partialOutput, reached, observed, traversed⟩ := (success_bind _ _ _ _ _).mp tagged
      obtain ⟨partialTail, endpoint, restObserved, finished⟩ := (success_bind _ _ _ _ _).mp traversed
      obtain ⟨term, firstAfter, rendered, paired⟩ := (success_bind _ _ _ _ _).mp first
      obtain ⟨rfl, rfl⟩ := (success_pure (input.1, term) output firstAfter middle).mp paired
      obtain ⟨taggedTerm, partialAfter, partialRendered, partialPaired⟩ := (success_bind _ _ _ _ _).mp observed
      obtain ⟨rfl, rfl⟩ := (success_pure (input.1, taggedTerm) partialOutput partialAfter reached).mp partialPaired
      obtain ⟨cross, same⟩ := fragment_agrees heap leftFuel rightFuel input.2 left right middle reached term taggedTerm
        frame total inputBoundary rendered partialRendered
      have rightFrame := partial_frame heap rightFuel input.2 right reached taggedTerm (frame.total total) partialRendered
      have leftFrame := frame.trans (rightFrame.trans cross.symm)
      obtain ⟨lastCross, tailsSame⟩ := ih middle reached last endpoint tail partialTail cross
        (leftFrame.total total) (opaque_frame heap left middle inputBoundary leftFrame) remaining restObserved
      obtain ⟨rfl, rfl⟩ := (success_pure ((input.1, term) :: tail) pending last leftAfter).mp final
      obtain ⟨rfl, rfl⟩ := (success_pure ((input.1, taggedTerm) :: partialTail) partials endpoint rightAfter).mp finished
      exact ⟨lastCross, by simp only [List.map_cons, same, tailsSame]⟩

private theorem pending_complete (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (level : Nat → Nat) (frontier : Nat) (inputs : List (EnumGuard × Fragment Symbol))
    (before : State Symbol EnumGuard) (safe : Safe before) (ordered : Stratified before level frontier)
    (bounded : ∀ input ∈ inputs, FragmentBound before.counter input.2) :
    ∃ fuel pending after,
      (∀ extra, Success (inputs.mapM fun input => do
        pure (input.1, ← SourcePruningEnumerationPartialOutput.expandPartial heap (fuel + extra) input.2)) before pending after) ∧
      RenderStable before after ∧ Frame before after := by
  induction inputs generalizing before with
  | nil => exact ⟨0, [], before, fun _ => (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩, .refl before safe, .refl before⟩
  | cons input rest ih =>
      obtain ⟨firstFuel, term, middle, first, firstStable, firstFrame, firstOrdered, _models⟩ :=
        SourcePruningEnumerationPartialOutput.expandPartial_complete heap level frontier input.2 before safe ordered
          (bounded input (by simp))
      obtain ⟨restFuel, pending, after, continued, lastStable, lastFrame⟩ :=
        ih middle firstStable.safe firstOrdered
          (fun input member => by rw [firstStable.counter]; exact bounded input (by simp [member]))
      let fuel := firstFuel + restFuel
      refine ⟨fuel, (input.1, term) :: pending, after, ?_, firstStable.trans lastStable, firstFrame.trans lastFrame⟩
      intro extra
      rw [List.mapM_cons]
      apply (success_bind _ _ _ _ _).mpr
      refine ⟨(input.1, term), middle, ?_, ?_⟩
      · apply (success_bind _ _ _ _ _).mpr
        refine ⟨term, middle, ?_, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩
        simpa only [fuel, Nat.add_assoc] using (first (restFuel + extra)).1
      · apply (success_bind _ _ _ _ _).mpr
        refine ⟨pending, after, ?_, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩
        simpa only [fuel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using continued (firstFuel + extra)

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

variable {Typing : Type} {width : Nat}
variable [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)]

private theorem packet_boundary
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {caller : SourceCurrentAllocatedPartialState.State width} {memos : EndpointMemoGateTrace.Memos}
    {metadata : SourcePruningRecordTypes.Metadata Typing} {before : EnumerationExpandableIndex.Cached Symbol Constraint}
    (packet : SourcePruningEnumerationRecursive.Packet formulas solver inventory caller memos metadata before)
    (finished : EnumerationPureSelection.next (fun _ => none) before = .done) :
    Opaque caller.checked.native.machine.heap before.core := by
  obtain ⟨_roots, _paths, _storage, realized, _waiting, flags⟩ := packet.valid
  have inactive := flags_false before finished
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

/-- Default concrete and tagged observations have the same projected root and ordered attachments. -/
theorem default_finished_render_partial
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {caller : SourceCurrentAllocatedPartialState.State width} {memos : EndpointMemoGateTrace.Memos}
    {metadata : SourcePruningRecordTypes.Metadata Typing} {before : EnumerationExpandableIndex.Cached Symbol Constraint}
    (packet : SourcePruningEnumerationRecursive.Packet formulas solver inventory caller memos metadata before)
    (canonical : EnumerationValidity.Canonical before.core) (references : ReferencesCarry before.core)
    (root : CarriesGraph before.core 0) (inside : 0 < before.core.counter)
    (finished : EnumerationPureSelection.next (fun _ => none) before = .done) :
    let heap := caller.checked.native.machine.heap
    let tagged := fun fuel => do
      let rootTerm ← SourcePruningEnumerationPartialOutput.rootPartial (EnumGuard := Constraint) heap fuel
      let attached ← (← get).obligations.mapM fun obligation => do
        pure (obligation.1, ← SourcePruningEnumerationPartialOutput.expandPartial heap fuel obligation.2)
      pure (rootTerm, attached)
    ∃ bound term pending concreteAfter partialRoot partialPending partialAfter,
      (∀ extra,
        Success (SourcePruningEnumerationRendering.render heap ("Mu", FullSyntax.Formula.top) (bound + extra) 0)
          before.core (term, pending) concreteAfter ∧
        Success (tagged (bound + extra)) before.core (partialRoot, partialPending) partialAfter) ∧
      RenderStable before.core concreteAfter ∧ Frame before.core concreteAfter ∧
      EnumerationValidity.Canonical concreteAfter ∧
      RenderStable before.core partialAfter ∧ Frame before.core partialAfter ∧
      term = SourcePruningPositions.openProgram true partialRoot ∧
      pending = partialPending.map (fun attachment => (attachment.1, SourcePruningPositions.openProgram true attachment.2)) := by
  dsimp only
  let heap := caller.checked.native.machine.heap
  let tagged : Nat → EnumerateM Symbol Constraint (PartialTerm × List (Constraint × PartialTerm)) := fun fuel => do
    let rootTerm ← SourcePruningEnumerationPartialOutput.rootPartial (EnumGuard := Constraint) heap fuel
    let attached ← (← get).obligations.mapM fun obligation => do
      pure (obligation.1, ← SourcePruningEnumerationPartialOutput.expandPartial heap fuel obligation.2)
    pure (rootTerm, attached)
  obtain ⟨concreteBound, term, pending, concreteAfter, concreteRuns, concreteStable, concreteFrame, concreteCanonical⟩ :=
    SourcePruningEnumerationDefaultFinishedRendering.default_finished_render packet canonical references root inside finished marker
  obtain ⟨level, frontier, ordered⟩ := packet.ordered
  obtain ⟨rootBound, partialRoot, partialMiddle, rootRuns, partialRootStable, partialRootFrame, partialOrdered, _completes⟩ :=
    SourcePruningEnumerationPartialOutput.rootPartial_complete heap level frontier before.core packet.safe ordered inside
  obtain ⟨pendingBound, partialPending, partialAfter, pendingRuns, partialPendingStable, partialPendingFrame⟩ :=
    pending_complete heap level frontier partialMiddle.obligations partialMiddle partialRootStable.safe partialOrdered
      partialRootStable.safe.1.guards
  let bound := concreteBound + rootBound + pendingBound
  have concreteAt : ∀ extra,
      Success (SourcePruningEnumerationRendering.render heap marker (bound + extra) 0) before.core (term, pending) concreteAfter := by
    intro extra
    simpa only [bound, Nat.add_assoc] using concreteRuns (rootBound + pendingBound + extra)
  have rootAt : ∀ extra,
      Success (SourcePruningEnumerationPartialOutput.rootPartial heap (bound + extra)) before.core partialRoot partialMiddle := by
    intro extra
    have same : rootBound + (concreteBound + pendingBound + extra) = bound + extra := by dsimp [bound]; omega
    rw [← same]
    exact (rootRuns (concreteBound + pendingBound + extra)).1
  have pendingAt : ∀ extra,
      Success (partialMiddle.obligations.mapM fun obligation => do
        pure (obligation.1, ← SourcePruningEnumerationPartialOutput.expandPartial heap (bound + extra) obligation.2))
        partialMiddle partialPending partialAfter := by
    intro extra
    have same : pendingBound + (concreteBound + rootBound + extra) = bound + extra := by dsimp [bound]; omega
    rw [← same]
    exact pendingRuns (concreteBound + rootBound + extra)
  have taggedAt : ∀ extra, Success (tagged (bound + extra)) before.core (partialRoot, partialPending) partialAfter := by
    intro extra
    dsimp only [tagged]
    apply (success_bind _ _ _ _ _).mpr
    refine ⟨partialRoot, partialMiddle, rootAt extra, ?_⟩
    apply (success_bind _ _ _ _ _).mpr
    refine ⟨partialMiddle, partialMiddle, (get_success _ _ _).mpr ⟨rfl, rfl⟩, ?_⟩
    exact (success_bind _ _ _ _ _).mpr
      ⟨partialPending, partialAfter, pendingAt extra, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩
  have actual := concreteAt 0
  unfold SourcePruningEnumerationRendering.render at actual
  obtain ⟨observedTerm, concreteMiddle, concreteRoot, continued⟩ := (success_bind _ _ _ _ _).mp actual
  obtain ⟨readState, readAfter, getting, traversed⟩ := (success_bind _ _ _ _ _).mp continued
  obtain ⟨sameState, sameAfter⟩ := (get_success _ _ _).mp getting
  subst readState
  subst readAfter
  obtain ⟨observedPending, endpoint, concretePending, paired⟩ := (success_bind _ _ _ _ _).mp traversed
  obtain ⟨sameOutput, rfl⟩ := (success_pure (observedTerm, observedPending) (term, pending) endpoint concreteAfter).mp paired
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj sameOutput
  have inputBoundary := packet_boundary packet finished
  obtain ⟨cross, rootSame⟩ := root_agrees heap (bound + 0) (bound + 0) before.core before.core concreteMiddle partialMiddle
    term partialRoot (.refl before.core) packet.safe.1.total inputBoundary concreteRoot (rootAt 0)
  have rootFrame := partialRootFrame.trans cross.symm
  have observedPartialPending := pendingAt 0
  rw [cross.obligations] at observedPartialPending
  obtain ⟨_finalCross, pendingSame⟩ := pending_agrees heap (bound + 0) (bound + 0) concreteMiddle.obligations
    concreteMiddle partialMiddle concreteAfter partialAfter pending partialPending cross (rootFrame.total packet.safe.1.total)
    (opaque_frame heap before.core concreteMiddle inputBoundary rootFrame) concretePending observedPartialPending
  refine ⟨bound, term, pending, concreteAfter, partialRoot, partialPending, partialAfter, ?_,
    concreteStable, concreteFrame, concreteCanonical, partialRootStable.trans partialPendingStable,
    partialRootFrame.trans partialPendingFrame, rootSame, pendingSame⟩
  intro extra
  exact ⟨concreteAt extra, taggedAt extra⟩

end MicroCFTA.SourcePruningEnumerationDefaultPartialAgreement
