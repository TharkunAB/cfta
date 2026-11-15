import MicroCFTA.SourcePruningEnumerationObservedRealPrefixResources
import MicroCFTA.SourceCurrentAllocatedReaderConsumed
import MicroCFTA.SourceCurrentAllocatedReaderNumeric
import MicroCFTA.SourceCurrentAllocatedRowReadNumeric
import MicroCFTA.SourceEqualityExposureCosts
import MicroCFTA.SourceEqualityAnnotationExposure
import MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy

import MicroCFTA.SourcePruningEnumerationSharedPreparedLiveRoot

set_option autoImplicit false

namespace MicroCFTA.SourcePruningEnumerationSharedRecursive
open EnumerationState EnumerationCorrectness EnumerationSchedule InternedConstructorTemplates
open InternedProbeProvenance SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourcePruningEnumerationRecursive (Packet)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedReaderControl (Config Good Step g)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Heap" => InternedConstructorTemplates.State Symbol Constraint
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]
attribute [local instance] SourcePruningEnumerationAction.actionMonadList

private theorem actual_collect_path (fuel limit : Nat) (before : Config Symbol Constraint)
    (good : Good limit before) :
    ∃ count after, SourceCurrentAllocatedReaderConsumed.Path count before after ∧
      after.heap = (MergedFreshOrdinaryExposure.collect fuel before.heap before.seen before.pending).state := by
  induction fuel generalizing before with
  | zero =>
      obtain ⟨heap, seen, pending⟩ := before
      cases pending <;> exact ⟨0, _, .refl _, rfl⟩
  | succ fuel ih =>
      obtain ⟨heap, seen, pending⟩ := before
      have advancePath (middle : Config Symbol Constraint)
          (step : Step (⟨heap, seen, pending⟩ : Config Symbol Constraint) middle)
          (same : (MergedFreshOrdinaryExposure.collect (fuel + 1) heap seen pending).state =
            (MergedFreshOrdinaryExposure.collect fuel middle.heap middle.seen middle.pending).state) :
          ∃ count after,
            SourceCurrentAllocatedReaderConsumed.Path count (⟨heap, seen, pending⟩ : Config Symbol Constraint) after ∧
            after.heap = (MergedFreshOrdinaryExposure.collect (fuel + 1) heap seen pending).state := by
        obtain ⟨count, after, path, endpoint⟩ := ih middle (step.good good)
        exact ⟨count + 1, after, .step step path, endpoint.trans same.symm⟩
      cases pending with
      | nil => exact ⟨0, _, .refl _, rfl⟩
      | cons value rest =>
          have available := good.available value List.mem_cons_self
          cases value with
          | empty => exact advancePath ⟨heap, seen, rest⟩ .empty rfl
          | reference name =>
              have impossible := good.closed (.reference name) List.mem_cons_self
              cases impossible
          | node entry rows depth free =>
              apply advancePath ⟨heap, seen, rest⟩ .node
              exact SourceEqualityAnnotationExposure.prepend_state _ rows
          | union entry members depth free =>
              by_cases visited : entry.identity ∈ seen
              · apply advancePath ⟨heap, seen, rest⟩ (.union_seen visited)
                simp only [MergedFreshOrdinaryExposure.collect, ite_eq_left visited]
              · apply advancePath ⟨heap, entry.identity :: seen, members ++ rest⟩ (.union_fresh visited)
                simp only [MergedFreshOrdinaryExposure.collect, ite_eq_right visited]
          | mu entry body depth ordinary =>
              by_cases visited : entry.identity ∈ seen
              · apply advancePath ⟨heap, seen, rest⟩ (.mu_seen visited)
                simp only [MergedFreshOrdinaryExposure.collect, ite_eq_left visited]
              · obtain ⟨result, middle, unfolded, _context, _cached, _covered, _available, _growth, _history⟩ :=
                  InternedFreshOrdinaryStoredSubstitution.unfold_complete_decoded (.mu entry body depth ordinary)
                    heap good.semantic.1 available good.semantic.2 good.covered
                apply advancePath ⟨middle, entry.identity :: seen, result :: rest⟩ (.mu_fresh visited unfolded)
                simp only [MergedFreshOrdinaryExposure.collect, ite_eq_right visited, unfolded]

private theorem actual_collect_state_fits
    (fuel limit control : Nat) (before : Config Symbol Constraint)
    (good : Good limit before) (fits : SourceCurrentAllocatedReaderControl.Fits control before) :
    SourceCurrentMemoMergeResourceControl.Fits (SourceCurrentAllocatedReaderNumeric.fuel limit control)
      (MergedFreshOrdinaryExposure.collect fuel before.heap before.seen before.pending).state := by
  obtain ⟨count, after, actual, same⟩ := actual_collect_path fuel limit before good
  obtain ⟨finalControl, _good, finalFits, path⟩ :=
    SourceCurrentAllocatedReaderNumeric.path_control actual control good fits
  have bounded := finalFits.mono (path.final_le
    SourceCurrentAllocatedReaderControl.g_mono SourceCurrentAllocatedReaderControl.g_strict)
  rw [← same]
  exact ⟨bounded.stored, bounded.nodes, bounded.edges, Nat.zero_le _⟩

private theorem actual_read_state_fits
    (fuel bound : Nat) (value : Node) (heap : Heap)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady heap)
    (available : Available heap value) (closed : value.free = [])
    (fits : SourceCurrentMemoMergeResourceControl.Fits bound heap) :
    SourceCurrentMemoMergeResourceControl.Fits (SourceCurrentProjectionUnionResources.readFuel bound)
      (MergedFreshOrdinaryExposure.nodeEdges fuel value heap).state := by
  let control := SourceCurrentAllocatedReaderNumeric.initialControl bound bound bound 1
  let total := SourceCurrentAllocatedReaderNumeric.fuel bound (g control)
  change SourceCurrentMemoMergeResourceControl.Fits total
    (MergedFreshOrdinaryExposure.nodeEdges fuel value heap).state
  have initialGood : Good bound (⟨heap, [], [value]⟩ : Config Symbol Constraint) :=
    ⟨semantic.ready.semantic, semantic.ready.covered, semantic.ready.depth,
      InternedValueMassBinderDepth.stored_bounded heap bound fits.stored,
      by intro original member; cases List.mem_singleton.mp member; exact available,
      by intro original member; cases List.mem_singleton.mp member; exact closed⟩
  have initialFits : SourceCurrentAllocatedReaderControl.Fits control
      (⟨heap, [], [value]⟩ : Config Symbol Constraint) := by
    have initial := SourceCurrentAllocatedReaderControl.initial_fits heap [] [value] bound fits.stored
      initialGood.available
    apply initial.mono
    simp only [SourceCurrentAllocatedReaderControl.initialBound,
      SourceCurrentAllocatedReaderNumeric.initialControl, control, List.length_singleton, Nat.one_mul, Nat.max_self]
    exact Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨fits.nodes, fits.edges⟩, Nat.le_refl _⟩
  have sufficient : g control ≤ total :=
    HeightOrderControlled.majorant_ge g SourceCurrentAllocatedReaderControl.g_strict (bound + 1) (g control)
  have earlier : control ≤ total :=
    Nat.le_trans (Nat.le_of_lt (SourceCurrentAllocatedReaderControl.g_strict control)) sufficient
  have unchanged (same : (MergedFreshOrdinaryExposure.nodeEdges fuel value heap).state = heap) :
      SourceCurrentMemoMergeResourceControl.Fits total
        (MergedFreshOrdinaryExposure.nodeEdges fuel value heap).state := by
    rw [same]
    have larger := initialFits.mono earlier
    exact ⟨larger.stored, larger.nodes, larger.edges, Nat.zero_le _⟩
  have closure (current : Heap)
      (good : Good bound (⟨current, [], [value]⟩ : Config Symbol Constraint))
      (currentFits : SourceCurrentAllocatedReaderControl.Fits (g control)
        (⟨current, [], [value]⟩ : Config Symbol Constraint)) :
      SourceCurrentMemoMergeResourceControl.Fits total
        (MergedFreshOrdinaryExposure.collect fuel current [] [value]).canonical.state := by
    rw [SourceEqualityAnnotationExposure.canonical_state]
    exact actual_collect_state_fits fuel bound (g control) ⟨current, [], [value]⟩ good currentFits
  cases value with
  | empty | reference | node => exact unchanged rfl
  | union entry members depth free =>
      exact closure heap initialGood (initialFits.mono
        (Nat.le_of_lt (SourceCurrentAllocatedReaderControl.g_strict control)))
  | mu entry body depth ordinary =>
      obtain ⟨result, middle, unfolded, _context, _cached, _covered, _available, growth, history⟩ :=
        InternedFreshOrdinaryStoredSubstitution.unfold_complete_decoded (.mu entry body depth ordinary)
          heap semantic.ready.semantic.1 available semantic.ready.semantic.2 semantic.ready.covered
      have step : Step (⟨heap, [], [.mu entry body depth ordinary]⟩ : Config Symbol Constraint)
          ⟨middle, [entry.identity], [result]⟩ := .mu_fresh (by simp) unfolded
      have producedGood := step.good initialGood
      have producedFits := step.fits initialGood initialFits
      have bounded := producedFits.mono sufficient
      have fallbackGood : Good bound (⟨middle, [], [.mu entry body depth ordinary]⟩ : Config Symbol Constraint) :=
        ⟨producedGood.semantic, producedGood.covered, producedGood.depth, producedGood.bounded,
          by intro original member; cases List.mem_singleton.mp member; exact available.grows heap middle growth history,
          by intro original member; cases List.mem_singleton.mp member; exact closed⟩
      have fallbackFits : SourceCurrentAllocatedReaderControl.Fits (g control)
          (⟨middle, [], [.mu entry body depth ordinary]⟩ : Config Symbol Constraint) :=
        ⟨producedFits.stored, producedFits.nodes, producedFits.edges,
          Nat.le_trans initialFits.work (Nat.le_of_lt (SourceCurrentAllocatedReaderControl.g_strict control))⟩
      have fallback := closure middle fallbackGood fallbackFits
      cases result with
      | node resultEntry rows level free =>
          simpa only [MergedFreshOrdinaryExposure.nodeEdges, unfolded, MergedSourceExposure.Result.state] using
            (show SourceCurrentMemoMergeResourceControl.Fits total middle from
              ⟨bounded.stored, bounded.nodes, bounded.edges, Nat.zero_le _⟩)
      | empty | reference | union | mu =>
          simpa only [MergedFreshOrdinaryExposure.nodeEdges, unfolded] using fallback

private theorem actual_narrow_state_resources
    (profile : Profile) (property : Constraint → Prop)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (metadata : Metadata Typing) (fuel uv : Nat) (value : Node) (before : Heap)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before)
    (costs : InternedFreshOrdinaryCostHeap.Heap before)
    (available : Available before value) (closed : value.free = [])
    (bounded : SourceCurrentConstrainedCapRequiredResources.HeapFits profile before)
    (known : SourceEqualityAnnotationHeap.Heap property before) :
    SourceCurrentConstrainedCapRequiredResources.HeapFits
        (SourceCurrentConstrainedCapEditForecast.headProfile profile)
        (SourcePruningOuterNarrow.narrow holeKey fits admits metadata fuel uv value before).state ∧
      SourceEqualityAnnotationHeap.Heap property
        (SourcePruningOuterNarrow.narrow holeKey fits admits metadata fuel uv value before).state := by
  have pureResources : SourceCurrentConstrainedCapRequiredResources.HeapFits
      (SourceCurrentConstrainedCapEditForecast.headProfile profile) before ∧
      SourceEqualityAnnotationHeap.Heap property before :=
    ⟨bounded.mono (SourceCurrentConstrainedCapEditForecast.headProfile_ge profile), known⟩
  have fallback (input : Node) (inputAvailable : Available before input) (inputClosed : input.free = []) :
      SourceCurrentConstrainedCapRequiredResources.HeapFits
        (SourceCurrentConstrainedCapEditForecast.headProfile profile)
        (SourcePruningNativeView.narrowAt fits admits fuel (holeKey metadata.typing uv) input before).state ∧
      SourceEqualityAnnotationHeap.Heap property
        (SourcePruningNativeView.narrowAt fits admits fuel (holeKey metadata.typing uv) input before).state := by
    cases exposed : MergedFreshOrdinaryExposure.nodeEdges fuel input before with
    | done rows middle =>
        let constructed := InternedConstructorTemplates.run (makeNode (rows.filter (SourcePruningNativeView.keeps fits admits
          (holeKey metadata.typing uv)))) middle
        have completed : SourcePruningNativeView.narrowAt fits admits fuel
            (holeKey metadata.typing uv) input before = .done constructed.1 constructed.2 := by
          simp only [SourcePruningNativeView.narrowAt, exposed, constructed]
        have actual := SourcePruningNativeView.narrowAt_resources profile property fits admits
          (holeKey metadata.typing uv) fuel input before constructed.1 constructed.2 completed
          semantic costs inputAvailable inputClosed bounded known
        simpa only [completed, MergedSourceComparison.Result.state] using actual
    | unresolved | pending | exhausted =>
        have actual := actual_read_state_fits fuel (SourceCurrentConstrainedCapEditForecast.scalar profile)
          input before semantic inputAvailable inputClosed bounded.scalar_fits
        have small : SourceCurrentProjectionUnionResources.readFuel
            (SourceCurrentConstrainedCapEditForecast.scalar profile) ≤
            SourceCurrentProjectionUnionResources.headGrowth
              (SourceCurrentConstrainedCapEditForecast.scalar profile) :=
          Nat.le_trans (show SourceCurrentProjectionUnionResources.readFuel
              (SourceCurrentConstrainedCapEditForecast.scalar profile) ≤
              SourceCurrentProjectionUnionResources.readGrowth
                (SourceCurrentConstrainedCapEditForecast.scalar profile) by
              unfold SourceCurrentProjectionUnionResources.readGrowth
              omega)
            (SourceCurrentMemoMergeResourceControl.primitiveGrowth_ge _ _)
        have larger := actual.mono small
        have kept := SourceEqualityAnnotationExposure.nodeEdges_heap property fuel input before
          semantic.ready.semantic semantic.ready.covered known inputAvailable inputClosed
        simpa only [SourcePruningNativeView.narrowAt, exposed, MergedSourceExposure.Result.state,
          MergedSourceComparison.Result.state, SourceCurrentConstrainedCapEditForecast.headProfile] using
          (show SourceCurrentConstrainedCapRequiredResources.HeapFits
            (SourceCurrentConstrainedCapEditForecast.headProfile profile)
            (MergedFreshOrdinaryExposure.nodeEdges fuel input before).state ∧
            SourceEqualityAnnotationHeap.Heap property
              (MergedFreshOrdinaryExposure.nodeEdges fuel input before).state from
            ⟨⟨larger.nodes, larger.edges, larger.stored⟩, kept⟩)
  cases value with
  | mu entry body depth ordinary => exact pureResources
  | empty | reference | node | union =>
      by_cases typed : metadata.types.contains uv = true
      · simpa only [SourcePruningOuterNarrow.narrow, typed, ↓reduceIte,
          MergedSourceComparison.Result.state] using pureResources
      · simp only [SourcePruningOuterNarrow.narrow]
        rw [ite_eq_right typed]
        exact fallback _ available closed

private theorem prepared_state
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (metadata : Metadata Typing) (fuel representativeFuel uv oldHandle : Nat)
    (scs : List Suspended) (oldValue : Node) (heap : Heap) :
    (SourcePruningEnumerationAction.prepare (EnumGuard := Constraint) holeKey fits admits metadata fuel representativeFuel
      uv oldHandle scs oldValue heap).state =
      (SourcePruningOuterNarrow.narrow holeKey fits admits metadata fuel uv oldValue heap).state := by
  unfold SourcePruningEnumerationAction.prepare SourcePruningEnumerationAction.prepareWithNarrow
  cases SourcePruningOuterNarrow.narrow holeKey fits admits metadata fuel uv oldValue heap <;> rfl

/-- Every actual real prefix endpoint fits the original native resource forecast. -/
theorem prefix_real_resources_at_original_budget
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (before : Cached)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (profile : Profile) (property : Constraint → Prop)
    (bounded : SourceCurrentConstrainedCapGeneratedQueryResources.Fits profile caller.checked)
    (known : SourceEqualityAnnotationHeap.Heap property caller.checked.native.machine.heap)
    (workFuel selected : Nat)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand selected)) :
    SourcePruningEnumerationSelectedStep.Resources profile property caller
      (SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
        workFuel workFuel workFuel workFuel workFuel workFuel selected caller before memos.query)
 := by
  classical
  have _selectedDecision := chosen
  obtain ⟨_roots, _paths, _storage, realized, _counts, _flags⟩ := packet.valid
  have initial : SourceCurrentConstrainedCapGeneratedQueryResources.Fits
        (SourceCurrentConstrainedCapEditForecast.headProfile profile) caller.checked ∧
      SourceEqualityAnnotationHeap.Heap property caller.checked.native.machine.heap :=
    ⟨bounded.mono (SourceCurrentConstrainedCapEditForecast.headProfile_ge profile), known⟩
  by_cases readable : ∃ (oldHandle : Nat) (scs : List Suspended) (readAfter : Core),
      ExceptT.run (getValue workFuel selected before.core) =
        [.ok (.unenumerated (some oldHandle) scs, readAfter)]
  · obtain ⟨oldHandle, scs, readAfter, reading⟩ := readable
    by_cases fresh : ∃ checked : Core,
        ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated caller.checked.native.machine.heap
          workFuel selected oldHandle scs readAfter) = [.ok (false, checked)]
    · obtain ⟨checked, checking⟩ := fresh
      cases decoded : lookupNode caller.checked.native.machine.heap oldHandle with
      | none =>
          simpa only [SourcePruningEnumerationSelectedStep.runPrefix,
            SourcePruningEnumerationSelectedStep.runPrefixWithNarrow, reading, checking, decoded,
            SourcePruningEnumerationSelectedStep.Resources] using initial
      | some oldValue =>
          have readObserved : Success (getValue workFuel selected) before.core
              (.unenumerated (some oldHandle) scs) readAfter := by
            rw [Success, reading]
            exact List.mem_singleton_self _
          obtain ⟨found, _lookup, stored, _readState⟩ :=
            (getValue_success workFuel selected before.core readAfter
              (.unenumerated (some oldHandle) scs)).mp readObserved
          obtain ⟨old, lookup, available, closed⟩ := realized found.representative oldHandle scs stored
          have same : old = oldValue := Option.some.inj (lookup.symm.trans decoded)
          subst old
          have native := actual_narrow_state_resources profile property holeKey fits admits metadata
            workFuel selected oldValue caller.checked.native.machine.heap
            packet.context.ready.semantic packet.context.ready.costs available closed
            (SourceCurrentConstrainedCapRequiredResources.of_checked bounded) known
          let prepared := SourcePruningEnumerationAction.prepare (EnumGuard := Constraint) holeKey fits admits metadata workFuel workFuel
            selected oldHandle scs oldValue caller.checked.native.machine.heap
          have preparedResources : SourceCurrentConstrainedCapRequiredResources.HeapFits
              (SourceCurrentConstrainedCapEditForecast.headProfile profile) prepared.state ∧
              SourceEqualityAnnotationHeap.Heap property prepared.state := by
            dsimp only [prepared]
            rw [prepared_state]
            exact native
          have reachedResources : SourceCurrentConstrainedCapGeneratedQueryResources.Fits
              (SourceCurrentConstrainedCapEditForecast.headProfile profile)
              (SourceCurrentAllocatedPartialState.advance caller
                (advancePhysical caller.checked ⟨prepared.state, caller.checked.operations⟩)
                caller.fourth caller.merge).checked ∧
              SourceEqualityAnnotationHeap.Heap property prepared.state :=
            ⟨⟨preparedResources.1.nodes, preparedResources.1.edges,
              Nat.le_trans bounded.domains (SourceCurrentConstrainedCapEditForecast.headProfile_ge profile).2.2.1,
              preparedResources.1.stored⟩, preparedResources.2⟩
          unfold SourcePruningEnumerationSelectedStep.runPrefix SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
          simp only [reading, checking, decoded]
          simp only [← SourcePruningEnumerationAction.prepare_configured_eq]
          dsimp only [prepared] at reachedResources
          generalize preparedEq : SourcePruningEnumerationAction.prepare (EnumGuard := Constraint) holeKey fits admits metadata
            workFuel workFuel selected oldHandle scs oldValue caller.checked.native.machine.heap = preparedResult
            at reachedResources ⊢
          cases preparedResult with
          | failed fault heap => exact reachedResources
          | done pair heap =>
              obtain ⟨value, action⟩ := pair
              cases action with
              | none => exact reachedResources
              | some action =>
                  repeat' first
                  | exact reachedResources
                  | split
    · unfold SourcePruningEnumerationSelectedStep.runPrefix SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
      rw [reading]
      dsimp only
      split
      · exact initial
      · exact (fresh ⟨_, by assumption⟩).elim
      · exact initial
  · have stopped : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
        workFuel workFuel workFuel workFuel workFuel workFuel selected caller before memos.query =
        .stopped (ExceptT.run (getValue workFuel selected before.core)) none := by
      unfold SourcePruningEnumerationSelectedStep.runPrefix SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
      dsimp only
      split
      · exact (readable ⟨_, _, _, by assumption⟩).elim
      · rfl
    rw [stopped]
    exact initial

/-- Zero read fuel stops before any selected native preparation and has no current-prefix certificate. -/
theorem prefix_zero_stops_and_not_current
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (before : Cached)
    (profile : Profile) (property : Constraint → Prop) (selected : Nat) :
    let observed := SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
      0 0 0 0 0 0 selected caller before memos.query
    observed = .stopped [.error .representativeFuel] none ∧
      ¬ CurrentPrefixResources stop order metadata formulas solver inventory selected caller before memos
        profile property observed
 := by
  have reading : ExceptT.run (getValue 0 selected before.core) = [.error .representativeFuel] := rfl
  have stopped : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
      0 0 0 0 0 0 selected caller before memos.query = .stopped [.error .representativeFuel] none := by
    simp only [SourcePruningEnumerationSelectedStep.runPrefix,
      SourcePruningEnumerationSelectedStep.runPrefixWithNarrow, reading]
  dsimp only
  refine ⟨stopped, ?_⟩
  rw [stopped]
  intro current
  exact current.1

section Noncontinuing
open SourcePruningEnumerationSharedSelectedContinuations
local notation "Output" => SourcePruningEnumerationSharedPreparedRecursive.Output
local notation "Failure" => SourcePruningEnumerationSharedPreparedRecursive.Failure
local notation "Fold" => NativeContinuations.Result (Output width Typing) (Failure width Typing) width
local notation "Visitor" => List Suspended → Node → Caller width → Cached → Queries →
  (Fragments.Fragment Symbol → Caller width → Queries → Cached → Fold) →
  (SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.Observation width → Option Cached → Fold) → Fold

/-- A real selected step outside both continuation forms emits no local output at its original budget. -/
theorem real_prefix_noncontinuing_emits_no_output
    [DecidableEq Symbol] [DecidableEq Node]
    (child : Visitor)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata : Metadata Typing) (workFuel recursiveFuel selected : Nat)
    (caller : Caller width) (queries : Queries) (before : Cached)
    (observed : SourcePruningEnumerationSelectedStep.Result width Typing)
    (actual : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
      workFuel workFuel workFuel workFuel workFuel workFuel selected caller before queries = observed)
    (noncontinuing : match observed with
      | .parked _ (some _) (some [.ok ((_updated, _next), _core)]) => False
      | .narrowed _ _ _ _ (some []) _ _ _ => True
      | .narrowed _ _ _ _ _ _ (some [.ok ((true, _updated), _core)]) _ => True
      | .narrowed _ _ _ _ _ (some _) (some [.ok ((false, _updated), _core)]) none => False
      | _ => True) :
    SourcePruningEnumerationSharedPreparedRecursive.emitted
      (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow child
        (SourcePruningOuterNarrow.narrow holeKey fits admits) graph templates checkEmpty edgesOf stop order
        workFuel (recursiveFuel + 1) metadata caller queries before (some (.expand selected))) = []
 := by
  have observing : SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
      (SourcePruningOuterNarrow.narrow holeKey fits admits) graph templates stop order metadata
      workFuel workFuel workFuel workFuel workFuel workFuel selected caller before queries = observed := actual
  cases observed with
  | stopped read checked =>
      simp only [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow,
        observing, SourcePruningEnumerationSharedPreparedRecursive.emitted]
  | parked checked candidate raw =>
      cases candidate with
      | none =>
          simp only [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow,
            observing, SourcePruningEnumerationSharedPreparedRecursive.emitted]
      | some parked =>
          cases raw with
          | none =>
              simp only [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow,
                observing, SourcePruningEnumerationSharedPreparedRecursive.emitted]
          | some rows =>
              cases rows with
              | nil =>
                  simp only [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow,
                    observing, SourcePruningEnumerationSharedPreparedRecursive.emitted]
              | cons first rest =>
                  cases first with
                  | error fault =>
                      simp only [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow,
                        observing, SourcePruningEnumerationSharedPreparedRecursive.emitted]
                  | ok payload =>
                      rcases payload with ⟨⟨updated, next⟩, core⟩
                      cases rest with
                      | nil => exact False.elim noncontinuing
                      | cons second tail =>
                          simp only [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow,
                            observing, SourcePruningEnumerationSharedPreparedRecursive.emitted]
  | narrowed checked prepared reached saved action candidate right ordinary =>
      cases action with
      | none =>
          cases right with
          | none =>
              simp only [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow,
                observing, SourcePruningEnumerationSharedPreparedRecursive.emitted]
          | some rows =>
              cases rows with
              | nil =>
                  simp only [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow,
                    observing, SourcePruningEnumerationSharedPreparedRecursive.emitted]
              | cons first rest =>
                  cases first with
                  | error fault =>
                      simp only [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow,
                        observing, SourcePruningEnumerationSharedPreparedRecursive.emitted]
                  | ok payload =>
                      rcases payload with ⟨⟨pruned, updated⟩, core⟩
                      cases rest with
                      | cons second tail =>
                          cases pruned <;>
                            simp only [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow,
                              observing, SourcePruningEnumerationSharedPreparedRecursive.emitted]
                      | nil =>
                          cases pruned with
                          | true =>
                              simp only [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow,
                                observing, SourcePruningEnumerationSharedPreparedRecursive.emitted]
                          | false =>
                              cases candidate with
                              | none =>
                                  simp only [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow,
                                    observing, SourcePruningEnumerationSharedPreparedRecursive.emitted]
                              | some after =>
                                  cases ordinary with
                                  | none => exact False.elim noncontinuing
                                  | some details =>
                                      simp only [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow,
                                        observing, SourcePruningEnumerationSharedPreparedRecursive.emitted]
      | some rows =>
          cases rows with
          | nil =>
              simp only [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow,
                observing, SourcePruningEnumerationSharedPreparedRecursive.emitted]
          | cons first rest =>
              cases right with
              | none =>
                  simp only [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow,
                    observing, SourcePruningEnumerationSharedPreparedRecursive.emitted]
              | some rows =>
                  cases rows with
                  | nil =>
                      simp only [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow,
                        observing, SourcePruningEnumerationSharedPreparedRecursive.emitted]
                  | cons first rest =>
                      cases first with
                      | error fault =>
                          simp only [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow,
                            observing, SourcePruningEnumerationSharedPreparedRecursive.emitted]
                      | ok payload =>
                          rcases payload with ⟨⟨pruned, updated⟩, core⟩
                          cases rest with
                          | cons second tail =>
                              cases pruned <;>
                                simp only [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow,
                                  observing, SourcePruningEnumerationSharedPreparedRecursive.emitted]
                          | nil =>
                              cases pruned with
                              | true =>
                                  simp only [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow,
                                    observing, SourcePruningEnumerationSharedPreparedRecursive.emitted]
                              | false =>
                                  cases candidate with
                                  | none =>
                                      simp only [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow,
                                        observing, SourcePruningEnumerationSharedPreparedRecursive.emitted]
                                  | some after =>
                                      cases ordinary with
                                      | none => exact False.elim noncontinuing
                                      | some details =>
                                          simp only [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow,
                                            observing, SourcePruningEnumerationSharedPreparedRecursive.emitted]

end Noncontinuing
end MicroCFTA.SourcePruningEnumerationSharedRecursive
