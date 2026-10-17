import MicroCFTA.SourceCurrentScanNumericForecast
import MicroCFTA.SourceCurrentSeededGuardNumeric
import MicroCFTA.SourceCurrentSecondarySeededSupport
import MicroCFTA.SourceCurrentSeededInitialRanges
import MicroCFTA.SourceCurrentConjunctionCallUnique
import MicroCFTA.SourceCurrentAllocatedScanWorker

/-!
# Complete current Scans from initial numeric resources

The initial class list determines every profile, alphabet, and reservation.
Actual gates derive selected support. Actual seeded and memo returns feed
the original suffix. The old range interface is an output of this proof.
-/
namespace MicroCFTA.SourceCurrentScanNumeric
open Cache EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
open SourceCurrentConjunctionClassScan (Scan advanceHeap)
open SourceCurrentScanNumericForecast (classStep schedule Reserved fuel classFuel)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
local notation "gateProfile" => SourceCurrentGateFrameResources.forecast
local notation "Ranges" => SourceCurrentConjunctionClassScanCompletion.Ranges
variable {bits width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- One exact Scan return retains the full Frame and the initial numeric schedule. -/
structure Receipt (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (alphabet : List Guard) (profile : Profile) (budget : Nat) (values : List (Value Symbol Guard)) (classes : Constraints)
    (before : Checked width) (memo : Memo) (outcome : Option Class) (selected : Constraints)
    (after : Checked width) (saved : Memo) (inventory : Inventory) : Prop where
  /-- The original Scan graph retains the same complete return. -/
  actual : Scan budget source reaches values classes before memo outcome selected after saved
  /-- The initial numeric proof derives the original universal reached-range contract. -/
  ranges : Ranges budget source reaches values classes before memo
  /-- The same returned inventory carries the full native query Frame. -/
  frame : Frame formulas solver inventory after
  /-- The exact return fits the schedule computed from the initial inputs. -/
  fits : Fits (schedule budget values.length classes alphabet profile).2 after
  /-- Every returned physical guard belongs to the predicted finite alphabet. -/
  carrier : Heap (fun guard => guard ∈ (schedule budget values.length classes alphabet profile).1) after.native.machine.heap
  /-- The full physical return retains readiness and constructor histories. -/
  effects : Effects (physical before) (physical after)
  /-- Every original forest occurrence remains available after the Scan. -/
  available : Values after.native.machine.heap values
  /-- The exact saved fourth memo retains its semantic correctness. -/
  correct : SourceCurrentEmptinessMemo.Correct formulas solver after.native.machine.heap saved
  /-- Every initial fourth-memo entry remains in the exact saved memo. -/
  retained : SourceCurrentEmptinessMemo.Extends memo saved
  /-- Each independently larger worker fuel returns the same full state and memo. -/
  run : ∀ g s p h n, fuel budget values.length classes alphabet profile ≤ g →
    fuel budget values.length classes alphabet profile ≤ s → fuel budget values.length classes alphabet profile ≤ p →
    fuel budget values.length classes alphabet profile ≤ h → fuel budget values.length classes alphabet profile ≤ n →
    SourceCurrentAllocatedScanWorker.scan g s p h n budget values classes before memo =
      .done (outcome, selected) after saved

/-- Initial caller invariants construct the complete Scan, its ranges, and exact worker return. -/
theorem complete (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (alphabet : List Guard) (budget : Nat) (values : List (Value Symbol Guard)) (classes : Constraints)
    (before : Checked (bits + 2)) (memo : Memo) (inventory : Inventory)
    (frame : Frame formulas solver inventory before) (profile : Profile) (fits : Fits profile before)
    (available : Values before.native.machine.heap values)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo)
    (known : Heap (fun guard => guard ∈ alphabet) before.native.machine.heap)
    (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ [])
    (reserved : Reserved bits budget values.length classes alphabet profile)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    ∃ outcome selected after saved next,
      Receipt formulas solver alphabet profile budget values classes before memo outcome selected after saved next := by
  induction classes generalizing before memo inventory profile alphabet memos with
  | nil =>
      exact ⟨none, [], before, memo, inventory, .nil, trivial, frame, fits, known,
        .refl _ (SourceCurrentAllocatedConjunctionMemo.ready before frame.ready.good frame.ready.semantic frame.ready.costs),
        available, correct, (fun _ _ found => found), by intros; rfl⟩
  | cons paths classes ih =>
      let nextPlan := classStep budget values.length paths alphabet profile
      have tailProper : ∀ other ∈ classes, ∀ path ∈ other, path ≠ [] :=
        fun other member => proper other (List.mem_cons_of_mem _ member)
      have limits := SourceCurrentScanNumericForecast.classFuel_limits budget values.length paths alphabet profile
      have localFuel : classFuel budget values.length paths alphabet profile ≤
          fuel budget values.length (paths :: classes) alphabet profile := Nat.le_max_left _ _
      have tailFuel : fuel budget values.length classes nextPlan.1 nextPlan.2 ≤
          fuel budget values.length (paths :: classes) alphabet profile := Nat.le_max_right _ _
      have widen := SourceCurrentScanNumericForecast.classStep_alphabet_ge budget values.length paths alphabet profile
      obtain ⟨firstAnswer, heap, primary, firstFrame, firstFits, firstValues, firstEffects, firstDone⟩ :=
        SourceCurrentGateFrameResources.primary formulas solver inventory source reaches values paths before frame profile fits available
      have firstCorrect := SourceCurrentEmptinessMemo.grows formulas solver firstEffects.keeps memo correct
      have firstKnown := (SourcePrimaryGateEffects.class_effects (fun guard => guard ∈ alphabet)
        source reaches primary frame.ready.semantic frame.ready.costs available known).2.2.2
      have firstValid := SourceQueryUnfoldMemo.valid_grows _ _ frame.ready.semantic firstEffects.keeps memos valid
      cases firstAnswer with
      | false =>
          obtain ⟨outcome, selected, after, saved, next, rest⟩ := ih (alphabet := nextPlan.1) (before := advanceHeap before heap) (memo := memo)
            (inventory := inventory) (profile := nextPlan.2) firstFrame (firstFits.mono (SourceCurrentScanNumericForecast.classStep_primary_ge _ _ _ _ _)) firstValues
            firstCorrect (SourceCurrentNativeGuardStep.heap_mono widen firstKnown) tailProper reserved.2 memos firstValid
          refine ⟨outcome, paths :: selected, after, saved, next,
            .selected primary rest.actual, ?_, rest.frame, rest.fits, rest.carrier,
            firstEffects.trans rest.effects, rest.available, rest.correct, rest.retained, ?_⟩
          · refine ⟨?_, ?_, ?_⟩
            · intro other actual
              obtain ⟨_same, rfl⟩ := EndpointStatefulGateTrace.class_trace_unique source reaches values paths
                before.native.machine.heap false false heap other primary actual
              exact rest.ranges
            · intro other actual
              have impossible := (EndpointStatefulGateTrace.class_trace_unique source reaches values paths
                before.native.machine.heap false true heap other primary actual).1
              cases impossible
            · intro other actual
              have impossible := (EndpointStatefulGateTrace.class_trace_unique source reaches values paths
                before.native.machine.heap false true heap other primary actual).1
              cases impossible
          · intro g s p h n enoughG enoughS enoughP enoughH enoughN
            have first := firstDone g (Nat.le_trans (Nat.le_trans limits.1 localFuel) enoughG)
            have tail := rest.run g s p h n (Nat.le_trans tailFuel enoughG) (Nat.le_trans tailFuel enoughS)
              (Nat.le_trans tailFuel enoughP) (Nat.le_trans tailFuel enoughH) (Nat.le_trans tailFuel enoughN)
            simp [SourceCurrentAllocatedScanWorker.scan, SourceCurrentAllocatedScanWorker.gate,
              SourceCurrentAllocatedGateWorker.primary, first, SourceCurrentAllocatedGateWorker.lift,
              SourceCurrentAllocatedScanWorker.Outcome.bind, tail, SourceCurrentAllocatedScanWorker.Outcome.select]
      | true =>
          obtain ⟨secondAnswer, anchor, secondary, secondFrame, secondFits, secondValues, secondEffects, secondDone⟩ :=
            SourceCurrentGateFrameResources.secondary formulas solver inventory source reaches values paths
              (advanceHeap before heap) firstFrame (gateProfile paths profile) firstFits firstValues
          have secondCorrect := SourceCurrentEmptinessMemo.grows formulas solver secondEffects.keeps memo firstCorrect
          have secondKnown := (SourceCurrentSecondaryEffects.class_effects (fun guard => guard ∈ alphabet)
            source secondary firstFrame.ready.semantic firstFrame.ready.costs firstValues firstKnown).2.2.2
          have secondValid := SourceQueryUnfoldMemo.valid_grows _ _ firstFrame.ready.semantic secondEffects.keeps memos firstValid
          cases secondAnswer with
          | true =>
              obtain ⟨outcome, selected, after, saved, next, rest⟩ := ih (alphabet := nextPlan.1) (before := advanceHeap (advanceHeap before heap) anchor)
                (memo := memo) (inventory := inventory) (profile := nextPlan.2) secondFrame
                (secondFits.mono (SourceCurrentScanNumericForecast.classStep_secondary_ge _ _ _ _ _)) secondValues
                secondCorrect (SourceCurrentNativeGuardStep.heap_mono widen secondKnown) tailProper reserved.2 memos secondValid
              refine ⟨outcome, selected, after, saved, next, .skipped primary secondary rest.actual, ?_,
                rest.frame, rest.fits, rest.carrier, firstEffects.trans (secondEffects.trans rest.effects),
                rest.available, rest.correct, rest.retained, ?_⟩
              · refine ⟨?_, ?_, ?_⟩
                · intro other actual
                  have impossible := (EndpointStatefulGateTrace.class_trace_unique source reaches values paths
                    before.native.machine.heap true false heap other primary actual).1
                  cases impossible
                · intro other actual nextAnchor otherSecondary
                  obtain ⟨_same, rfl⟩ := EndpointStatefulGateTrace.class_trace_unique source reaches values paths
                    before.native.machine.heap true true heap other primary actual
                  obtain ⟨_same, rfl⟩ := SourceCurrentSecondaryTrace.class_trace_unique source values paths heap
                    true true anchor nextAnchor secondary otherSecondary
                  exact rest.ranges
                · intro other actual nextAnchor otherSecondary
                  obtain ⟨_same, rfl⟩ := EndpointStatefulGateTrace.class_trace_unique source reaches values paths
                    before.native.machine.heap true true heap other primary actual
                  have impossible := (SourceCurrentSecondaryTrace.class_trace_unique source values paths heap
                    true false anchor nextAnchor secondary otherSecondary).1
                  cases impossible
              · intro g s p h n enoughG enoughS enoughP enoughH enoughN
                have first := firstDone g (Nat.le_trans (Nat.le_trans limits.1 localFuel) enoughG)
                have second := secondDone s (Nat.le_trans (Nat.le_trans limits.2.1 localFuel) enoughS)
                have tail := rest.run g s p h n (Nat.le_trans tailFuel enoughG) (Nat.le_trans tailFuel enoughS)
                  (Nat.le_trans tailFuel enoughP) (Nat.le_trans tailFuel enoughH) (Nat.le_trans tailFuel enoughN)
                simp [SourceCurrentAllocatedScanWorker.scan, SourceCurrentAllocatedScanWorker.gate,
                  SourceCurrentAllocatedGateWorker.primary, SourceCurrentAllocatedGateWorker.secondary, first, second,
                  SourceCurrentAllocatedGateWorker.lift, SourceCurrentAllocatedScanWorker.Outcome.bind, tail]
          | false =>
              have support := SourceCurrentSecondarySeededSupport.class_support source secondary firstFrame.ready.semantic
                firstFrame.ready.costs firstValues (proper paths List.mem_cons_self)
              have signedProper := SourceCurrentSecondarySeededSupport.mapped_proper (proper paths List.mem_cons_self)
              have seededRanges := SourceCurrentSeededInitialRanges.complete formulas solver inventory source anchor support.1
                support.2.2.1 values (paths.map (List.map Int.ofNat)) (advanceHeap (advanceHeap before heap) anchor)
                (gateProfile paths (gateProfile paths profile)) secondFrame secondFits secondValues (grows_refl _)
                support.2.2.2.2.2.2 signedProper reserved.1 memos secondValid
              obtain ⟨query, middle, queryInventory, queryMemos, seeded, _reads, receipt, queryFits, _included, queryDone, queryKnown⟩ :=
                SourceCurrentSeededGuardNumeric.complete alphabet formulas solver inventory source anchor support.1 support.2.2.1
                  values (paths.map (List.map Int.ofNat)) (advanceHeap (advanceHeap before heap) anchor)
                  (gateProfile paths (gateProfile paths profile)) secondFrame secondFits secondValues (grows_refl _)
                  support.2.2.2.2.2.2 signedProper reserved.1 secondKnown memos secondValid
              have queryCorrect := SourceCurrentEmptinessMemo.grows formulas solver receipt.effects.keeps memo secondCorrect
              have physicalReady := SourceCurrentAllocatedConjunctionMemo.ready middle receipt.frame.ready.good
                receipt.frame.ready.semantic receipt.frame.ready.costs
              have scalarFits := (SourceCurrentConstrainedCapRequiredResources.of_checked queryFits).scalar_fits
              obtain ⟨answer, later, savedMemo, decision, memoEffects, memoCorrect, _sound, retained, _guards, memoKnown, bounded, memoDone⟩ :=
                SourceCurrentConjunctionAlphabetBounds.memo_complete formulas solver nextPlan.1 budget memo query (physical middle)
                  (SourceCurrentConstrainedCapTargetForecast.scalar
                    (SourceCurrentConstrainedCapSeededForecast.finalProfile values.length (paths.map (List.map Int.ofNat))
                      (gateProfile paths (gateProfile paths profile)))) physicalReady receipt.available scalarFits queryCorrect
                  Plain receipt.frame.context.guards queryKnown
              have finalFrame := SourceCurrentConjunctionCallerNumeric.of_call formulas solver decision receipt.frame receipt.available queryCorrect
              have memoFits : Fits nextPlan.2 (advancePhysical middle later) :=
                ⟨bounded.nodes, bounded.edges, queryFits.domains, bounded.stored⟩
              have memoValues : Values (advancePhysical middle later).native.machine.heap values :=
                fun value member => memoEffects.keeps.available value (receipt.effects.keeps.available value (secondValues value member))
              have memoValid := SourceQueryUnfoldMemo.valid_grows _ _ receipt.frame.ready.semantic memoEffects.keeps
                queryMemos receipt.globals.valid
              have queryStable := fun (p h n : Nat) enoughP enoughH enoughN =>
                SourceCurrentAllocatedSeededWorkerStability.seeded_done_stable (P := p) (H := h) (N := n) queryDone enoughP enoughH enoughN
              have actualRanges : ∀ other, EndpointStatefulGateTrace.ClassTrace source reaches values paths
                  before.native.machine.heap true other → ∀ nextAnchor,
                  SourceCurrentSecondaryTrace.ClassTrace source values paths other false nextAnchor →
                  SourceCurrentAllocatedSeededQuery.SeededRanges values (paths.map (List.map Int.ofNat))
                    (advanceHeap (advanceHeap before other) nextAnchor) ∧
                  ∀ otherQuery otherMiddle, SourceCurrentAllocatedSeededQuery.Seeded values (paths.map (List.map Int.ofNat))
                    (advanceHeap (advanceHeap before other) nextAnchor) otherQuery otherMiddle →
                    ∀ otherLater otherSaved, SourceCurrentConjunctionMemo.Call budget memo otherQuery (physical otherMiddle) false otherLater otherSaved →
                      answer = false ∧ otherLater = later ∧ otherSaved = savedMemo := by
                intro other actual nextAnchor otherSecondary
                obtain ⟨_same, rfl⟩ := EndpointStatefulGateTrace.class_trace_unique source reaches values paths
                  before.native.machine.heap true true heap other primary actual
                obtain ⟨_same, rfl⟩ := SourceCurrentSecondaryTrace.class_trace_unique source values paths heap
                  false false anchor nextAnchor secondary otherSecondary
                refine ⟨seededRanges, ?_⟩
                intro otherQuery otherMiddle otherSeeded otherLater otherSaved otherCall
                obtain ⟨rfl, rfl⟩ := seeded.unique otherSeeded
                obtain ⟨sameAnswer, sameLater, sameSaved⟩ := SourceCurrentConjunctionCallUnique.call decision otherCall
                exact ⟨sameAnswer, sameLater.symm, sameSaved.symm⟩
              cases answer with
              | false =>
                  obtain ⟨outcome, selected, after, saved, next, rest⟩ := ih (alphabet := nextPlan.1) (before := advancePhysical middle later) (memo := savedMemo)
                    (inventory := queryInventory) (profile := nextPlan.2) finalFrame memoFits memoValues memoCorrect memoKnown
                    tailProper reserved.2 queryMemos memoValid
                  refine ⟨outcome, selected, after, saved, next, .continued primary secondary seeded decision rest.actual, ?_,
                    rest.frame, rest.fits, rest.carrier,
                    firstEffects.trans (secondEffects.trans (receipt.effects.trans (memoEffects.trans rest.effects))),
                    rest.available, rest.correct, (fun key entry found => rest.retained key entry (retained key entry found)), ?_⟩
                  · refine ⟨?_, ?_, ?_⟩
                    · intro other actual
                      have impossible := (EndpointStatefulGateTrace.class_trace_unique source reaches values paths
                        before.native.machine.heap true false heap other primary actual).1
                      cases impossible
                    · intro other actual nextAnchor otherSecondary
                      obtain ⟨_same, rfl⟩ := EndpointStatefulGateTrace.class_trace_unique source reaches values paths
                        before.native.machine.heap true true heap other primary actual
                      have impossible := (SourceCurrentSecondaryTrace.class_trace_unique source values paths heap
                        false true anchor nextAnchor secondary otherSecondary).1
                      cases impossible
                    · intro other actual nextAnchor otherSecondary
                      have aligned := actualRanges other actual nextAnchor otherSecondary
                      refine ⟨aligned.1, ?_⟩
                      intro otherQuery otherMiddle otherSeeded otherLater otherSaved otherCall
                      obtain ⟨rfl, rfl⟩ := seeded.unique (by
                        obtain ⟨_same, rfl⟩ := EndpointStatefulGateTrace.class_trace_unique source reaches values paths
                          before.native.machine.heap true true heap other primary actual
                        obtain ⟨_same, rfl⟩ := SourceCurrentSecondaryTrace.class_trace_unique source values paths heap
                          false false anchor nextAnchor secondary otherSecondary
                        exact otherSeeded)
                      obtain ⟨_same, rfl, rfl⟩ := SourceCurrentConjunctionCallUnique.call decision otherCall
                      exact rest.ranges
                  · intro g s p h n enoughG enoughS enoughP enoughH enoughN
                    have first := firstDone g (Nat.le_trans (Nat.le_trans limits.1 localFuel) enoughG)
                    have second := secondDone s (Nat.le_trans (Nat.le_trans limits.2.1 localFuel) enoughS)
                    have queryAt := queryStable p h n (Nat.le_trans (Nat.le_trans limits.2.2.1 localFuel) enoughP)
                      (Nat.le_trans (Nat.le_trans limits.2.2.1 localFuel) enoughH) (Nat.le_trans (Nat.le_trans limits.2.2.1 localFuel) enoughN)
                    have memoAt := SourceCurrentAllocatedConjunctionWorker.call_lift
                      (memoDone p h (Nat.le_trans (Nat.le_trans limits.2.2.2.1 localFuel) enoughP)
                        (Nat.le_trans (Nat.le_trans limits.2.2.2.2 localFuel) enoughH))
                    have tail := rest.run g s p h n (Nat.le_trans tailFuel enoughG) (Nat.le_trans tailFuel enoughS)
                      (Nat.le_trans tailFuel enoughP) (Nat.le_trans tailFuel enoughH) (Nat.le_trans tailFuel enoughN)
                    simp [SourceCurrentAllocatedScanWorker.scan, SourceCurrentAllocatedScanWorker.gate,
                      SourceCurrentAllocatedGateWorker.primary, SourceCurrentAllocatedGateWorker.secondary, first, second,
                      SourceCurrentAllocatedGateWorker.lift, SourceCurrentAllocatedScanWorker.query, queryAt,
                      SourceCurrentAllocatedScanWorker.decision, memoAt, SourceCurrentAllocatedScanWorker.Outcome.bind, tail]
              | true =>
                  refine ⟨some paths, [], advancePhysical middle later, savedMemo, queryInventory,
                    .stopped primary secondary seeded decision, ?_, finalFrame,
                    memoFits.mono (SourceCurrentScanNumericForecast.schedule_profile_ge budget values.length classes nextPlan.1 nextPlan.2),
                    SourceCurrentNativeGuardStep.heap_mono
                      (SourceCurrentScanNumericForecast.schedule_alphabet_ge budget values.length classes nextPlan.1 nextPlan.2) memoKnown,
                    firstEffects.trans (secondEffects.trans (receipt.effects.trans memoEffects)), memoValues, memoCorrect, retained, ?_⟩
                  · refine ⟨?_, ?_, ?_⟩
                    · intro other actual
                      have impossible := (EndpointStatefulGateTrace.class_trace_unique source reaches values paths
                        before.native.machine.heap true false heap other primary actual).1
                      cases impossible
                    · intro other actual nextAnchor otherSecondary
                      obtain ⟨_same, rfl⟩ := EndpointStatefulGateTrace.class_trace_unique source reaches values paths
                        before.native.machine.heap true true heap other primary actual
                      have impossible := (SourceCurrentSecondaryTrace.class_trace_unique source values paths heap
                        false true anchor nextAnchor secondary otherSecondary).1
                      cases impossible
                    · intro other actual nextAnchor otherSecondary
                      have aligned := actualRanges other actual nextAnchor otherSecondary
                      refine ⟨aligned.1, ?_⟩
                      intro otherQuery otherMiddle otherSeeded otherLater otherSaved otherCall
                      have impossible := (aligned.2 otherQuery otherMiddle otherSeeded otherLater otherSaved otherCall).1
                      cases impossible
                  · intro g s p h n enoughG enoughS enoughP enoughH enoughN
                    have first := firstDone g (Nat.le_trans (Nat.le_trans limits.1 localFuel) enoughG)
                    have second := secondDone s (Nat.le_trans (Nat.le_trans limits.2.1 localFuel) enoughS)
                    have queryAt := queryStable p h n (Nat.le_trans (Nat.le_trans limits.2.2.1 localFuel) enoughP)
                      (Nat.le_trans (Nat.le_trans limits.2.2.1 localFuel) enoughH) (Nat.le_trans (Nat.le_trans limits.2.2.1 localFuel) enoughN)
                    have memoAt := SourceCurrentAllocatedConjunctionWorker.call_lift
                      (memoDone p h (Nat.le_trans (Nat.le_trans limits.2.2.2.1 localFuel) enoughP)
                        (Nat.le_trans (Nat.le_trans limits.2.2.2.2 localFuel) enoughH))
                    simp [SourceCurrentAllocatedScanWorker.scan, SourceCurrentAllocatedScanWorker.gate,
                      SourceCurrentAllocatedGateWorker.primary, SourceCurrentAllocatedGateWorker.secondary, first, second,
                      SourceCurrentAllocatedGateWorker.lift, SourceCurrentAllocatedScanWorker.query, queryAt,
                      SourceCurrentAllocatedScanWorker.decision, memoAt, SourceCurrentAllocatedScanWorker.Outcome.bind]

end MicroCFTA.SourceCurrentScanNumeric
