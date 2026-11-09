import MicroCFTA.SourceCurrentSharedScanCallerNumeric
import MicroCFTA.SourceCurrentSeededInitialRanges
import MicroCFTA.SourceCurrentAllocatedGateWorker
import MicroCFTA.SourceCurrentAllocatedSeededWorkerStability

/-!
# Native ranges at actual shared Scan prefixes

Each predicate follows the literal gate, query and decision outcomes.
A reached seeded query receives its range certificate before execution.
A failed query therefore retains its own entry checks. Only a successful
prefix checks the continuation at its exact returned state and memo.
-/
namespace MicroCFTA.SourceCurrentSharedScanInitialRanges
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityClassOrder (Record)
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentConjunctionClassScan (advanceHeap)
open SourceCurrentSharedScanNumericForecast (classStep Reserved)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "advance" => SourceCurrentAllocatedPartialState.advance
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
local notation "gateProfile" => SourceCurrentGateFrameResources.forecast
local notation "gate" => SourceCurrentAllocatedSharedScanWorker.gate
local notation "query" => SourceCurrentAllocatedSharedScanWorker.query
local notation "decision" => SourceCurrentAllocatedSharedScanWorker.decision
variable {bits width : Nat}

/-- A successful prefix checks its continuation at the literal checked state and fourth memo. -/
def After (observed : SourceCurrentAllocatedSharedScanWorker.Outcome A width)
    (next : A → Checked width → Fourth → Prop) : Prop :=
  match observed with
  | .done value after saved => next value after saved
  | .failed _ _ _ => True

/-- A supplied success exposes the range check at its own returned prefix. -/
theorem after_of_done {observed : SourceCurrentAllocatedSharedScanWorker.Outcome A width}
    {next : A → Checked width → Fourth → Prop} {value : A} {after : Checked width} {saved : Fourth}
    (checked : After observed next) (actual : observed = .done value after saved) :
    next value after saved := by
  simpa only [actual, After] using checked

private theorem after_intro {observed : SourceCurrentAllocatedSharedScanWorker.Outcome A width}
    {next : A → Checked width → Fourth → Prop}
    (checked : ∀ value after saved, observed = .done value after saved → next value after saved) :
    After observed next := by
  cases observed with
  | done value after saved => exact checked value after saved rfl
  | failed => trivial

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- Only reached seeded queries need native words; each continuation follows the actual observation. -/
noncomputable def Ranges (g s p h n budget : Nat) (values : List Node) :
    List Record → Checked width → Fourth → Prop
  | [], _, _ => True
  | record :: records, before, memo =>
      After (gate true g values record.paths before memo) fun primary middle current =>
        if primary then
          After (gate false s values record.paths middle current) fun secondary later saved =>
            if secondary then Ranges g s p h n budget values records later saved
            else SourceCurrentAllocatedSeededQuery.SeededRanges values
                (record.paths.map (List.map Int.ofNat)) later ∧
              After (query p h n values record.paths later saved) fun value checked fourth =>
                After (decision p h budget record.paths value checked fourth) fun answer after final =>
                  if answer then True else Ranges g s p h n budget values records after final
        else Ranges g s p h n budget values records middle current

omit [DecidableEq Symbol] [DecidableEq Node] in
private theorem primary_done {g : Nat} {values : List Node} {paths : Class}
    {before after : Checked width} {memo saved : Fourth} {answer : Bool}
    (actual : gate true g values paths before memo = .done answer after saved) :
    saved = memo ∧ SourceCurrentAllocatedGateWorker.primary g values paths before = .done answer after := by
  cases observed : SourceCurrentAllocatedGateWorker.primary g values paths before with
  | done value checked =>
      simp only [SourceCurrentAllocatedSharedScanWorker.gate, ite_true, observed] at actual
      cases actual
      exact ⟨rfl, rfl⟩
  | failed =>
      simp only [SourceCurrentAllocatedSharedScanWorker.gate, ite_true, observed] at actual
      cases actual

omit [DecidableEq Symbol] [DecidableEq Node] in
private theorem secondary_done {s : Nat} {values : List Node} {paths : Class}
    {before after : Checked width} {memo saved : Fourth} {answer : Bool}
    (actual : gate false s values paths before memo = .done answer after saved) :
    saved = memo ∧ SourceCurrentAllocatedGateWorker.secondary s values paths before = .done answer after := by
  cases observed : SourceCurrentAllocatedGateWorker.secondary s values paths before with
  | done value checked =>
      simp only [SourceCurrentAllocatedSharedScanWorker.gate, Bool.false_eq_true, ite_false, observed] at actual
      cases actual
      exact ⟨rfl, rfl⟩
  | failed =>
      simp only [SourceCurrentAllocatedSharedScanWorker.gate, Bool.false_eq_true, ite_false, observed] at actual
      cases actual

omit [DecidableEq Node] in
private theorem query_done {p h n : Nat} {values : List Node} {paths : Class}
    {before after : Checked width} {memo saved : Fourth} {value : Node}
    (actual : query p h n values paths before memo = .done value after saved) :
    saved = memo ∧ SourceCurrentAllocatedSeededWorker.seeded p h n values
      (paths.map (List.map Int.ofNat)) before = .done value after := by
  cases observed : SourceCurrentAllocatedSeededWorker.seeded p h n values
      (paths.map (List.map Int.ofNat)) before with
  | done result checked =>
      simp only [SourceCurrentAllocatedSharedScanWorker.query, observed] at actual
      cases actual
      exact ⟨rfl, rfl⟩
  | failed =>
      simp only [SourceCurrentAllocatedSharedScanWorker.query, observed] at actual
      cases actual

omit [DecidableEq Symbol] [DecidableEq Node] in
private theorem primary_resources (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) {inventory : Inventory} {alphabet : List Guard}
    {g : Nat} {values : List Node} {paths : Class} {before : Caller width} {memos : Memos}
    {answer : Bool} {after : Checked width}
    (actual : SourceCurrentAllocatedGateWorker.primary g values paths before.checked = .done answer after)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (available : Values before.checked.native.machine.heap values)
    (known : Heap (fun guard => guard ∈ alphabet) before.checked.native.machine.heap) :
    ∃ final, Post formulas solver inventory before (advance before after before.fourth before.merge) final ∧
      Frame formulas solver inventory after ∧ Fits (gateProfile paths profile) after ∧
      Values after.native.machine.heap values ∧ Heap (fun guard => guard ∈ alphabet) after.native.machine.heap := by
  have given := SourceCurrentAllocatedGateWorker.primary_graph actual
  have same := (SourceCurrentAllocatedGateWorker.primary_done actual).2
  obtain ⟨computed, heap, trace, returned, bounded, resident, _effects, _run⟩ :=
    SourceCurrentGateFrameResources.primary formulas solver inventory source reaches values paths
      before.checked frame profile fits available
  obtain ⟨rfl, rfl⟩ := EndpointStatefulGateTrace.class_trace_unique source reaches values paths
    before.checked.native.machine.heap computed answer heap after.native.machine.heap trace given
  obtain ⟨final, _reads, post⟩ := SourceCurrentSharedScanCallerSteps.primary_post formulas solver given initial available
  refine ⟨final, ?_, ?_, ?_, resident, ?_⟩
  · simpa only [← same] using post
  · simpa only [← same] using returned
  · simpa only [← same] using bounded
  · exact (SourcePrimaryGateEffects.class_effects (fun guard => guard ∈ alphabet)
      source reaches given frame.ready.semantic frame.ready.costs available known).2.2.2

omit [DecidableEq Symbol] [DecidableEq Node] in
private theorem secondary_resources (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) {inventory : Inventory} {alphabet : List Guard}
    {s : Nat} {values : List Node} {paths : Class} {before : Caller width} {memos : Memos}
    {answer : Bool} {after : Checked width}
    (actual : SourceCurrentAllocatedGateWorker.secondary s values paths before.checked = .done answer after)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (available : Values before.checked.native.machine.heap values)
    (known : Heap (fun guard => guard ∈ alphabet) before.checked.native.machine.heap) :
    ∃ final, Post formulas solver inventory before (advance before after before.fourth before.merge) final ∧
      Frame formulas solver inventory after ∧ Fits (gateProfile paths profile) after ∧
      Values after.native.machine.heap values ∧ Heap (fun guard => guard ∈ alphabet) after.native.machine.heap := by
  have given := SourceCurrentAllocatedGateWorker.secondary_graph actual
  have same := (SourceCurrentAllocatedGateWorker.secondary_done actual).2
  obtain ⟨computed, heap, trace, returned, bounded, resident, _effects, _run⟩ :=
    SourceCurrentGateFrameResources.secondary formulas solver inventory source reaches values paths
      before.checked frame profile fits available
  obtain ⟨rfl, rfl⟩ := SourceCurrentSecondaryTrace.class_trace_unique source values paths
    before.checked.native.machine.heap computed answer heap after.native.machine.heap trace given
  obtain ⟨final, _reads, post⟩ := SourceCurrentSharedScanCallerSteps.secondary_post formulas solver given initial available
  refine ⟨final, ?_, ?_, ?_, resident, ?_⟩
  · simpa only [← same] using post
  · simpa only [← same] using returned
  · simpa only [← same] using bounded
  · exact (SourceCurrentSecondaryEffects.class_effects (fun guard => guard ∈ alphabet)
      source given frame.ready.semantic frame.ready.costs available known).2.2.2

private theorem call_carrier (annotation : Guard → Prop) {p h budget : Nat} {queryValue : Node}
    {before after : Checked width} {memo saved : Fourth}
    {snapshot : SourceCurrentConjunctionSharedWorklistStep.State Symbol FullSyntax.Formula} {answer : Bool}
    (actual : SourceCurrentAllocatedSharedConjunctionWorker.call p h budget queryValue before memo =
      .done answer after saved snapshot)
    (ready : SourceCurrentConjunctionRowsAllocation.Ready (physical before))
    (known : Heap annotation before.native.machine.heap) (available : Available before.native.machine.heap queryValue) :
    Heap annotation after.native.machine.heap := by
  obtain ⟨raw, reached⟩ := SourceCurrentAllocatedSharedConjunctionWorker.call_done actual
  have preserved := SourceCurrentConjunctionSharedWorkerAnnotations.call_heap annotation p h budget memo queryValue
    (physical before) ready known available
  rw [raw] at preserved
  dsimp only [SourceCurrentConjunctionSharedWorker.Outcome.state] at preserved
  rw [reached]
  exact preserved

/-- Current reservations derive checks before every actual seeded query at all five Scan bounds. -/
theorem initial_ranges (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory) (alphabet : List Guard)
    (budget : Nat) (values : List Node) (records : List Record) (before : Caller (bits + 2)) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (available : Values before.checked.native.machine.heap values)
    (proper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [])
    (reserved : Reserved bits budget values.length (records.map Record.paths) alphabet profile)
    (known : Heap (fun guard => guard ∈ alphabet) before.checked.native.machine.heap) :
    ∀ g s p h n, Ranges g s p h n budget values records before.checked before.fourth := by
  induction records generalizing inventory alphabet before memos profile with
  | nil => intros; trivial
  | cons record records ih =>
      intro g s p h n
      have tailProper : ∀ other ∈ records, ∀ path ∈ other.paths, path ≠ [] :=
        fun other member => proper other (List.mem_cons_of_mem _ member)
      let nextPlan := classStep budget values.length record.paths alphabet profile
      change After (gate true g values record.paths before.checked before.fourth) _
      apply after_intro
      intro first middle current firstActual
      obtain ⟨rfl, primary⟩ := primary_done firstActual
      obtain ⟨firstMemos, firstPost, firstFrame, firstFits, firstValues, firstKnown⟩ :=
        primary_resources formulas solver primary initial frame profile fits available known
      let firstCaller := advance before middle before.fourth before.merge
      cases first with
      | false =>
          change Ranges g s p h n budget values records middle before.fourth
          exact ih (inventory := inventory) (alphabet := nextPlan.1) (before := firstCaller)
            (memos := firstMemos) (profile := nextPlan.2) firstPost.context firstFrame
            (firstFits.mono (SourceCurrentSharedScanNumericForecast.classStep_primary_ge _ _ _ _ _))
            firstValues tailProper reserved.2 (SourceCurrentNativeGuardStep.heap_mono
              (SourceCurrentSharedScanNumericForecast.classStep_alphabet_ge budget values.length record.paths alphabet profile)
              firstKnown) g s p h n
      | true =>
          change After (gate false s values record.paths middle before.fourth) _
          apply after_intro
          intro second later saved secondActual
          obtain ⟨rfl, secondary⟩ := secondary_done secondActual
          obtain ⟨secondMemos, secondPost, secondFrame, secondFits, secondValues, secondKnown⟩ :=
            secondary_resources formulas solver secondary firstPost.context firstFrame
              (gateProfile record.paths profile) firstFits firstValues firstKnown
          let secondCaller := advance firstCaller later firstCaller.fourth firstCaller.merge
          cases second with
          | true =>
              change Ranges g s p h n budget values records later before.fourth
              exact ih (inventory := inventory) (alphabet := nextPlan.1) (before := secondCaller)
                (memos := secondMemos) (profile := nextPlan.2) secondPost.context secondFrame
                (secondFits.mono (SourceCurrentSharedScanNumericForecast.classStep_secondary_ge _ _ _ _ _))
                secondValues tailProper reserved.2 (SourceCurrentNativeGuardStep.heap_mono
                  (SourceCurrentSharedScanNumericForecast.classStep_alphabet_ge budget values.length record.paths alphabet profile)
                  secondKnown) g s p h n
          | false =>
              change SourceCurrentAllocatedSeededQuery.SeededRanges values
                  (record.paths.map (List.map Int.ofNat)) later ∧ After (query p h n values record.paths later before.fourth) _
              have support := SourceCurrentSecondarySeededSupport.class_support source
                (SourceCurrentAllocatedGateWorker.secondary_graph secondary) firstFrame.ready.semantic
                firstFrame.ready.costs firstValues (proper record List.mem_cons_self)
              have signedProper := SourceCurrentSecondarySeededSupport.mapped_proper (proper record List.mem_cons_self)
              have ranges := SourceCurrentSeededInitialRanges.complete formulas solver inventory source
                later.native.machine.heap support.1 support.2.2.1 values (record.paths.map (List.map Int.ofNat))
                secondCaller.checked (gateProfile record.paths (gateProfile record.paths profile))
                secondFrame secondFits secondValues (grows_refl _) support.2.2.2.2.2.2 signedProper
                reserved.1 secondMemos secondPost.context.globals
              refine ⟨ranges, ?_⟩
              apply after_intro
              intro node checked fourth queryActual
              obtain ⟨rfl, queried⟩ := query_done queryActual
              obtain ⟨computed, reached, queryInventory, queryMemos, _trace, _reads, queryReceipt,
                  queryFits, _included, queryDone, queryKnown⟩ :=
                SourceCurrentSeededGuardNumeric.complete alphabet formulas solver inventory source
                  later.native.machine.heap support.1 support.2.2.1 values (record.paths.map (List.map Int.ofNat))
                  secondCaller.checked (gateProfile record.paths (gateProfile record.paths profile))
                  secondFrame secondFits secondValues (grows_refl _) support.2.2.2.2.2.2 signedProper
                  reserved.1 secondKnown secondMemos secondPost.context.globals
              have same := SourceCurrentAllocatedSeededWorkerStability.seeded_done_unique queryDone queried
              have canonicalPost := SourceCurrentSeededCallerNumeric.of_receipt formulas solver secondPost.context queryReceipt
              have queryPost : Post formulas solver queryInventory secondCaller
                  (advance secondCaller checked secondCaller.fourth secondCaller.merge) queryMemos := by
                simpa only [same.2] using canonicalPost
              have queryFrame : Frame formulas solver queryInventory checked := by
                simpa only [same.2] using queryReceipt.frame
              have nodeAvailable : Available checked.native.machine.heap node := by
                simpa only [same.1, same.2] using queryReceipt.available
              let nativeProfile := SourceCurrentConstrainedCapSeededForecast.finalProfile values.length
                (record.paths.map (List.map Int.ofNat)) (gateProfile record.paths (gateProfile record.paths profile))
              have nativeFits : Fits nativeProfile checked := by
                simpa only [same.2] using queryFits
              have nativeKnown : Heap (fun guard => guard ∈ nextPlan.1) checked.native.machine.heap := by
                simpa only [same.2, nextPlan, SourceCurrentSharedScanNumericForecast.classStep] using queryKnown
              let queryCaller := advance secondCaller checked secondCaller.fourth secondCaller.merge
              change After (decision p h budget record.paths node checked before.fourth) _
              apply after_intro
              intro answer after final decisionActual
              obtain ⟨snapshot, called⟩ := SourceCurrentAllocatedSharedScanWorker.decision_done decisionActual
              obtain ⟨decisionMemos, _advanced, _calls, callPost, _sound, _resident,
                  _unfolding, _querySame, memoFits, _stable⟩ :=
                SourceCurrentAllocatedSharedConjunctionWorkerActual.raw_done_resources_with_alphabet formulas solver
                  nextPlan.1 nativeProfile queryPost.context nativeFits nodeAvailable nativeKnown called
              have finalFrame := SourceCurrentSharedConjunctionCallerNumeric.of_call formulas solver called queryFrame nodeAvailable
              have physicalReady := SourceCurrentAllocatedConjunctionMemo.ready checked queryFrame.ready.good
                queryFrame.ready.semantic queryFrame.ready.costs
              have finalKnown := call_carrier (fun guard => guard ∈ nextPlan.1) called physicalReady nativeKnown nodeAvailable
              have finalValues : Values after.native.machine.heap values := fun value member =>
                callPost.effects.keeps.available value (queryPost.effects.keeps.available value (secondValues value member))
              let finalCaller := advance queryCaller after final queryCaller.merge
              cases answer with
              | true => trivial
              | false =>
                  change Ranges g s p h n budget values records after final
                  exact ih (inventory := queryInventory) (alphabet := nextPlan.1) (before := finalCaller)
                    (memos := decisionMemos) (profile := nextPlan.2) callPost.context finalFrame
                    memoFits finalValues tailProper reserved.2 finalKnown g s p h n

end MicroCFTA.SourceCurrentSharedScanInitialRanges
