import MicroCFTA.SourceCurrentSharedCallReadValidity
import MicroCFTA.SourceCurrentSharedScanCallerNumeric
import MicroCFTA.SourceCurrentAllocatedGateReadValidity
import MicroCFTA.SourceCurrentAllocatedSeededReadValidity
import MicroCFTA.SourceCurrentSeededInitialRanges

/-!
# Validity of the supplied shared Scan reads

The proof follows each supplied read receipt. Initial resources derive the
Frame and reservation at each reached prefix. The returned bundle belongs
to that receipt. Equality of physical endpoints does not identify bundles.
-/
namespace MicroCFTA.SourceCurrentSharedScanReadValidity
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentConjunctionClassScan (Ready advanceHeap)
open SourceCurrentSharedScanNumericForecast (classStep schedule Reserved)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "advance" => SourceCurrentAllocatedPartialState.advance
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
local notation "gateProfile" => SourceCurrentGateFrameResources.forecast
variable {bits width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

omit [DecidableEq Symbol] [DecidableEq Node] in
private theorem gate_post {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    {before : Caller width} {heap : State Symbol Guard} {memos final : Memos}
    (initial : Context formulas solver inventory before memos)
    (ready : Ready (advanceHeap before.checked heap))
    (effects : SourceCurrentConjunctionRowsAllocation.Effects
      (physical before.checked) (physical (advanceHeap before.checked heap)))
    (valid : Valid heap final) (probes : InternedFreshOrdinaryProbeHeap.Heap heap) :
    Post formulas solver inventory before
      (advance before (advanceHeap before.checked heap) before.fourth before.merge) final := by
  have admitted := initial.admitted.advance ⟨heap, before.checked.operations⟩
    (SourceCurrentAllocatedQueryMemo.advance_extension before.checked _ effects)
  exact ⟨⟨ready, admitted, initial.sound.advance formulas solver _ before.fourth before.merge effects,
    initial.stored.grows effects.keeps, initial.covered,
    SourceCurrentEmptinessMemo.grows formulas solver effects.keeps before.fourth initial.correct,
    valid, probes⟩, effects, extends_refl _, fun _ _ found => found⟩

omit [DecidableEq Symbol] [DecidableEq Node] in
private theorem primary (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) {inventory : Inventory}
    {before : Caller width} {memos final : Memos} {values : List Node} {paths : Class}
    {answer : Bool} {heap : State Symbol Guard}
    {actual : EndpointStatefulGateTrace.ClassTrace source reaches values paths before.checked.native.machine.heap answer heap}
    (reads : SourceCurrentAllocatedPrimaryReads.ClassReads actual memos final)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (available : Values before.checked.native.machine.heap values) :
    Post formulas solver inventory before (advance before (advanceHeap before.checked heap) before.fourth before.merge) final ∧
      Frame formulas solver inventory (advanceHeap before.checked heap) ∧
      Fits (gateProfile paths profile) (advanceHeap before.checked heap) ∧ Values heap values := by
  obtain ⟨computed, reached, trace, returned, bounded, resident, effects, _run⟩ :=
    SourceCurrentGateFrameResources.primary formulas solver inventory source reaches values paths before.checked frame profile fits available
  obtain ⟨rfl, rfl⟩ := EndpointStatefulGateTrace.class_trace_unique source reaches values paths
    before.checked.native.machine.heap computed answer reached heap trace actual
  have kept := SourceCurrentAllocatedGateReadValidity.primary_class reads
    (SourceCurrentClassGateCompletion.gate_ready initial.ready.semantic initial.ready.costs) available initial.globals
  have probes := (SourceCurrentAllocatedProbeGates.Primary.class_effects source reaches actual
    initial.ready.semantic initial.ready.costs available initial.probes).2.2.2
  exact ⟨gate_post initial returned.ready effects kept.valid probes, returned, bounded, resident⟩

omit [DecidableEq Symbol] [DecidableEq Node] in
private theorem secondary (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) {inventory : Inventory}
    {before : Caller width} {memos final : Memos} {values : List Node} {paths : Class}
    {answer : Bool} {heap : State Symbol Guard}
    {actual : SourceCurrentSecondaryTrace.ClassTrace source values paths before.checked.native.machine.heap answer heap}
    (reads : SourceCurrentSecondaryMemos.ClassReads actual memos final)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (available : Values before.checked.native.machine.heap values) :
    Post formulas solver inventory before (advance before (advanceHeap before.checked heap) before.fourth before.merge) final ∧
      Frame formulas solver inventory (advanceHeap before.checked heap) ∧
      Fits (gateProfile paths profile) (advanceHeap before.checked heap) ∧ Values heap values := by
  obtain ⟨computed, reached, trace, returned, bounded, resident, effects, _run⟩ :=
    SourceCurrentGateFrameResources.secondary formulas solver inventory source reaches values paths before.checked frame profile fits available
  obtain ⟨rfl, rfl⟩ := SourceCurrentSecondaryTrace.class_trace_unique source values paths
    before.checked.native.machine.heap computed answer reached heap trace actual
  have kept := SourceCurrentAllocatedGateReadValidity.secondary_class reads
    (SourceCurrentClassGateCompletion.gate_ready initial.ready.semantic initial.ready.costs) available initial.globals
  have probes := (SourceCurrentAllocatedProbeGates.Secondary.class_effects source actual
    initial.ready.semantic initial.ready.costs available initial.probes).2.2.2
  exact ⟨gate_post initial returned.ready effects kept.valid probes, returned, bounded, resident⟩

private structure Result (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (alphabet : List Guard) (profile : Profile)
    (before : Caller width) (memos : Memos) (values : List Node) (after : Checked width)
    (saved : Fourth) (next : Inventory) (final : Memos) : Prop where
  post : Post formulas solver next before (advance before after saved before.merge) final
  frame : Frame formulas solver next after
  fits : Fits profile after
  carrier : Heap (fun guard => guard ∈ alphabet) after.native.machine.heap
  available : Values after.native.machine.heap values

private theorem query (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (alphabet : List Guard) (profile : Profile) (budget : Nat)
    (values : List Node) (paths : Class) (before : Caller (bits + 2)) (memos : Memos)
    (initial : Context formulas solver inventory before memos) (frame : Frame formulas solver inventory before.checked)
    (fits : Fits profile before.checked) (available : Values before.checked.native.machine.heap values)
    (proper : ∀ path ∈ paths, path ≠ [])
    (reserved : SourceCurrentConstrainedCapSeededForecast.SeededReserved bits values.length
      (paths.map (List.map Int.ofNat)) (gateProfile paths (gateProfile paths profile)))
    (known : Heap (fun guard => guard ∈ alphabet) before.checked.native.machine.heap)
    {heap anchor : State Symbol Guard} {middle later : Checked (bits + 2)} {saved : Fourth}
    {node : Node} {p h : Nat} {snapshot : SourceCurrentConjunctionSharedWorklistStep.State Symbol FullSyntax.Formula}
    {first second queried final : Memos} {answer : Bool}
    {primaryTrace : EndpointStatefulGateTrace.ClassTrace source reaches values paths before.checked.native.machine.heap true heap}
    {secondaryTrace : SourceCurrentSecondaryTrace.ClassTrace source values paths heap false anchor}
    {seeded : SourceCurrentAllocatedSeededQuery.Seeded values (paths.map (List.map Int.ofNat))
      (advanceHeap (advanceHeap before.checked heap) anchor) node middle}
    (firstRead : SourceCurrentAllocatedPrimaryReads.ClassReads primaryTrace memos first)
    (secondRead : SourceCurrentSecondaryMemos.ClassReads secondaryTrace first second)
    (seededRead : SourceCurrentAllocatedSeededMemos.SeededReads seeded second queried)
    (called : SourceCurrentAllocatedSharedConjunctionWorker.call p h budget node middle before.fourth = .done answer later saved snapshot)
    (callRead : SourceCurrentConjunctionSharedWorkerOutcomeMemos.CallReads p h budget before.fourth node (physical middle) queried final) :
    ∃ next, Result formulas solver (classStep budget values.length paths alphabet profile).1
      (classStep budget values.length paths alphabet profile).2 before memos values later saved next final := by
  obtain ⟨firstPost, firstFrame, firstFits, firstValues⟩ := primary formulas solver firstRead initial frame profile fits available
  let firstCaller := advance before (advanceHeap before.checked heap) before.fourth before.merge
  obtain ⟨secondPost, secondFrame, secondFits, secondValues⟩ :=
    secondary formulas solver secondRead firstPost.context firstFrame (gateProfile paths profile) firstFits firstValues
  let secondCaller := advance firstCaller (advanceHeap firstCaller.checked anchor) firstCaller.fourth firstCaller.merge
  have firstKnown := (SourcePrimaryGateEffects.class_effects (fun guard => guard ∈ alphabet)
    source reaches primaryTrace frame.ready.semantic frame.ready.costs available known).2.2.2
  have secondKnown := (SourceCurrentSecondaryEffects.class_effects (fun guard => guard ∈ alphabet)
    source secondaryTrace firstFrame.ready.semantic firstFrame.ready.costs firstValues firstKnown).2.2.2
  have support := SourceCurrentSecondarySeededSupport.class_support source secondaryTrace firstFrame.ready.semantic
    firstFrame.ready.costs firstValues proper
  have signedProper := SourceCurrentSecondarySeededSupport.mapped_proper proper
  obtain ⟨computed, reached, next, _canonicalFinal, trace, _canonicalReads, receipt, queryFits, _included, _done, queryKnown⟩ :=
    SourceCurrentSeededGuardNumeric.complete alphabet formulas solver inventory source anchor support.1 support.2.2.1
      values (paths.map (List.map Int.ofNat)) secondCaller.checked
      (gateProfile paths (gateProfile paths profile)) secondFrame secondFits secondValues (grows_refl _)
      support.2.2.2.2.2.2 signedProper reserved secondKnown second secondPost.context.globals
  obtain ⟨sameNode, sameState⟩ := trace.unique seeded
  subst computed reached
  have ranges := SourceCurrentSeededInitialRanges.complete formulas solver inventory source anchor support.1 support.2.2.1
    values (paths.map (List.map Int.ofNat)) secondCaller.checked
    (gateProfile paths (gateProfile paths profile)) secondFrame secondFits secondValues (grows_refl _)
    support.2.2.2.2.2.2 signedProper reserved second secondPost.context.globals
  have given := SourceCurrentAllocatedSeededReadValidity.seeded source anchor support.1 support.2.2.1 seededRead
    ranges secondFrame.ready.good
    (SourceCurrentAllocatedConjunctionMemo.ready secondCaller.checked secondFrame.ready.good secondFrame.ready.semantic secondFrame.ready.costs)
    secondFrame.ready.scopedCache secondFrame.ready.idle secondValues (grows_refl _) support.2.2.2.2.2.2 secondPost.context.globals
  have queryReceipt : SourceCurrentConstrainedCapSeededNumeric.Receipt formulas solver next secondCaller.checked node middle second queried :=
    ⟨receipt.frame, receipt.effects, receipt.extension, receipt.available, receipt.closed,
      ⟨receipt.effects.keeps, receipt.frame.ready.semantic, receipt.frame.ready.costs, given.1, given.2.1, given.2.2⟩,
      receipt.probes⟩
  have queryPost := SourceCurrentSeededCallerNumeric.of_receipt formulas solver secondPost.context queryReceipt
  let queryCaller := advance secondCaller middle before.fourth before.merge
  let nextPlan := classStep budget values.length paths alphabet profile
  let nativeProfile := SourceCurrentConstrainedCapSeededForecast.finalProfile values.length
    (paths.map (List.map Int.ofNat)) (gateProfile paths (gateProfile paths profile))
  obtain ⟨_canonical, advanced, _canonicalCalls, canonicalPost, _sound, _resident, _retained, _same, memoFits, _stable⟩ :=
    SourceCurrentAllocatedSharedConjunctionWorkerActual.raw_done_resources_with_alphabet formulas solver
      nextPlan.1 nativeProfile queryPost.context queryFits receipt.available queryKnown called
  have physicalReady := SourceCurrentAllocatedConjunctionMemo.ready middle receipt.frame.ready.good
    receipt.frame.ready.semantic receipt.frame.ready.costs
  have coherent := SourceCurrentSharedCallReadValidity.call p h budget before.fourth node (physical middle)
    physicalReady receipt.available queryPost.context.globals callRead
  obtain ⟨rawCall, _physical⟩ := SourceCurrentAllocatedSharedConjunctionWorker.call_done called
  rw [rawCall] at coherent
  dsimp only [SourceCurrentConjunctionSharedWorker.Outcome.state] at coherent
  have givenValid : Valid later.native.machine.heap final := by
    simpa only [advanced, SourceCurrentAllocatedQueryMemo.advancePhysical, SourceRecursiveIntersectionThunks.advance] using coherent
  have callPost : Post formulas solver next queryCaller (advance queryCaller later saved queryCaller.merge) final :=
    ⟨⟨canonicalPost.context.ready, canonicalPost.context.admitted, canonicalPost.context.sound,
      canonicalPost.context.stored, canonicalPost.context.covered, canonicalPost.context.correct,
      givenValid, canonicalPost.context.probes⟩, canonicalPost.effects, canonicalPost.retained, canonicalPost.fourthRetained⟩
  have finalFrame := SourceCurrentSharedConjunctionCallerNumeric.of_call formulas solver called receipt.frame receipt.available
  have heapKnown := SourceCurrentConjunctionSharedWorkerAnnotations.call_heap (fun guard => guard ∈ nextPlan.1)
    p h budget before.fourth node (physical middle) physicalReady queryKnown receipt.available
  rw [rawCall] at heapKnown
  dsimp only [SourceCurrentConjunctionSharedWorker.Outcome.state] at heapKnown
  have memoKnown : Heap (fun guard => guard ∈ nextPlan.1) later.native.machine.heap := by
    simpa only [advanced, SourceCurrentAllocatedQueryMemo.advancePhysical, SourceRecursiveIntersectionThunks.advance] using heapKnown
  exact ⟨next, firstPost.trans (secondPost.trans (queryPost.trans callPost)), finalFrame, memoFits, memoKnown,
    fun value member => callPost.effects.keeps.available value
      (receipt.effects.keeps.available value (secondValues value member))⟩

private theorem checked (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (alphabet : List Guard) (profile : Profile) (budget : Nat)
    (values : List Node) (records : List SourceEqualityClassOrder.Record)
    (before : Caller (bits + 2)) (memos : Memos)
    (initial : Context formulas solver inventory before memos) (frame : Frame formulas solver inventory before.checked)
    (fits : Fits profile before.checked) (available : Values before.checked.native.machine.heap values)
    (proper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [])
    (reserved : Reserved bits budget values.length (records.map SourceEqualityClassOrder.Record.paths) alphabet profile)
    (known : Heap (fun guard => guard ∈ alphabet) before.checked.native.machine.heap)
    {outcome : Option Class} {kept : List SourceEqualityClassOrder.Record} {after : Checked (bits + 2)}
    {saved : Fourth} {final : Memos}
    (reads : SourceCurrentSharedScanCallerNumeric.ScanReads budget values records before.checked before.fourth outcome kept after saved memos final) :
    ∃ next, Result formulas solver
      (schedule budget values.length (records.map SourceEqualityClassOrder.Record.paths) alphabet profile).1
      (schedule budget values.length (records.map SourceEqualityClassOrder.Record.paths) alphabet profile).2
      before memos values after saved next final := by
  induction records generalizing before memos inventory alphabet profile after saved outcome kept final with
  | nil =>
      cases reads
      exact ⟨inventory,
        Post.rebase initial rfl rfl rfl
          (initial.sound.advance formulas solver _ before.fourth before.merge
            (.refl _ (SourceCurrentAllocatedConjunctionMemo.ready before.checked initial.ready.good initial.ready.semantic initial.ready.costs))),
        frame, fits, known, available⟩
  | cons record records ih =>
      have tailProper : ∀ other ∈ records, ∀ path ∈ other.paths, path ≠ [] :=
        fun other member => proper other (List.mem_cons_of_mem _ member)
      have widen := SourceCurrentSharedScanNumericForecast.classStep_alphabet_ge budget values.length record.paths alphabet profile
      cases reads with
      | selected first tail =>
          obtain ⟨post, returned, bounded, resident⟩ := primary formulas solver first initial frame profile fits available
          have carrier := (SourcePrimaryGateEffects.class_effects (fun guard => guard ∈ alphabet)
            source reaches (by assumption) frame.ready.semantic frame.ready.costs available known).2.2.2
          obtain ⟨next, rest⟩ := ih (inventory := inventory) (alphabet := (classStep budget values.length record.paths alphabet profile).1)
            (profile := (classStep budget values.length record.paths alphabet profile).2) (before := _) (memos := _) post.context returned
            (bounded.mono (SourceCurrentSharedScanNumericForecast.classStep_primary_ge _ _ _ _ _)) resident tailProper
            reserved.2 (SourceCurrentNativeGuardStep.heap_mono widen carrier) tail
          exact ⟨next, post.trans rest.post, rest.frame, rest.fits, rest.carrier, rest.available⟩
      | skipped first second tail =>
          obtain ⟨post, returned, bounded, resident⟩ := primary formulas solver first initial frame profile fits available
          obtain ⟨post2, returned2, bounded2, resident2⟩ :=
            secondary formulas solver second post.context returned (gateProfile record.paths profile) bounded resident
          have carrier := (SourcePrimaryGateEffects.class_effects (fun guard => guard ∈ alphabet)
            source reaches (by assumption) frame.ready.semantic frame.ready.costs available known).2.2.2
          have carrier2 := (SourceCurrentSecondaryEffects.class_effects (fun guard => guard ∈ alphabet)
            source (by assumption) returned.ready.semantic returned.ready.costs resident carrier).2.2.2
          obtain ⟨next, rest⟩ := ih (inventory := inventory) (alphabet := (classStep budget values.length record.paths alphabet profile).1)
            (profile := (classStep budget values.length record.paths alphabet profile).2) (before := _) (memos := _) post2.context returned2
            (bounded2.mono (SourceCurrentSharedScanNumericForecast.classStep_secondary_ge _ _ _ _ _)) resident2 tailProper
            reserved.2 (SourceCurrentNativeGuardStep.heap_mono widen carrier2) tail
          exact ⟨next, post.trans (post2.trans rest.post), rest.frame, rest.fits, rest.carrier, rest.available⟩
      | continued first second seeded called calls tail =>
          obtain ⟨next, result⟩ := query formulas solver inventory alphabet profile budget values record.paths before memos
            initial frame fits available (proper record List.mem_cons_self) reserved.1 known first second seeded called calls
          obtain ⟨last, rest⟩ := ih (inventory := next) (alphabet := (classStep budget values.length record.paths alphabet profile).1)
            (profile := (classStep budget values.length record.paths alphabet profile).2) (before := _) (memos := _) result.post.context result.frame result.fits
            result.available tailProper reserved.2 result.carrier tail
          exact ⟨last, result.post.trans rest.post, rest.frame, rest.fits, rest.carrier, rest.available⟩
      | stopped first second seeded called calls =>
          obtain ⟨next, result⟩ := query formulas solver inventory alphabet profile budget values record.paths before memos
            initial frame fits available (proper record List.mem_cons_self) reserved.1 known first second seeded called calls
          exact ⟨next, result.post, result.frame,
            result.fits.mono (SourceCurrentSharedScanNumericForecast.schedule_profile_ge budget values.length
              (records.map SourceEqualityClassOrder.Record.paths) _ _),
            SourceCurrentNativeGuardStep.heap_mono
              (SourceCurrentSharedScanNumericForecast.schedule_alphabet_ge budget values.length
                (records.map SourceEqualityClassOrder.Record.paths) _ _) result.carrier, result.available⟩

/-- Current resources validate the exact supplied Scan bundle at its own returned heap. -/
theorem scan (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (alphabet : List Guard) (budget : Nat) (values : List Node) (records : List SourceEqualityClassOrder.Record)
    (before : Caller (bits + 2)) (memos : Memos)
    (initial : Context formulas solver inventory before memos) (frame : Frame formulas solver inventory before.checked)
    (profile : Profile) (fits : Fits profile before.checked) (available : Values before.checked.native.machine.heap values)
    (proper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [])
    (reserved : Reserved bits budget values.length (records.map SourceEqualityClassOrder.Record.paths) alphabet profile)
    (known : Heap (fun guard => guard ∈ alphabet) before.checked.native.machine.heap)
    {outcome : Option Class} {kept : List SourceEqualityClassOrder.Record} {after : Checked (bits + 2)}
    {saved : Fourth} {final : Memos}
    (reads : SourceCurrentSharedScanCallerNumeric.ScanReads budget values records before.checked before.fourth outcome kept after saved memos final) :
    Valid after.native.machine.heap final := by
  obtain ⟨_, result⟩ := checked formulas solver inventory alphabet profile budget values records before memos
    initial frame fits available proper reserved known reads
  exact result.post.context.globals

end MicroCFTA.SourceCurrentSharedScanReadValidity
