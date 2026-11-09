import MicroCFTA.SourceCurrentSharedScanNumericForecast
import MicroCFTA.SourceCurrentSharedScanCallerSteps
import MicroCFTA.SourceCurrentSharedConjunctionCallerNumeric
import MicroCFTA.SourceCurrentSeededGuardNumeric
import MicroCFTA.SourceCurrentSeededCallerNumeric
import MicroCFTA.SourceCurrentSecondarySeededSupport
import MicroCFTA.SourceCurrentAllocatedSharedRecordScanWorker
import MicroCFTA.SourceCurrentConjunctionSharedWorkerAnnotations
import MicroCFTA.SourceCurrentConjunctionClassWitness
import MicroCFTA.SourceCurrentPrimaryReplay

/-!
# Initial resources construct actual shared record scans

The induction follows the original record list. Each visited phase passes
its exact caller and ordered memo bundle to the next phase. The initial
schedule supplies all five worker bounds. Successful replay retains the
same checked state and fourth memo. Read receipts use their actual base
bounds. No historical Demand Scan or reached-range supplier is used.
-/
namespace MicroCFTA.SourceCurrentSharedScanCallerNumeric
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityClassOrder
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentSharedScanNumericForecast (classStep schedule Reserved fuel classFuel)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Snapshot" => SourceCurrentConjunctionSharedWorklistStep.State Symbol FullSyntax.Formula
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "advance" => SourceCurrentAllocatedPartialState.advance
local notation "advanceHeap" => SourceCurrentConjunctionClassScan.advanceHeap
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
local notation "gateProfile" => SourceCurrentGateFrameResources.forecast
local notation "recordScan" => SourceCurrentAllocatedSharedRecordScanWorker.scan
local notation "checkedCall" => SourceCurrentAllocatedSharedConjunctionWorker.call
local notation "CallReads" => SourceCurrentConjunctionSharedWorkerOutcomeMemos.CallReads
variable {bits width : Nat}

/-- A stopped result refutes one literal original class for every accepted forest. -/
def StoppedSound (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (values : List Node) (records : List Record) (outcome : Option Class) : Prop :=
  ∀ paths, outcome = some paths → paths ∈ records.map Record.paths ∧ ∀ ambient symbol terms,
    All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms →
      ¬ClassSat (.node symbol terms) paths

private theorem stopped_cons {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {values : List Node}
    {record : Record} {records : List Record} {outcome : Option Class}
    (sound : StoppedSound formulas solver values records outcome) :
    StoppedSound formulas solver values (record :: records) outcome := by
  intro paths stopped
  obtain ⟨member, refused⟩ := sound paths stopped
  exact ⟨List.mem_cons_of_mem _ member, refused⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- Each successful branch retains its literal phase reads and original record occurrence. -/
inductive ScanReads (budget : Nat) (values : List Node) :
    List Record → Checked width → Memo → Option Class → List Record → Checked width → Memo → Memos → Memos → Prop where
  | nil {before : Checked width} {memo : Memo} {memos : Memos} :
      ScanReads budget values [] before memo none [] before memo memos memos
  | selected {record : Record} {records kept : List Record} {before after : Checked width}
      {heap : State Symbol Guard} {memo saved : Memo} {outcome : Option Class} {memos middle final : Memos}
      {primary : EndpointStatefulGateTrace.ClassTrace source reaches values record.paths before.native.machine.heap false heap}
      (first : SourceCurrentAllocatedPrimaryReads.ClassReads primary memos middle)
      (tail : ScanReads budget values records (advanceHeap before heap) memo outcome kept after saved middle final) :
      ScanReads budget values (record :: records) before memo outcome (record :: kept) after saved memos final
  | skipped {record : Record} {records kept : List Record} {before after : Checked width}
      {heap anchor : State Symbol Guard} {memo saved : Memo} {outcome : Option Class}
      {memos first second final : Memos}
      {primary : EndpointStatefulGateTrace.ClassTrace source reaches values record.paths before.native.machine.heap true heap}
      {secondary : SourceCurrentSecondaryTrace.ClassTrace source values record.paths heap true anchor}
      (firstRead : SourceCurrentAllocatedPrimaryReads.ClassReads primary memos first)
      (secondRead : SourceCurrentSecondaryMemos.ClassReads secondary first second)
      (tail : ScanReads budget values records (advanceHeap (advanceHeap before heap) anchor) memo
        outcome kept after saved second final) :
      ScanReads budget values (record :: records) before memo outcome kept after saved memos final
  | continued {record : Record} {records kept : List Record} {before middle later after : Checked width}
      {heap anchor : State Symbol Guard} {memo current saved : Memo} {outcome : Option Class}
      {query : Node} {p h : Nat} {snapshot : Snapshot} {memos first second queried final : Memos}
      {primary : EndpointStatefulGateTrace.ClassTrace source reaches values record.paths before.native.machine.heap true heap}
      {secondary : SourceCurrentSecondaryTrace.ClassTrace source values record.paths heap false anchor}
      {seeded : SourceCurrentAllocatedSeededQuery.Seeded values (record.paths.map (List.map Int.ofNat))
        (advanceHeap (advanceHeap before heap) anchor) query middle}
      (firstRead : SourceCurrentAllocatedPrimaryReads.ClassReads primary memos first)
      (secondRead : SourceCurrentSecondaryMemos.ClassReads secondary first second)
      (seededRead : SourceCurrentAllocatedSeededMemos.SeededReads seeded second queried)
      (called : checkedCall p h budget query middle memo = .done false later current snapshot)
      (callRead : CallReads p h budget memo query (physical middle) queried final)
      {last : Memos}
      (tail : ScanReads budget values records later current outcome kept after saved final last) :
      ScanReads budget values (record :: records) before memo outcome kept after saved memos last
  | stopped {record : Record} {records : List Record} {before middle after : Checked width}
      {heap anchor : State Symbol Guard} {memo saved : Memo} {query : Node}
      {p h : Nat} {snapshot : Snapshot} {memos first second queried final : Memos}
      {primary : EndpointStatefulGateTrace.ClassTrace source reaches values record.paths before.native.machine.heap true heap}
      {secondary : SourceCurrentSecondaryTrace.ClassTrace source values record.paths heap false anchor}
      {seeded : SourceCurrentAllocatedSeededQuery.Seeded values (record.paths.map (List.map Int.ofNat))
        (advanceHeap (advanceHeap before heap) anchor) query middle}
      (firstRead : SourceCurrentAllocatedPrimaryReads.ClassReads primary memos first)
      (secondRead : SourceCurrentSecondaryMemos.ClassReads secondary first second)
      (seededRead : SourceCurrentAllocatedSeededMemos.SeededReads seeded second queried)
      (called : checkedCall p h budget query middle memo = .done true after saved snapshot)
      (callRead : CallReads p h budget memo query (physical middle) queried final) :
      ScanReads budget values (record :: records) before memo (some record.paths) [] after saved memos final

/-- One computed record return retains its complete caller and original resource schedule. -/
structure Receipt (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (alphabet : List Guard) (profile : Profile)
    (budget : Nat) (values : List Node) (records : List Record) (before : Caller width) (memos : Memos)
    (outcome : Option Class) (kept : List Record) (after : Checked width) (saved : Memo)
    (next : Inventory) (final : Memos) : Prop where
  reads : ScanReads budget values records before.checked before.fourth outcome kept after saved memos final
  post : Post formulas solver next before (advance before after saved before.merge) final
  frame : Frame formulas solver next after
  fits : Fits (schedule budget values.length (records.map Record.paths) alphabet profile).2 after
  carrier : Heap (fun guard => guard ∈ (schedule budget values.length (records.map Record.paths) alphabet profile).1)
    after.native.machine.heap
  available : Values after.native.machine.heap values
  selected : kept.Sublist records
  primary : ∀ record ∈ kept, EndpointStatefulGateTrace.ClassTrace source reaches values record.paths
    after.native.machine.heap false after.native.machine.heap
  sound : StoppedSound formulas solver values records outcome
  run : ∀ g s p h n,
    fuel budget values.length (records.map Record.paths) alphabet profile ≤ g →
    fuel budget values.length (records.map Record.paths) alphabet profile ≤ s →
    fuel budget values.length (records.map Record.paths) alphabet profile ≤ p →
    fuel budget values.length (records.map Record.paths) alphabet profile ≤ h →
    fuel budget values.length (records.map Record.paths) alphabet profile ≤ n →
    recordScan g s p h n budget values records before.checked before.fourth = .done (outcome, kept) after saved

private theorem call_carrier (annotation : Guard → Prop) {p h budget : Nat} {query : Node}
    {before after : Checked width} {memo saved : Memo} {snapshot : Snapshot} {answer : Bool}
    (actual : checkedCall p h budget query before memo = .done answer after saved snapshot)
    (ready : SourceCurrentConjunctionRowsAllocation.Ready (physical before))
    (known : Heap annotation before.native.machine.heap) (available : Available before.native.machine.heap query) :
    Heap annotation after.native.machine.heap := by
  obtain ⟨raw, reached⟩ := SourceCurrentAllocatedSharedConjunctionWorker.call_done actual
  have preserved := SourceCurrentConjunctionSharedWorkerAnnotations.call_heap annotation p h budget memo query
    (physical before) ready known available
  rw [raw] at preserved
  dsimp only [SourceCurrentConjunctionSharedWorker.Outcome.state] at preserved
  rw [reached]
  exact preserved

/-- Initial caller facts and reservations construct the shared scan at all five computed bounds. -/
theorem complete (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory) (alphabet : List Guard)
    (budget : Nat) (values : List Node) (records : List Record) (before : Caller (bits + 2)) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (available : Values before.checked.native.machine.heap values)
    (proper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [])
    (active : ∀ record ∈ records, Nontrivial record.paths)
    (reserved : Reserved bits budget values.length (records.map Record.paths) alphabet profile)
    (known : Heap (fun guard => guard ∈ alphabet) before.checked.native.machine.heap) :
    ∃ outcome kept after saved next final,
      Receipt formulas solver alphabet profile budget values records before memos outcome kept after saved next final := by
  induction records generalizing before memos inventory alphabet profile with
  | nil =>
      refine ⟨none, [], before.checked, before.fourth, inventory, memos, .nil, ?_, frame, fits,
        known, available, .refl _, (by intro record member; cases member), ?_, ?_⟩
      · exact Post.rebase initial rfl rfl rfl
          (initial.sound.advance formulas solver _ before.fourth before.merge
            (.refl _ (SourceCurrentAllocatedConjunctionMemo.ready before.checked initial.ready.good initial.ready.semantic initial.ready.costs)))
      · intro paths impossible
        cases impossible
      · intros
        rfl
  | cons record records ih =>
      let paths := record.paths
      let nextPlan := classStep budget values.length paths alphabet profile
      have tailProper : ∀ other ∈ records, ∀ path ∈ other.paths, path ≠ [] :=
        fun other member => proper other (List.mem_cons_of_mem _ member)
      have tailActive : ∀ other ∈ records, Nontrivial other.paths :=
        fun other member => active other (List.mem_cons_of_mem _ member)
      have limits := SourceCurrentSharedScanNumericForecast.classFuel_limits budget values.length paths alphabet profile
      have localFuel : classFuel budget values.length paths alphabet profile ≤
          fuel budget values.length ((record :: records).map Record.paths) alphabet profile := Nat.le_max_left _ _
      have tailFuel : fuel budget values.length (records.map Record.paths) nextPlan.1 nextPlan.2 ≤
          fuel budget values.length ((record :: records).map Record.paths) alphabet profile := Nat.le_max_right _ _
      have widen := SourceCurrentSharedScanNumericForecast.classStep_alphabet_ge budget values.length paths alphabet profile
      obtain ⟨firstAnswer, heap, primary, firstFrame, firstFits, firstValues, firstEffects, firstDone⟩ :=
        SourceCurrentGateFrameResources.primary formulas solver inventory source reaches values paths before.checked frame profile fits available
      obtain ⟨firstMemos, firstRead, firstPost⟩ :=
        SourceCurrentSharedScanCallerSteps.primary_post formulas solver primary initial available
      have firstKnown := (SourcePrimaryGateEffects.class_effects (fun guard => guard ∈ alphabet)
        source reaches primary frame.ready.semantic frame.ready.costs available known).2.2.2
      cases firstAnswer with
      | false =>
          obtain ⟨outcome, kept, after, saved, next, final, rest⟩ := ih (inventory := inventory) (alphabet := nextPlan.1)
            (before := advance before (advanceHeap before.checked heap) before.fourth before.merge)
            (memos := firstMemos) (profile := nextPlan.2) firstPost.context firstFrame
            (firstFits.mono (SourceCurrentSharedScanNumericForecast.classStep_primary_ge _ _ _ _ _)) firstValues
            tailProper tailActive reserved.2 (SourceCurrentNativeGuardStep.heap_mono widen firstKnown)
          have headPrimary := (SourceCurrentPrimaryReplay.class_replay source reaches values paths
            before.checked.native.machine.heap false heap primary frame.ready.semantic available).2.2
            after.native.machine.heap rest.post.effects.keeps.growth
          have keptPrimary : ∀ other ∈ record :: kept, EndpointStatefulGateTrace.ClassTrace source reaches
              values other.paths after.native.machine.heap false after.native.machine.heap := by
            intro other member
            rcases List.mem_cons.mp member with same | tailMember
            · cases same
              exact headPrimary
            · exact rest.primary other tailMember
          refine ⟨outcome, record :: kept, after, saved, next, final, .selected firstRead rest.reads,
            firstPost.trans rest.post, rest.frame, rest.fits, rest.carrier, rest.available,
            .cons_cons _ rest.selected, keptPrimary, stopped_cons rest.sound, ?_⟩
          intro g s p h n enoughG enoughS enoughP enoughH enoughN
          have first := firstDone g (Nat.le_trans (Nat.le_trans limits.1 localFuel) enoughG)
          dsimp only [paths] at first
          have tail := rest.run g s p h n (Nat.le_trans tailFuel enoughG) (Nat.le_trans tailFuel enoughS)
            (Nat.le_trans tailFuel enoughP) (Nat.le_trans tailFuel enoughH) (Nat.le_trans tailFuel enoughN)
          dsimp only [SourceCurrentAllocatedPartialState.advance] at tail
          simp [SourceCurrentAllocatedSharedRecordScanWorker.scan, SourceCurrentAllocatedSharedScanWorker.gate,
            SourceCurrentAllocatedGateWorker.primary, first, SourceCurrentAllocatedGateWorker.lift,
            SourceCurrentAllocatedSharedScanWorker.Outcome.bind, tail, SourceCurrentAllocatedSharedRecordScanWorker.select]
      | true =>
          let firstCaller := advance before (advanceHeap before.checked heap) before.fourth before.merge
          obtain ⟨secondAnswer, anchor, secondary, secondFrame, secondFits, secondValues, secondEffects, secondDone⟩ :=
            SourceCurrentGateFrameResources.secondary formulas solver inventory source reaches values paths
              (advanceHeap before.checked heap) firstFrame (gateProfile paths profile) firstFits firstValues
          obtain ⟨secondMemos, secondRead, secondPost⟩ :=
            SourceCurrentSharedScanCallerSteps.secondary_post formulas solver secondary firstPost.context firstValues
          let secondCaller := advance firstCaller (advanceHeap firstCaller.checked anchor) firstCaller.fourth firstCaller.merge
          have secondKnown := (SourceCurrentSecondaryEffects.class_effects (fun guard => guard ∈ alphabet)
            source secondary firstFrame.ready.semantic firstFrame.ready.costs firstValues firstKnown).2.2.2
          cases secondAnswer with
          | true =>
              obtain ⟨outcome, kept, after, saved, next, final, rest⟩ := ih (inventory := inventory) (alphabet := nextPlan.1) (before := secondCaller)
                (memos := secondMemos) (profile := nextPlan.2) secondPost.context secondFrame
                (secondFits.mono (SourceCurrentSharedScanNumericForecast.classStep_secondary_ge _ _ _ _ _)) secondValues
                tailProper tailActive reserved.2 (SourceCurrentNativeGuardStep.heap_mono widen secondKnown)
              refine ⟨outcome, kept, after, saved, next, final, .skipped firstRead secondRead rest.reads,
                firstPost.trans (secondPost.trans rest.post), rest.frame, rest.fits, rest.carrier, rest.available,
                .cons _ rest.selected, rest.primary, stopped_cons rest.sound, ?_⟩
              intro g s p h n enoughG enoughS enoughP enoughH enoughN
              have first := firstDone g (Nat.le_trans (Nat.le_trans limits.1 localFuel) enoughG)
              have second := secondDone s (Nat.le_trans (Nat.le_trans limits.2.1 localFuel) enoughS)
              dsimp only [paths] at first second
              have tail := rest.run g s p h n (Nat.le_trans tailFuel enoughG) (Nat.le_trans tailFuel enoughS)
                (Nat.le_trans tailFuel enoughP) (Nat.le_trans tailFuel enoughH) (Nat.le_trans tailFuel enoughN)
              dsimp only [secondCaller, firstCaller, SourceCurrentAllocatedPartialState.advance] at tail
              simp [SourceCurrentAllocatedSharedRecordScanWorker.scan, SourceCurrentAllocatedSharedScanWorker.gate,
                SourceCurrentAllocatedGateWorker.primary, SourceCurrentAllocatedGateWorker.secondary, first, second,
                SourceCurrentAllocatedGateWorker.lift, SourceCurrentAllocatedSharedScanWorker.Outcome.bind, tail]
          | false =>
              have support := SourceCurrentSecondarySeededSupport.class_support source secondary firstFrame.ready.semantic
                firstFrame.ready.costs firstValues (proper record List.mem_cons_self)
              have signedProper := SourceCurrentSecondarySeededSupport.mapped_proper (proper record List.mem_cons_self)
              obtain ⟨query, middle, queryInventory, queryMemos, seeded, seededReads, queryReceipt, queryFits,
                  included, queryDone, queryKnown⟩ :=
                SourceCurrentSeededGuardNumeric.complete alphabet formulas solver inventory source anchor support.1 support.2.2.1
                  values (paths.map (List.map Int.ofNat)) secondCaller.checked
                  (gateProfile paths (gateProfile paths profile)) secondFrame secondFits secondValues (grows_refl _)
                  support.2.2.2.2.2.2 signedProper reserved.1 secondKnown secondMemos secondPost.context.globals
              have queryPost := SourceCurrentSeededCallerNumeric.of_receipt formulas solver secondPost.context queryReceipt
              let queryCaller := advance secondCaller middle secondCaller.fourth secondCaller.merge
              let nativeProfile := SourceCurrentConstrainedCapSeededForecast.finalProfile values.length
                (paths.map (List.map Int.ofNat)) (gateProfile paths (gateProfile paths profile))
              obtain ⟨answer, later, saved, snapshot, decisionMemos, called, callReads, callPost, answerSound,
                  _queryAvailable, _unfolding, _querySame, memoFits, memoDone⟩ :=
                SourceCurrentAllocatedSharedConjunctionWorkerActual.finite_resources_with_alphabet formulas solver
                  nextPlan.1 budget nativeProfile queryPost.context queryFits queryReceipt.available queryKnown
              have finalFrame := SourceCurrentSharedConjunctionCallerNumeric.of_call formulas solver
                called queryReceipt.frame queryReceipt.available
              have physicalReady := SourceCurrentAllocatedConjunctionMemo.ready middle queryReceipt.frame.ready.good
                queryReceipt.frame.ready.semantic queryReceipt.frame.ready.costs
              have memoKnown := call_carrier (fun guard => guard ∈ nextPlan.1) called physicalReady queryKnown queryReceipt.available
              have memoValues : Values later.native.machine.heap values := fun value member =>
                callPost.effects.keeps.available value (queryReceipt.effects.keeps.available value (secondValues value member))
              have queryStable := fun (p h n : Nat) enoughP enoughH enoughN =>
                SourceCurrentAllocatedSeededWorkerStability.seeded_done_stable (P := p) (H := h) (N := n)
                  queryDone enoughP enoughH enoughN
              let memoCaller := advance queryCaller later saved queryCaller.merge
              cases answer with
              | false =>
                  obtain ⟨outcome, kept, after, finalSaved, next, final, rest⟩ := ih (inventory := queryInventory) (alphabet := nextPlan.1) (before := memoCaller)
                    (memos := decisionMemos) (profile := nextPlan.2) callPost.context finalFrame memoFits memoValues tailProper tailActive reserved.2 memoKnown
                  refine ⟨outcome, kept, after, finalSaved, next, final,
                    .continued firstRead secondRead seededReads called callReads rest.reads,
                    firstPost.trans (secondPost.trans (queryPost.trans (callPost.trans rest.post))),
                    rest.frame, rest.fits, rest.carrier, rest.available, .cons _ rest.selected, rest.primary, stopped_cons rest.sound, ?_⟩
                  intro g s p h n enoughG enoughS enoughP enoughH enoughN
                  have first := firstDone g (Nat.le_trans (Nat.le_trans limits.1 localFuel) enoughG)
                  have second := secondDone s (Nat.le_trans (Nat.le_trans limits.2.1 localFuel) enoughS)
                  have queryAt := queryStable p h n (Nat.le_trans (Nat.le_trans limits.2.2.1 localFuel) enoughP)
                    (Nat.le_trans (Nat.le_trans limits.2.2.1 localFuel) enoughH)
                    (Nat.le_trans (Nat.le_trans limits.2.2.1 localFuel) enoughN)
                  have memoAt := memoDone p h (Nat.le_trans (Nat.le_trans limits.2.2.2.1 localFuel) enoughP)
                    (Nat.le_trans (Nat.le_trans limits.2.2.2.2 localFuel) enoughH)
                  dsimp only [paths] at first second queryAt
                  have tail := rest.run g s p h n (Nat.le_trans tailFuel enoughG) (Nat.le_trans tailFuel enoughS)
                    (Nat.le_trans tailFuel enoughP) (Nat.le_trans tailFuel enoughH) (Nat.le_trans tailFuel enoughN)
                  dsimp only [secondCaller, firstCaller, SourceCurrentAllocatedPartialState.advance] at queryAt
                  dsimp only [SourceCurrentAllocatedPartialState.advance] at memoAt
                  dsimp only [memoCaller, queryCaller, secondCaller, firstCaller,
                    SourceCurrentAllocatedPartialState.advance] at tail
                  simp [SourceCurrentAllocatedSharedRecordScanWorker.scan, SourceCurrentAllocatedSharedScanWorker.gate,
                    SourceCurrentAllocatedGateWorker.primary, SourceCurrentAllocatedGateWorker.secondary, first, second,
                    SourceCurrentAllocatedGateWorker.lift, SourceCurrentAllocatedSharedScanWorker.query, queryAt,
                    SourceCurrentAllocatedSharedScanWorker.decision, memoAt, SourceCurrentAllocatedSharedScanWorker.Outcome.bind, tail]
              | true =>
                  refine ⟨some paths, [], later, saved, queryInventory, decisionMemos,
                    .stopped firstRead secondRead seededReads called callReads,
                    firstPost.trans (secondPost.trans (queryPost.trans callPost)), finalFrame,
                    memoFits.mono (SourceCurrentSharedScanNumericForecast.schedule_profile_ge budget values.length
                      (records.map Record.paths) nextPlan.1 nextPlan.2),
                    SourceCurrentNativeGuardStep.heap_mono
                      (SourceCurrentSharedScanNumericForecast.schedule_alphabet_ge budget values.length
                        (records.map Record.paths) nextPlan.1 nextPlan.2) memoKnown,
                    memoValues, List.nil_sublist _, (by intro record member; cases member), ?_, ?_⟩
                  · intro stopped same
                    have equal := Option.some.inj same
                    subst stopped
                    refine ⟨?_, ?_⟩
                    · exact List.mem_map.mpr ⟨record, List.mem_cons_self, rfl⟩
                    intro ambient symbol terms accepted satisfied
                    obtain ⟨part, common, _⟩ := SourceCurrentConjunctionClassWitness.class_signed_common
                      (.node symbol terms) paths (active record List.mem_cons_self) satisfied
                    have nonempty := SourceCurrentConjunctionClassWitness.class_nonempty paths (active record List.mem_cons_self)
                    have signedNonempty : paths.map (List.map Int.ofNat) ≠ [] :=
                      fun empty => nonempty (List.map_eq_nil_iff.mp empty)
                    have acceptedPart := included signedNonempty ambient symbol terms part accepted common
                    exact answerSound.2 rfl ambient part acceptedPart
                  · intro g s p h n enoughG enoughS enoughP enoughH enoughN
                    have first := firstDone g (Nat.le_trans (Nat.le_trans limits.1 localFuel) enoughG)
                    have second := secondDone s (Nat.le_trans (Nat.le_trans limits.2.1 localFuel) enoughS)
                    have queryAt := queryStable p h n (Nat.le_trans (Nat.le_trans limits.2.2.1 localFuel) enoughP)
                      (Nat.le_trans (Nat.le_trans limits.2.2.1 localFuel) enoughH)
                      (Nat.le_trans (Nat.le_trans limits.2.2.1 localFuel) enoughN)
                    have memoAt := memoDone p h (Nat.le_trans (Nat.le_trans limits.2.2.2.1 localFuel) enoughP)
                      (Nat.le_trans (Nat.le_trans limits.2.2.2.2 localFuel) enoughH)
                    dsimp only [paths] at first second queryAt
                    dsimp only [secondCaller, firstCaller, SourceCurrentAllocatedPartialState.advance] at queryAt
                    dsimp only [SourceCurrentAllocatedPartialState.advance] at memoAt
                    simp [SourceCurrentAllocatedSharedRecordScanWorker.scan, SourceCurrentAllocatedSharedScanWorker.gate,
                      SourceCurrentAllocatedGateWorker.primary, SourceCurrentAllocatedGateWorker.secondary, first, second,
                      SourceCurrentAllocatedGateWorker.lift, SourceCurrentAllocatedSharedScanWorker.query, queryAt,
                      SourceCurrentAllocatedSharedScanWorker.decision, memoAt, SourceCurrentAllocatedSharedScanWorker.Outcome.bind, paths]

/-- The same computed receipt replays the path worker at the same complete return. -/
theorem Receipt.path_run {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {alphabet : List Guard} {profile : Profile}
    {budget : Nat} {values : List Node} {records kept : List Record} {before : Caller width} {memos final : Memos}
    {outcome : Option Class} {after : Checked width} {saved : Memo} {next : Inventory}
    (receipt : Receipt formulas solver alphabet profile budget values records before memos outcome kept after saved next final)
    (g s p h n : Nat)
    (enoughG : fuel budget values.length (records.map Record.paths) alphabet profile ≤ g)
    (enoughS : fuel budget values.length (records.map Record.paths) alphabet profile ≤ s)
    (enoughP : fuel budget values.length (records.map Record.paths) alphabet profile ≤ p)
    (enoughH : fuel budget values.length (records.map Record.paths) alphabet profile ≤ h)
    (enoughN : fuel budget values.length (records.map Record.paths) alphabet profile ≤ n) :
    SourceCurrentAllocatedSharedScanWorker.scan g s p h n budget values (records.map Record.paths)
      before.checked before.fourth = .done (outcome, kept.map Record.paths) after saved := by
  have mapped := congrArg SourceCurrentAllocatedSharedRecordScanWorker.mapPaths
    (receipt.run g s p h n enoughG enoughS enoughP enoughH enoughN)
  rw [SourceCurrentAllocatedSharedRecordScanWorker.scan_mapPaths] at mapped
  exact mapped

end MicroCFTA.SourceCurrentSharedScanCallerNumeric
