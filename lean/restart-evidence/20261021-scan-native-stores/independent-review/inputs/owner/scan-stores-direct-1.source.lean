import MicroCFTA.SourceCurrentGatePublicationHistory
import MicroCFTA.SourceCurrentConjunctionPublicationHistory
import MicroCFTA.SourceCurrentNativeCurrentStores
import MicroCFTA.SourceCurrentAllocatedNativeActualScope
import MicroCFTA.SourceCurrentNativePositiveSupportAdvance
import MicroCFTA.SourceCurrentNativeOpenRequestResults
import MicroCFTA.SourceCurrentGateGuard
import MicroCFTA.SourceCurrentConjunctionGuard
import MicroCFTA.SourceCurrentConstrainedCapProjectionGuard
import MicroCFTA.SourceCurrentConjunctionDecisionSoundness

/-!
# Current native stores through the same completed Scan

Actual gate and conjunction intervals preserve causal publication history.
Admitted seeded queries retain their exact returned scope and stores.
This theorem consumes a completed graph and does not construct admission.
-/
namespace MicroCFTA.SourceCurrentScanNativeStores
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentConjunctionClassScan (Scan Ready advanceHeap)
open SourceCurrentAllocatedSeededQuery (Operand Fold Seeded)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentNativeRequestPositivePositions (Support)
open SourceCurrentNativeMuPublication (History)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Heap" => State Symbol Guard
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "Current" => SourceCurrentConstrainedCapCurrentNative.At Plain
local notation "PathSupport" => SourceCurrentSecondaryProjectionScoped.PathSupport
local notation "GateReady" => InternedFreshOrdinaryMemoGateTrace.Ready
variable {width : Nat} [edgeDec : DecidableEq (EdgeKey Symbol Guard)]

private structure QueryPost (before after : Checked width) (result : Node) : Prop where
  ready : Ready after
  effects : Effects (physical before) (physical after)
  extension : SourceRecursiveIntersectionKernel.Extension before.native.machine after.native.machine
  available : Available after.native.machine.heap result
  closed : result.free = []
  current : Current after
  supported : Support after.native.machine.heap after.native
  causal : Nonempty (History empty after.native.machine.heap)

private theorem unchanged (before : Checked width) (after : Physical)
    (ready : Ready before) (current : Current before)
    (supported : Support before.native.machine.heap before.native)
    (causal : History empty before.native.machine.heap)
    (effects : Effects (physical before) after)
    (guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain after.heap)
    (interval : History before.native.machine.heap after.heap) :
    Current (advancePhysical before after) ∧
      Support (advancePhysical before after).native.machine.heap (advancePhysical before after).native ∧
      Nonempty (History empty (advancePhysical before after).native.machine.heap) := by
  have next := SourceCurrentAllocatedConjunctionMemo.lift_effects before after ready.good ready.idle effects
  exact ⟨SourceCurrentConstrainedCapCurrentNative.advance Plain before _ current next.good
    next.semantic.ready.semantic guards next.extension next.tables.1 next.tables.2.1,
    SourceCurrentNativePositiveSupportAdvance.advance before _ current supported next.good next.extension
      next.tables.1 next.tables.2.1, ⟨.trans causal interval⟩⟩

private theorem operand (unconstrained : Node → Bool) (anchor : Heap)
    (anchorSemantic : SourceEqualityRequiredSemanticCache.SemanticReady anchor) (anchorReady : GateReady anchor)
    {path : List Int} {values : List Node} {before after : Checked width} {result : Node}
    (actual : Operand path values before result after) (ready : Ready before)
    (available : Values before.native.machine.heap values) (growth : Grows anchor before.native.machine.heap)
    (supportedPath : PathSupport unconstrained anchor path values) (current : Current before)
    (supported : Support before.native.machine.heap before.native)
    (causal : History empty before.native.machine.heap) : QueryPost before after result := by
  obtain ⟨natural, rfl, supportedPath⟩ := supportedPath
  cases actual with
  | force result heap projected =>
      obtain ⟨effects, resident, closed⟩ := SourceCurrentAllocatedGateFields.forest unconstrained anchor
        anchorSemantic anchorReady projected
        (SourceCurrentAllocatedConjunctionMemo.ready before ready.good ready.semantic ready.costs)
        available growth supportedPath
      have guards := SourceCurrentConstrainedCapProjectionGuard.forest Plain projected ready.semantic ready.costs
        available current.1.guards
      obtain ⟨interval⟩ := SourceCurrentRequiredPublicationHistory.forest projected ready.semantic ready.costs available
      obtain ⟨nextCurrent, nextSupport, nextHistory⟩ := unchanged before ⟨heap, before.operations⟩ ready
        current supported causal effects guards interval
      exact ⟨SourceCurrentConjunctionClassScan.advance_ready before _ ready effects, effects,
        SourceCurrentAllocatedQueryMemo.advance_extension before _ effects, resident, closed,
        nextCurrent, nextSupport, nextHistory⟩

variable [DecidableEq Symbol]

private theorem fold (unconstrained : Node → Bool) (anchor : Heap)
    (anchorSemantic : SourceEqualityRequiredSemanticCache.SemanticReady anchor) (anchorReady : GateReady anchor)
    {paths : List (List Int)} {values : List Node} {before after : Checked width} {result : Node}
    (actual : Fold values paths before result after) (ready : Ready before)
    (available : Values before.native.machine.heap values) (growth : Grows anchor before.native.machine.heap)
    (supportedPaths : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
    (current : Current before) (supported : Support before.native.machine.heap before.native)
    (causal : History empty before.native.machine.heap) : QueryPost before after result := by
  revert ready available growth supportedPaths current supported causal
  induction actual with
  | one actual =>
      intro ready available growth supportedPaths current supported causal
      exact operand unconstrained anchor anchorSemantic anchorReady actual ready available growth
        (supportedPaths _ List.mem_cons_self) current supported causal
  | cons first rest native ih =>
      intro ready available growth supportedPaths current supported causal
      have head := operand unconstrained anchor anchorSemantic anchorReady first ready available growth
        (supportedPaths _ List.mem_cons_self) current supported causal
      obtain ⟨headHistory⟩ := head.causal
      have tail := ih head.ready (fun value member => head.effects.keeps.available value (available value member))
        (grows_trans growth head.effects.keeps.growth)
        (fun path member => supportedPaths path (List.mem_cons_of_mem _ member)) head.current head.supported headHistory
      have leftAvailable := tail.effects.keeps.available _ head.available
      let actualStep : SourceCurrentAllocatedTargetQuery.Step _ _ _ _ _ := .run native
      obtain ⟨tailHistory⟩ := tail.causal
      obtain ⟨nextCurrent, nextSupport, nextHistory⟩ := SourceCurrentNativeCurrentStores.step actualStep
        tail.ready.good tail.ready.semantic tail.current tail.supported tailHistory leftAvailable tail.available
        head.closed tail.closed
      obtain ⟨scopedCache, idle, closed⟩ := SourceCurrentAllocatedNativeActualScope.step actualStep
        tail.ready.good tail.ready.semantic tail.ready.scopedCache tail.ready.idle leftAvailable tail.available
        head.closed tail.closed
      have effects := SourceCurrentAllocatedNativeTraceEffects.effects native tail.ready.good tail.ready.semantic
        tail.ready.costs (fun _ => trivial)
      have resident := SourceCurrentNativeOpenRequestResults.node_result _ _ _ _ _ tail.ready.good.native native
      exact ⟨⟨effects.1,effects.2.1.ready.semantic,effects.2.1.ready.costs,scopedCache,idle⟩,
        head.effects.trans (tail.effects.trans effects.2.1),
        head.extension.trans (tail.extension.trans effects.2.2), resident, closed,
        nextCurrent,nextSupport,nextHistory⟩

private theorem seeded (unconstrained : Node → Bool) (anchor : Heap)
    (anchorSemantic : SourceEqualityRequiredSemanticCache.SemanticReady anchor) (anchorReady : GateReady anchor)
    {paths : List (List Int)} {values : List Node} {before after : Checked width} {result : Node}
    (actual : Seeded values paths before result after) (ready : Ready before)
    (available : Values before.native.machine.heap values) (growth : Grows anchor before.native.machine.heap)
    (supportedPaths : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
    (current : Current before) (supported : Support before.native.machine.heap before.native)
    (causal : History empty before.native.machine.heap) : QueryPost before after result := by
  cases actual with
  | nil =>
      exact ⟨ready,.refl _ (SourceCurrentAllocatedConjunctionMemo.ready _ ready.good ready.semantic ready.costs),
        .refl _,empty_available _,rfl,current,supported,⟨causal⟩⟩
  | nonempty actual =>
      exact fold unconstrained anchor anchorSemantic anchorReady actual ready available growth
        (by intro path member; exact supportedPaths path (by simpa [List.mem_append,List.mem_cons,or_comm] using member))
        current supported causal

variable [DecidableEq Node]

private theorem decision
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {budget : Nat} {memo saved : SourceCurrentEmptinessMemo.Memo} {query : Node} {before : Checked width}
    {answer : Bool} {after : Physical}
    (actual : SourceCurrentConjunctionMemo.Call budget memo query (physical before) answer after saved)
    (ready : Ready before) (available : Available before.native.machine.heap query)
    (current : Current before) (supported : Support before.native.machine.heap before.native)
    (causal : History empty before.native.machine.heap) :
    Ready (advancePhysical before after) ∧ Effects (physical before) after ∧
      SourceRecursiveIntersectionKernel.Extension before.native.machine (advancePhysical before after).native.machine ∧
      Current (advancePhysical before after) ∧
      Support (advancePhysical before after).native.machine.heap (advancePhysical before after).native ∧
      Nonempty (History empty (advancePhysical before after).native.machine.heap) := by
  have initial := SourceCurrentAllocatedConjunctionMemo.ready before ready.good ready.semantic ready.costs
  have effects : Effects (physical before) after := by
    cases actual with
    | hit => exact .refl _ initial
    | miss _ actual => exact (SourceCurrentConjunctionDecision.Decision.verified actual initial available formulas solver).1
  have guards := SourceCurrentConjunctionGuard.call Plain actual initial available current.1.guards
  obtain ⟨interval⟩ := SourceCurrentConjunctionPublicationHistory.call actual initial available
  obtain ⟨nextCurrent,nextSupport,nextHistory⟩ := unchanged before after ready current supported causal effects guards interval
  exact ⟨SourceCurrentConjunctionClassScan.advance_ready before after ready effects,effects,
    SourceCurrentAllocatedQueryMemo.advance_extension before after effects,nextCurrent,nextSupport,nextHistory⟩

/-- The same completed Scan returns current conditional stores and its actual causal history. -/
theorem scan
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {budget : Nat} {unconstrained reaches : Node → Bool} {values : List Node}
    {classes selected : EqualityNormalize.Constraints} {outcome : Option EqualityNormalize.Class}
    {before after : Checked width} {memo saved : SourceCurrentEmptinessMemo.Memo}
    (actual : Scan budget unconstrained reaches values classes before memo outcome selected after saved)
    (ready : Ready before) (available : Values before.native.machine.heap values)
    (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ [])
    (current : Current before) (supported : Support before.native.machine.heap before.native)
    (causal : History empty before.native.machine.heap) :
    Ready after ∧ Effects (physical before) (physical after) ∧
      SourceRecursiveIntersectionKernel.Extension before.native.machine after.native.machine ∧
      Values after.native.machine.heap values ∧ Current after ∧
      Support after.native.machine.heap after.native ∧ Nonempty (History empty after.native.machine.heap) := by
  revert ready available proper current supported causal
  induction actual with
  | nil =>
      intro ready available proper current supported causal
      exact ⟨ready,.refl _ (SourceCurrentAllocatedConjunctionMemo.ready _ ready.good ready.semantic ready.costs),
        .refl _,available,current,supported,⟨causal⟩⟩
  | selected primary rest ih =>
      intro ready available proper current supported causal
      have first := SourceCurrentConjunctionClassScan.primary_effects unconstrained reaches primary ready available
      have guards := SourceCurrentGateGuard.primary Plain unconstrained reaches primary ready.semantic ready.costs
        available current.1.guards
      obtain ⟨interval⟩ := SourceCurrentGatePublicationHistory.primary unconstrained reaches primary
        ready.semantic ready.costs available
      obtain ⟨nextCurrent,nextSupport,⟨nextHistory⟩⟩ := unchanged _ _ ready current supported causal first.2.1 guards interval
      obtain ⟨finalReady,effects,extension,values,finalCurrent,finalSupport,finalHistory⟩ :=
        ih first.1 first.2.2 (fun paths member => proper paths (List.mem_cons_of_mem _ member))
          nextCurrent nextSupport nextHistory
      exact ⟨finalReady,first.2.1.trans effects,
        (SourceCurrentAllocatedQueryMemo.advance_extension _ _ first.2.1).trans extension,
        values,finalCurrent,finalSupport,finalHistory⟩
  | skipped primary secondary rest ih =>
      intro ready available proper current supported causal
      have first := SourceCurrentConjunctionClassScan.primary_effects unconstrained reaches primary ready available
      have firstGuards := SourceCurrentGateGuard.primary Plain unconstrained reaches primary ready.semantic ready.costs
        available current.1.guards
      obtain ⟨firstInterval⟩ := SourceCurrentGatePublicationHistory.primary unconstrained reaches primary
        ready.semantic ready.costs available
      obtain ⟨middleCurrent,middleSupport,⟨middleHistory⟩⟩ := unchanged _ _ ready current supported causal first.2.1 firstGuards firstInterval
      have second := SourceCurrentConjunctionClassScan.secondary_effects unconstrained secondary first.1 first.2.2
      have secondGuards := SourceCurrentGateGuard.secondary Plain unconstrained secondary first.1.semantic first.1.costs
        first.2.2 middleCurrent.1.guards
      obtain ⟨secondInterval⟩ := SourceCurrentGatePublicationHistory.secondary unconstrained secondary
        first.1.semantic first.1.costs first.2.2
      obtain ⟨nextCurrent,nextSupport,⟨nextHistory⟩⟩ := unchanged _ _ first.1 middleCurrent middleSupport middleHistory
        second.2.1 secondGuards secondInterval
      obtain ⟨finalReady,effects,extension,values,finalCurrent,finalSupport,finalHistory⟩ :=
        ih second.1 second.2.2 (fun paths member => proper paths (List.mem_cons_of_mem _ member))
          nextCurrent nextSupport nextHistory
      exact ⟨finalReady,first.2.1.trans (second.2.1.trans effects),
        (SourceCurrentAllocatedQueryMemo.advance_extension _ _ first.2.1).trans
          ((SourceCurrentAllocatedQueryMemo.advance_extension _ _ second.2.1).trans extension),
        values,finalCurrent,finalSupport,finalHistory⟩
  | continued primary secondary actualSeeded actualDecision rest ih =>
      intro ready available proper current supported causal
      have first := SourceCurrentConjunctionClassScan.primary_effects unconstrained reaches primary ready available
      have firstGuards := SourceCurrentGateGuard.primary Plain unconstrained reaches primary ready.semantic ready.costs
        available current.1.guards
      obtain ⟨firstInterval⟩ := SourceCurrentGatePublicationHistory.primary unconstrained reaches primary
        ready.semantic ready.costs available
      obtain ⟨middleCurrent,middleSupport,⟨middleHistory⟩⟩ := unchanged _ _ ready current supported causal first.2.1 firstGuards firstInterval
      have second := SourceCurrentConjunctionClassScan.secondary_effects unconstrained secondary first.1 first.2.2
      have secondGuards := SourceCurrentGateGuard.secondary Plain unconstrained secondary first.1.semantic first.1.costs
        first.2.2 middleCurrent.1.guards
      obtain ⟨secondInterval⟩ := SourceCurrentGatePublicationHistory.secondary unconstrained secondary
        first.1.semantic first.1.costs first.2.2
      obtain ⟨anchorCurrent,anchorSupport,⟨anchorHistory⟩⟩ := unchanged _ _ first.1 middleCurrent middleSupport middleHistory
        second.2.1 secondGuards secondInterval
      obtain ⟨anchorSemantic,anchorReady,_,_,pathsSupported⟩ := SourceCurrentSecondaryProjectionScoped.class_support
        unconstrained secondary first.1.semantic
        (SourceCurrentClassGateCompletion.gate_ready first.1.semantic first.1.costs) first.2.2 (proper _ List.mem_cons_self)
      have query := seeded unconstrained _ anchorSemantic anchorReady actualSeeded second.1 second.2.2 (grows_refl _)
        (by intro path member; obtain ⟨natural,included,rfl⟩ := List.mem_map.mp member; exact pathsSupported natural included)
        anchorCurrent anchorSupport anchorHistory
      obtain ⟨queryHistory⟩ := query.causal
      obtain ⟨laterReady,laterEffects,laterExtension,laterCurrent,laterSupport,⟨laterHistory⟩⟩ :=
        decision formulas solver actualDecision query.ready query.available query.current query.supported queryHistory
      have laterValues := fun value member => laterEffects.keeps.available value
        (query.effects.keeps.available value (second.2.2 value member))
      obtain ⟨finalReady,effects,extension,values,finalCurrent,finalSupport,finalHistory⟩ :=
        ih laterReady laterValues (fun paths member => proper paths (List.mem_cons_of_mem _ member))
          laterCurrent laterSupport laterHistory
      exact ⟨finalReady,first.2.1.trans (second.2.1.trans (query.effects.trans (laterEffects.trans effects))),
        (SourceCurrentAllocatedQueryMemo.advance_extension _ _ first.2.1).trans
          ((SourceCurrentAllocatedQueryMemo.advance_extension _ _ second.2.1).trans
            (query.extension.trans (laterExtension.trans extension))),values,finalCurrent,finalSupport,finalHistory⟩
  | stopped primary secondary actualSeeded actualDecision =>
      intro ready available proper current supported causal
      have first := SourceCurrentConjunctionClassScan.primary_effects unconstrained reaches primary ready available
      have firstGuards := SourceCurrentGateGuard.primary Plain unconstrained reaches primary ready.semantic ready.costs
        available current.1.guards
      obtain ⟨firstInterval⟩ := SourceCurrentGatePublicationHistory.primary unconstrained reaches primary
        ready.semantic ready.costs available
      obtain ⟨middleCurrent,middleSupport,⟨middleHistory⟩⟩ := unchanged _ _ ready current supported causal first.2.1 firstGuards firstInterval
      have second := SourceCurrentConjunctionClassScan.secondary_effects unconstrained secondary first.1 first.2.2
      have secondGuards := SourceCurrentGateGuard.secondary Plain unconstrained secondary first.1.semantic first.1.costs
        first.2.2 middleCurrent.1.guards
      obtain ⟨secondInterval⟩ := SourceCurrentGatePublicationHistory.secondary unconstrained secondary
        first.1.semantic first.1.costs first.2.2
      obtain ⟨anchorCurrent,anchorSupport,⟨anchorHistory⟩⟩ := unchanged _ _ first.1 middleCurrent middleSupport middleHistory
        second.2.1 secondGuards secondInterval
      obtain ⟨anchorSemantic,anchorReady,_,_,pathsSupported⟩ := SourceCurrentSecondaryProjectionScoped.class_support
        unconstrained secondary first.1.semantic
        (SourceCurrentClassGateCompletion.gate_ready first.1.semantic first.1.costs) first.2.2 (proper _ List.mem_cons_self)
      have query := seeded unconstrained _ anchorSemantic anchorReady actualSeeded second.1 second.2.2 (grows_refl _)
        (by intro path member; obtain ⟨natural,included,rfl⟩ := List.mem_map.mp member; exact pathsSupported natural included)
        anchorCurrent anchorSupport anchorHistory
      obtain ⟨queryHistory⟩ := query.causal
      obtain ⟨finalReady,effects,extension,finalCurrent,finalSupport,finalHistory⟩ :=
        decision formulas solver actualDecision query.ready query.available query.current query.supported queryHistory
      exact ⟨finalReady,first.2.1.trans (second.2.1.trans (query.effects.trans effects)),
        (SourceCurrentAllocatedQueryMemo.advance_extension _ _ first.2.1).trans
          ((SourceCurrentAllocatedQueryMemo.advance_extension _ _ second.2.1).trans (query.extension.trans extension)),
        (fun value member => effects.keeps.available value (query.effects.keeps.available value (second.2.2 value member))),
        finalCurrent,finalSupport,finalHistory⟩

end MicroCFTA.SourceCurrentScanNativeStores
