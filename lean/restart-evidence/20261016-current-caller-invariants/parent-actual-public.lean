import MicroCFTA.SourceCurrentAllocatedParentEdgeActual
import MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity

#print axioms MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.read
#check @MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.read
#print axioms MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.exposures
#check @MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.exposures
#print axioms MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.projections
#check @MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.projections
#print axioms MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.classes
#check @MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.classes
#print axioms MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.requirements
#check @MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.requirements
#print axioms MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.tuple
#check @MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.tuple
#print axioms MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.tuples
#check @MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.tuples
#print axioms MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.rows
#check @MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.rows
#print axioms MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.run
#check @MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.run
#print axioms MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.decision
#check @MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.decision
#print axioms MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.call
#check @MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.call
#print axioms MicroCFTA.SourceCurrentConjunctionRequiredActual.required_unique
#check @MicroCFTA.SourceCurrentConjunctionRequiredActual.required_unique
#print axioms MicroCFTA.SourceCurrentConjunctionRequiredActual.verified
#check @MicroCFTA.SourceCurrentConjunctionRequiredActual.verified
#print axioms MicroCFTA.SourceCurrentAllocatedPrimaryReads.node_erase
#check @MicroCFTA.SourceCurrentAllocatedPrimaryReads.node_erase
#print axioms MicroCFTA.SourceCurrentAllocatedPrimaryReads.child_erase
#check @MicroCFTA.SourceCurrentAllocatedPrimaryReads.child_erase
#print axioms MicroCFTA.SourceCurrentAllocatedPrimaryReads.edges_erase
#check @MicroCFTA.SourceCurrentAllocatedPrimaryReads.edges_erase
#print axioms MicroCFTA.SourceCurrentAllocatedPrimaryReads.path_erase
#check @MicroCFTA.SourceCurrentAllocatedPrimaryReads.path_erase
#print axioms MicroCFTA.SourceCurrentAllocatedPrimaryReads.class_erase
#check @MicroCFTA.SourceCurrentAllocatedPrimaryReads.class_erase
#print axioms MicroCFTA.SourceCurrentAllocatedScanSourceReads.ScanReads.erase
#check @MicroCFTA.SourceCurrentAllocatedScanSourceReads.ScanReads.erase
#print axioms MicroCFTA.SourceCurrentConjunctionScanClassPassActual.Reads.erase
#check @MicroCFTA.SourceCurrentConjunctionScanClassPassActual.Reads.erase
#print axioms MicroCFTA.SourceCurrentConjunctionScanClassPassActual.verified
#check @MicroCFTA.SourceCurrentConjunctionScanClassPassActual.verified
#print axioms MicroCFTA.SourceCurrentConjunctionScanClassPassActual.from_scan
#check @MicroCFTA.SourceCurrentConjunctionScanClassPassActual.from_scan
#print axioms MicroCFTA.SourceCurrentConjunctionScanClassPassActual.finite
#check @MicroCFTA.SourceCurrentConjunctionScanClassPassActual.finite
#print axioms MicroCFTA.SourceCurrentAllocatedLocalReductionActual.Reads.erase
#check @MicroCFTA.SourceCurrentAllocatedLocalReductionActual.Reads.erase
#print axioms MicroCFTA.SourceCurrentAllocatedLocalReductionActual.ranges_of_finite
#check @MicroCFTA.SourceCurrentAllocatedLocalReductionActual.ranges_of_finite
#print axioms MicroCFTA.SourceCurrentAllocatedLocalReductionActual.prefix_verified
#check @MicroCFTA.SourceCurrentAllocatedLocalReductionActual.prefix_verified
#print axioms MicroCFTA.SourceCurrentAllocatedLocalReductionActual.verified
#check @MicroCFTA.SourceCurrentAllocatedLocalReductionActual.verified
#print axioms MicroCFTA.SourceCurrentAllocatedLocalReductionActual.finite
#check @MicroCFTA.SourceCurrentAllocatedLocalReductionActual.finite
#print axioms MicroCFTA.SourceCurrentAllocatedParentEdgeActual.Reads.erase
#check @MicroCFTA.SourceCurrentAllocatedParentEdgeActual.Reads.erase
#print axioms MicroCFTA.SourceCurrentAllocatedParentEdgeActual.verified
#check @MicroCFTA.SourceCurrentAllocatedParentEdgeActual.verified
#print axioms MicroCFTA.SourceCurrentAllocatedParentEdgeActual.finite
#check @MicroCFTA.SourceCurrentAllocatedParentEdgeActual.finite

namespace MicroCFTA.CurrentActualFoundationProbe
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentConjunctionGlobalMemos
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

example (heap : State Symbol Guard) (memos : Memos) (semantic : SemanticReady heap)
    (costs : InternedFreshOrdinaryCostHeap.Heap heap) (valid : EndpointMemoGateTrace.Valid heap memos) :
    EndpointMemoGateTrace.Valid heap memos := by
  have actual : SourceCurrentConjunctionCompletionReads.Exposures [] heap [] heap := .nil
  have calls : ExposuresReads actual memos memos := .nil
  exact (SourceCurrentAllocatedConjunctionReadValidity.exposures calls semantic costs
    (by intro value member; cases member) valid).1

example (heap : State Symbol Guard) (memos : Memos) (semantic : SemanticReady heap)
    (costs : InternedFreshOrdinaryCostHeap.Heap heap) (valid : EndpointMemoGateTrace.Valid heap memos) :
    EndpointMemoGateTrace.Valid heap memos := by
  have actual : SourceCurrentConjunctionCompletionReads.Projections [] heap [] heap := .nil
  have calls : ProjectionsReads actual memos memos := .nil
  exact (SourceCurrentAllocatedConjunctionReadValidity.projections calls semantic costs
    (by intro job member; cases member) valid).1

example (before : Physical) (memos : Memos) (ready : SourceCurrentConjunctionRowsAllocation.Ready before)
    (valid : EndpointMemoGateTrace.Valid before.heap memos) :
    EndpointMemoGateTrace.Valid before.heap memos ∧ Extends memos.unfolding memos.unfolding ∧ memos.query=memos.query := by
  have actual : SourceCurrentConjunctionWorklist.Run 4 [] [] before [] before := .done
  have calls : RunReads actual memos memos := .done
  exact SourceCurrentAllocatedConjunctionReadValidity.run calls ready
    (by intro nodes member; cases member) valid

example (before : Physical) (memos : Memos) (ready : SourceCurrentConjunctionRowsAllocation.Ready before)
    (valid : EndpointMemoGateTrace.Valid before.heap memos) :
    EndpointMemoGateTrace.Valid before.heap memos := by
  have actual : SourceCurrentConjunctionWorklist.Run 4 [] [[.empty]] before [] before :=
    .empty rfl .done
  have calls : RunReads actual memos memos := .empty (impossible := rfl) .done
  exact (SourceCurrentAllocatedConjunctionReadValidity.run calls ready (by
    intro nodes member value included
    cases List.mem_singleton.mp member
    cases List.mem_singleton.mp included
    exact empty_available _) valid).1

example (before : Physical) (memos : Memos) (ready : SourceCurrentConjunctionRowsAllocation.Ready before)
    (valid : EndpointMemoGateTrace.Valid before.heap memos) :
    EndpointMemoGateTrace.Valid before.heap memos := by
  have actual : SourceCurrentConjunctionWorklist.Run 0 [] [[]] before [] before :=
    .skip rfl rfl .done
  have calls : RunReads actual memos memos := .skip (nonempty := rfl) (skipped := rfl) .done
  exact (SourceCurrentAllocatedConjunctionReadValidity.run calls ready (by
    intro nodes member value included
    cases List.mem_singleton.mp member
    cases included) valid).1

example (budget : Nat) (memo : SourceCurrentEmptinessMemo.Memo) (query original : Value Symbol Guard)
    (answer : Bool) (before : Physical) (memos : Memos)
    (found : memo query.referenceOf=some (original,answer))
    (ready : SourceCurrentConjunctionRowsAllocation.Ready before) (available : Available before.heap query)
    (valid : EndpointMemoGateTrace.Valid before.heap memos) :
    EndpointMemoGateTrace.Valid before.heap memos :=
  (SourceCurrentAllocatedConjunctionReadValidity.call
    (CallReads.hit (budget := budget) (before := before) (memos := memos) found) ready available valid).1

example (budget : Nat) (memo : SourceCurrentEmptinessMemo.Memo) (query : Value Symbol Guard)
    (before : Physical) (memos : Memos) (absent : memo query.referenceOf=none)
    (opened : SourceCurrentConjunctionWorklist.closed query=false)
    (ready : SourceCurrentConjunctionRowsAllocation.Ready before) (available : Available before.heap query)
    (valid : EndpointMemoGateTrace.Valid before.heap memos) :
    EndpointMemoGateTrace.Valid before.heap memos ∧ Extends memos.unfolding memos.unfolding ∧ memos.query=memos.query := by
  have actual : SourceCurrentConjunctionMemo.Call budget memo query before false before
      (SourceCurrentEmptinessMemo.insert memo query false) := .miss absent (.open_input opened)
  have calls : CallReads actual memos memos := .miss (absent := absent) (.open_input opened)
  exact SourceCurrentAllocatedConjunctionReadValidity.call calls ready available valid

example (fuel readFuel : Nat) (paths : List SourceEqualityNeeded.Path) (values result : List (Value Symbol Guard))
    (before after : State Symbol Guard)
    (actual : SourceEqualityRequiredExecution.requireAll fuel readFuel paths values before=.done result after) :
    result=result ∧ after=after := SourceCurrentConjunctionRequiredActual.required_unique actual actual
end MicroCFTA.CurrentActualFoundationProbe

namespace MicroCFTA.CurrentParentActualProbe
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "prefix" => SourceCurrentAllocatedPrecheck.state
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

/-- This actual rejection needs no child residency, load, inherited readiness, or local ranges. -/
theorem rejected_actual
    (F : SourceGuards.Formulas FullSyntax.Formula) (S : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (symbol : Symbol) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo) (memos : Memos)
    (ready : Ready before) (admitted : At F S inventory before)
    (test : SourceEqualityMkEdgeAllocation.contradictory original=true)
    (correct : SourceCurrentEmptinessMemo.Correct F S before.native.machine.heap fourth)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds F S) ambient memo)
    (valid : Valid before.native.machine.heap memos) :
    ∃ next, SourceCurrentAllocatedParentEdge.Receipt F S next symbol original loaded inherited values before
      (SourceCurrentAllocatedMkEdge.reject symbol before).1 (SourceCurrentAllocatedMkEdge.reject symbol before).2
      fourth fourth memo memo memos := by
  have actual : SourceCurrentAllocatedParentEdge.Edge budget symbol original loaded inherited values before fourth memo
      (SourceCurrentAllocatedMkEdge.reject symbol before).1 (SourceCurrentAllocatedMkEdge.reject symbol before).2 fourth memo :=
    .rejected test
  have reads : SourceCurrentAllocatedParentEdgeActual.Reads F S actual memos memos := .rejected (test := test)
  exact SourceCurrentAllocatedParentEdgeActual.verified F S inventory reads ready admitted (by
    intro live
    have impossible := test.symm.trans live
    cases impossible) correct stored covered valid

/-- The unchanged prefix itself excludes every live Scan range obligation. -/
theorem unchanged_actual
    (F : SourceGuards.Formulas FullSyntax.Formula) (S : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo) (memos : Memos)
    (ready : Ready before) (admitted : At F S inventory before)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.operations.constraints=.ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited)
    (available : Values before.native.machine.heap values)
    (actualPrefix : (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited before.operations).1=.ok .unchanged)
    (correct : SourceCurrentEmptinessMemo.Correct F S before.native.machine.heap fourth)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds F S) ambient memo)
    (valid : Valid before.native.machine.heap memos) :
    ∃ next, SourceCurrentAllocatedLocalReduction.Receipt F S next original loaded inherited values values before
      (prefix before loaded inherited) fourth fourth memo memo memos := by
  have actual : SourceCurrentAllocatedLocalReduction.Reduction budget loaded inherited values before fourth memo
      values (prefix before loaded inherited) fourth memo := .unchanged actualPrefix
  have reads : SourceCurrentAllocatedLocalReductionActual.Reads F S actual memos memos :=
    .unchanged (actual := actualPrefix)
  exact SourceCurrentAllocatedLocalReductionActual.verified F S inventory original reads ready admitted cached found
    inheritedReady available correct stored covered (by
      intro records classes
      have impossible := Except.ok.inj (actualPrefix.symm.trans classes)
      cases impossible) valid

/-- Empty-prefix execution returns the supplied erased slots without any future Scan checks. -/
theorem empty_actual
    (F : SourceGuards.Formulas FullSyntax.Formula) (S : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo) (memos : Memos)
    (ready : Ready before) (admitted : At F S inventory before)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.operations.constraints=.ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited)
    (available : Values before.native.machine.heap values)
    (actualPrefix : (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited before.operations).1=.ok .emptyChildren)
    (correct : SourceCurrentEmptinessMemo.Correct F S before.native.machine.heap fourth)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds F S) ambient memo)
    (valid : Valid before.native.machine.heap memos) :
    ∃ next, SourceCurrentAllocatedLocalReduction.Receipt F S next original loaded inherited values
      (EqualityLeafProjectionRuntimeEmpty.erase values) before (prefix before loaded inherited) fourth fourth memo memo memos := by
  have actual : SourceCurrentAllocatedLocalReduction.Reduction budget loaded inherited values before fourth memo
      (EqualityLeafProjectionRuntimeEmpty.erase values) (prefix before loaded inherited) fourth memo := .emptyChildren actualPrefix
  have reads : SourceCurrentAllocatedLocalReductionActual.Reads F S actual memos memos :=
    .emptyChildren (actual := actualPrefix)
  exact SourceCurrentAllocatedLocalReductionActual.verified F S inventory original reads ready admitted cached found
    inheritedReady available correct stored covered (by
      intro records classes
      have impossible := Except.ok.inj (actualPrefix.symm.trans classes)
      cases impossible) valid

/-- A successful empty class scan performs its actual required, pass, and propagation steps. -/
theorem empty_classes_actual
    (F : SourceGuards.Formulas FullSyntax.Formula) (S : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (before : Checked width) (fourth : Fourth) (memo : Memo) (memos : Memos)
    (ready : Ready before) (admitted : At F S inventory before)
    (correct : SourceCurrentEmptinessMemo.Correct F S before.native.machine.heap fourth)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds F S) ambient memo)
    (valid : Valid before.native.machine.heap memos) :
    ∃ next, SourceCurrentConjunctionScanClassPass.Receipt F S next [] [] [] before before fourth fourth memo memo none memos := by
  have scan : SourceCurrentConjunctionClassScan.Scan budget SourceMemoGate.unconstrained
      (SourceEndpointReachability.reaches SourceMemoGate.unconstrained) [] [] before fourth none [] before fourth := .nil
  have retained : SourceCurrentConjunctionSelectedRecords.Retained scan [] [] := .nil
  have done : SourceEqualityRequiredExecution.requireAll 0 0 (SourceEqualitySelectedRequired.paths []) [] before.native.machine.heap=
      .done [] before.native.machine.heap := by
    simpa [SourceEqualitySelectedRequired.paths, EqualityNormalize.canonicalClass] using
      SourceEqualityRequiredExecution.requireAll_identity 0 0 ([] : List (Value Symbol Guard)) before.native.machine.heap
  have passed : SourceCurrentAllocatedClassPass.Pass [] [] before memo [] before memo := .done .nil
  have actual : SourceCurrentConjunctionScanClassPass.Reduction budget [] [] before fourth memo none [] before fourth memo :=
    .completed (fuel := 0) (readFuel := 0) scan retained done passed
  have requiredReads : SourceCurrentRequiredQueryMemos.RequireAllReads (SourceEqualitySelectedRequired.paths []) [] [] before.native.machine.heap
      before.native.machine.heap memos memos := by
    simp only [SourceEqualitySelectedRequired.paths, List.flatten_nil, EqualityNormalize.canonicalClass,
      List.eraseDups_nil, List.mergeSort_nil, List.map_nil]
    change ∃ trace : SourceEqualityRequiredGraph.RequireChildren [] 0 [] before.native.machine.heap [] before.native.machine.heap,
      SourceCurrentRequiredQueryMemos.ChildrenReads trace memos memos
    exact ⟨.nil, .nil⟩
  have passedReads : SourceCurrentAllocatedClassPass.PassReads F S passed memos memos := .done .nil
  have reads : SourceCurrentConjunctionScanClassPassActual.Reads F S actual memos memos :=
    .completed (fuel := 0) (readFuel := 0) (retained := retained) (required := done) .nil requiredReads passedReads
  exact SourceCurrentConjunctionScanClassPassActual.verified F S inventory reads ready admitted
    (by intro value member; cases member) (by intro record member; cases member)
    (by intro record member; cases member) correct stored covered (by trivial) valid

#print axioms rejected_actual
#print axioms unchanged_actual
#print axioms empty_actual
#print axioms empty_classes_actual
end MicroCFTA.CurrentParentActualProbe
