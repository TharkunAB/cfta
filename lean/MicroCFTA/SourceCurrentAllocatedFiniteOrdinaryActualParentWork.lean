import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryActualClassPassWork
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentUniformBudgets
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeState
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryRequiredReservations

/-!
# Actual constructor Work through Stage, Local, and Parent

The supplied strict reads retain each literal intermediate state.
The finite ordinary Scan makes no constructor request.
Required precedes the class pass, and the parent constructor follows Local.
Initial own guard bounds give the uniform parent budget.
No capacity, reserved headroom, or future execution is an input.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryActualParentWork
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready advanceHeap)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (ChildrenShape EdgeShape)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace nodeRequests_append edgeRequests_append)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests observe makeEdge_observe)
open MergedOrdinaryHeight (childrenHeight edgeHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "Limits" => SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.Limits
local notation "Bounds" => SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.Bounds
local notation "sourceGate" => SourceMemoGate.unconstrained
local notation "sourceReaches" => SourceEndpointReachability.reaches sourceGate
local notation "contradictory" => SourceEqualityMkEdgeAllocation.contradictory
local notation "raw" => SourceEqualityConjoinAllocation.readback
variable {width : Nat}

section Stages
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- The same selected-only Scan, Required return, and class pass give the literal stage request bound. -/
theorem stage (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory)
    {budget : Nat} {records : List SourceEqualityClassOrder.Record}
    {values results : List (Value Symbol Guard)} {before after : Checked width}
    {fourth savedFourth : Fourth} {memo saved : Memo} {outcome : Option Class} {memos final : Memos}
    {actual : SourceCurrentConjunctionScanClassPass.Reduction budget records values before fourth memo outcome results after savedFourth saved}
    (reads : SourceCurrentConjunctionScanClassPassActual.Reads formulas solver actual memos final)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (proper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [])
    (fields : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record ∧ EqualityTrie.Ascending record.trie ∧ Nontrivial record.paths)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physical : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : NativeStored before.native) (profiles : Profiles memo) (output : OutputStored before.native)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count)
    (pathsBound : ∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound) :
    ∃ requests, Trace before.native.machine.heap after.native.machine.heap requests ∧
      nodeRequests requests ≤ SourceCurrentAllocatedFiniteOrdinaryStageResources.nodeBudget records rows arity count depth bound ∧
      edgeRequests requests ≤ SourceCurrentAllocatedFiniteOrdinaryStageResources.edgeBudget records rows arity count depth bound := by
  have domain := ChildrenShape.domain values profile
  have ranges := SourceCurrentAllocatedFiniteOrdinaryScanRanges.scan_ranges budget sourceGate sourceReaches values
    (records.map SourceEqualityClassOrder.Record.paths) before fourth ready.good.native.machine.1.coherent available domain
  have pathsProper : ∀ paths ∈ records.map SourceEqualityClassOrder.Record.paths, ∀ path ∈ paths, path ≠ [] := by
    intro paths member
    obtain ⟨record, present, rfl⟩ := List.mem_map.mp member
    exact proper record present
  have pathsActive : ∀ paths ∈ records.map SourceEqualityClassOrder.Record.paths, Nontrivial paths := by
    intro paths member
    obtain ⟨record, present, rfl⟩ := List.mem_map.mp member
    exact (fields record present).2.2
  cases reads with
  | stopped scanReads =>
      rename_i paths selected scan
      have impossible := (SourceCurrentAllocatedFiniteOrdinaryScan.scan scan ready available domain).1
      cases impossible
  | completed first second last =>
      rename_i kept requiredValues middle selected heap fuel readFuel scanMemos requiredMemos required scan retained pass
      have unchanged := SourceCurrentAllocatedFiniteOrdinaryScan.scan scan ready available domain
      have sameLength : kept.length = records.length := by
        have lengths := congrArg List.length (retained.fields.2.trans unchanged.2.1)
        simpa only [List.length_map] using lengths
      have sameKept := retained.fields.1.eq_of_length sameLength
      subst kept
      have sameMiddle := unchanged.2.2.1
      cases sameMiddle
      obtain ⟨requiredInventory, requiredReceipt⟩ := SourceCurrentConjunctionRequiredActual.verified
        formulas solver inventory scan ready admitted available pathsProper pathsActive correct ranges required
      have scanValid := (SourceCurrentAllocatedScanReadValidity.scan first ready available pathsProper formulas solver correct ranges valid).1
      have requiredValid := (SourceCurrentAllocatedRequiredReadValidity.required second ready.semantic ready.costs available scanValid).1
      have requiredProfile := SourceCurrentAllocatedFiniteOrdinaryRequiredProfile.requireAll_done fuel readFuel
        (SourceEqualitySelectedRequired.paths selected) values requiredValues before.native.machine.heap heap required ready.semantic available profile
      have narrowed := SourceCurrentAllocatedFiniteOrdinaryRequired.requireAll_done fuel readFuel
        (SourceEqualitySelectedRequired.paths selected) values requiredValues before.native.machine.heap heap required ready.semantic available domain
      have afterHeight := Nat.le_trans (SourceCurrentAllocatedFiniteOrdinaryNarrow.forest_height narrowed.2.2.2.2) heightBound
      have retainedFields := retained.fields
      have counted := SourceCurrentAllocatedFiniteOrdinaryActualClassPassWork.pass formulas solver requiredInventory last
        (fun record member => (fields record (retainedFields.1.subset member)).1)
        (fun record member => (fields record (retainedFields.1.subset member)).2.2)
        requiredReceipt.ready requiredReceipt.admitted requiredReceipt.resident (physical.grows requiredReceipt.effects.keeps)
        profiles (SourceCurrentAllocatedFiniteOrdinaryStored.advance_stored before.native _ native)
        (SourceCurrentAllocatedFiniteOrdinaryOutputStored.advance_stored before.native _ output) covered requiredValid
        rows arity count depth bound requiredProfile.2.2.2.1 (by rw [requiredProfile.2.2.2.2]; exact lengthBound) pathsBound afterHeight
      obtain ⟨later, lastWork, lastNodes, lastEdges⟩ := counted.2.2.2.2.2.2.2
      obtain ⟨earlier, firstWork, firstNodes, firstEdges, _nodeSupply, _edgeSupply⟩ :=
        SourceCurrentAllocatedFiniteOrdinaryRequiredReservations.requireAll_done fuel readFuel
          (SourceEqualitySelectedRequired.paths selected) values requiredValues before.native.machine.heap heap required ready.semantic available domain
      have occurrences := SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds.children values profile bound heightBound
      have neededNodes := Nat.le_trans occurrences.1 (Nat.mul_le_mul_right _ lengthBound)
      have neededEdges := Nat.le_trans occurrences.2 (Nat.mul_le_mul_right _ lengthBound)
      refine ⟨earlier ++ later, firstWork.trans lastWork, ?_, ?_⟩
      · rw [nodeRequests_append]
        unfold SourceCurrentAllocatedFiniteOrdinaryStageResources.nodeBudget
        omega
      · rw [edgeRequests_append]
        unfold SourceCurrentAllocatedFiniteOrdinaryStageResources.edgeBudget
        omega

/-- The literal own precheck selects the actual local stage budget or no constructor work. -/
theorem local_reads (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (original : Guard)
    {budget : Nat} {loaded : Allocated} {inherited : EqValue}
    {values results : List (Value Symbol Guard)} {before after : Checked width}
    {fourth savedFourth : Fourth} {memo saved : Memo} {memos final : Memos}
    {actual : SourceCurrentAllocatedLocalReduction.Reduction budget loaded inherited values before fourth memo results after savedFourth saved}
    (reads : SourceCurrentAllocatedLocalReductionActual.Reads formulas solver actual memos final)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited)
    (available : Values before.native.machine.heap values)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physical : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : NativeStored before.native) (profiles : Profiles memo) (output : OutputStored before.native)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (limits : Limits) (ownBound : Bounds limits original) (rows arity count bound : Nat)
    (profile : ChildrenShape rows arity values) (lengthBound : values.length ≤ count) (heightBound : childrenHeight values ≤ bound) :
    ∃ requests, Trace before.native.machine.heap after.native.machine.heap requests ∧
      nodeRequests requests ≤ SourceCurrentAllocatedFiniteOrdinaryLocalResources.nodeBudget loaded inherited before.operations
        rows arity count (SourceCurrentAllocatedFiniteOrdinaryGuardOwn.pathDepth limits) bound ∧
      edgeRequests requests ≤ SourceCurrentAllocatedFiniteOrdinaryLocalResources.edgeBudget loaded inherited before.operations
        rows arity count (SourceCurrentAllocatedFiniteOrdinaryGuardOwn.pathDepth limits) bound := by
  cases reads with
  | unchanged => exact ⟨[], .refl _, Nat.zero_le _, Nat.zero_le _⟩
  | emptyChildren => exact ⟨[], .refl _, Nat.zero_le _, Nat.zero_le _⟩
  | classes read =>
      rename_i records outcome actual continuation
      obtain ⟨own, checked⟩ := SourceCurrentAllocatedLocalReductionActual.prefix_verified formulas solver inventory before
        original loaded inherited ready admitted cached found inheritedReady actual
      obtain ⟨proper, _, _, _, _, fields⟩ := checked.classes records rfl
      have recordsProper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [] := by
        intro record member
        exact proper record.paths (List.mem_map.mpr ⟨record, member, rfl⟩)
      have pathsBound := (SourceCurrentAllocatedFiniteOrdinaryGuardOwn.receipt checked limits ownBound).2.2.2
      have counted := stage formulas solver inventory read checked.ready checked.admitted available recordsProper fields
        correct physical covered native profiles output valid rows arity count
        (SourceCurrentAllocatedFiniteOrdinaryGuardOwn.pathDepth limits) bound profile lengthBound pathsBound heightBound
      simpa only [SourceCurrentAllocatedFiniteOrdinaryLocalResources.nodeBudget,
        SourceCurrentAllocatedFiniteOrdinaryLocalResources.edgeBudget, actual, SourceCurrentAllocatedPrecheck.state_native] using counted

end Stages

private theorem built_work [DecidableEq (EdgeKey Symbol Guard)]
    (symbol : Symbol) (loaded : Allocated) (values : List (Value Symbol Guard))
    (before : Checked width) (after : Checked width) (result : EdgeValue Symbol Guard)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before.operations)
    (ready : SourceEqualityConstraintAllocation.Ready before.operations.constraints loaded.stored)
    (built : SourceCurrentAllocatedMkEdge.build symbol loaded values before = (.ok result, after)) :
    ∃ requests, Trace before.native.machine.heap after.native.machine.heap requests ∧ nodeRequests requests = 0 ∧ edgeRequests requests = 1 := by
  let keep := SourceEqualityMkEdgeAllocation.accepted (raw loaded) values.length
  let job := SourceEqualityMkEdgeAllocation.work symbol (raw loaded) values keep
  have checked := SourceEqualityMkEdgeAllocation.build_receipt symbol loaded.stored loaded.guard values before.operations before.native.machine.heap valid ready
  have heapEq : (run job before.native.machine.heap).2 = after.native.machine.heap := by
    have projected := congrArg (fun actual => actual.2.native.machine.heap) built
    dsimp only [SourceCurrentAllocatedMkEdge.build] at projected
    rw [checked.1] at projected
    exact projected
  refine ⟨observe job before.native.machine.heap, ?_, ?_, ?_⟩
  · simpa only [heapEq] using Trace.work before.native.machine.heap job
  · dsimp only [job, SourceEqualityMkEdgeAllocation.work]
    split <;> simp [makeEdge_observe, nodeRequests]
  · dsimp only [job, SourceEqualityMkEdgeAllocation.work]
    split <;> simp [makeEdge_observe, edgeRequests]

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- The supplied exact parent reads pay only for their local prefix and one selected edge constructor. -/
theorem structure_from_reads (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (original : EdgeValue Symbol Guard)
    {budget : Nat} {loaded : Allocated} {inherited : EqValue} {before after : Checked width} {result : EdgeValue Symbol Guard}
    {fourth savedFourth : Fourth} {memo saved : Memo} {memos final : Memos}
    {actual : SourceCurrentAllocatedParentEdge.Edge budget original.entry.key.symbol original.entry.key.constraint
      loaded inherited original.children before fourth memo result after savedFourth saved}
    (reads : SourceCurrentAllocatedParentEdgeActual.Reads formulas solver actual memos final)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (live : contradictory original.entry.key.constraint = false →
      SourceEqualityGuardReadback.Cached original.entry.key.constraint.equalities ∧
      SourceEqualityConstraintFieldLookup.load original.entry.key.constraint before.operations.constraints = .ok (some loaded) ∧
      SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited ∧ Values before.native.machine.heap original.children)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physical : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : NativeStored before.native) (profiles : Profiles memo) (output : OutputStored before.native)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (limits : Limits) (rows arity bound : Nat) (guards : SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge limits original)
    (profile : EdgeShape rows arity original) (heightBound : edgeHeight original ≤ bound) :
    ∃ requests, Trace before.native.machine.heap after.native.machine.heap requests ∧
      nodeRequests requests ≤ SourceCurrentAllocatedFiniteOrdinaryParentUniformBudgets.nodeBudget limits rows arity bound ∧
      edgeRequests requests ≤ SourceCurrentAllocatedFiniteOrdinaryParentUniformBudgets.edgeBudget limits rows arity bound := by
  cases reads with
  | rejected =>
      refine ⟨observe (makeEdge original.entry.key.symbol SourceEqualityConstraintConstructors.top [.empty]) before.native.machine.heap,
        Trace.work _ _, ?_, ?_⟩
      · simp [makeEdge_observe, nodeRequests]
      · simpa only [makeEdge_observe, edgeRequests] using
          SourceCurrentAllocatedFiniteOrdinaryParentUniformBudgets.edgeBudget_pos limits rows arity bound
  | live read =>
      rename_i children middle test built reduction
      obtain ⟨cached, found, inheritedReady, available⟩ := live test
      have rawBound := SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge.guard original guards
      have childHeight : childrenHeight original.children ≤ bound := by
        simpa only [SourceCurrentAllocatedFiniteOrdinaryDomain.edgeHeight_children] using heightBound
      obtain ⟨own, branch, prefixReceipt⟩ := SourceCurrentAllocatedPrecheck.loaded_complete formulas solver inventory before
        ready admitted original.entry.key.constraint cached loaded found inherited inheritedReady
      have uniform := SourceCurrentAllocatedFiniteOrdinaryParentUniformBudgets.receipt_budget prefixReceipt limits rawBound rows arity arity bound (Nat.le_refl _)
      obtain ⟨earlier, firstWork, firstNodes, firstEdges⟩ := local_reads formulas solver inventory original.entry.key.constraint
        read ready admitted cached found inheritedReady available correct physical covered native profiles output valid limits rawBound
        rows arity arity bound (EdgeShape.children original profile) (EdgeShape.arity original profile) childHeight
      have ranges : SourceCurrentAllocatedLocalReductionActual.Ranges budget loaded inherited original.children before fourth := by
        intro records _
        exact SourceCurrentAllocatedFiniteOrdinaryScanRanges.scan_ranges budget sourceGate sourceReaches original.children
          (records.map SourceEqualityClassOrder.Record.paths) (SourceCurrentAllocatedPrecheck.state before loaded inherited) fourth
          ready.good.native.machine.1.coherent available (EdgeShape.domain original profile)
      obtain ⟨next, receipt⟩ := SourceCurrentAllocatedLocalReductionActual.verified formulas solver inventory original.entry.key.constraint
        read ready admitted cached found inheritedReady available correct physical covered ranges valid
      have loadedReady := SourceEqualityConstraintFieldLookup.load_ready original.entry.key.constraint before.operations.constraints
        ready.good.operations.constraints cached loaded found
      obtain ⟨later, lastWork, lastNodes, lastEdges⟩ := built_work original.entry.key.symbol loaded children middle _ _
        receipt.ready.good.operations (loadedReady.1.grows receipt.effects.grows.constraint_growth) built
      refine ⟨earlier ++ later, firstWork.trans lastWork, ?_, ?_⟩
      · rw [nodeRequests_append, lastNodes]
        simp only [SourceCurrentAllocatedFiniteOrdinaryParentResources.nodeBudget, test, Bool.false_eq_true, ↓reduceIte] at uniform
        omega
      · rw [edgeRequests_append, lastEdges]
        simp only [SourceCurrentAllocatedFiniteOrdinaryParentResources.edgeBudget, test, Bool.false_eq_true, ↓reduceIte] at uniform
        omega

/-- Full initial caller facts give the same raw parent body's uniform Work trace. -/
theorem edge_body (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {budget : Nat} {request : SourceCurrentAllocatedPartialState.EdgeRequest} {before after : Caller width} {result : EdgeValue Symbol Guard}
    {actual : SourceCurrentAllocatedPartialGraph.EdgeBody budget request before result after} {memos final : Memos}
    (reads : SourceCurrentAllocatedPartialSourceReads.EdgeBodyReads formulas solver actual memos final)
    (inventory : Inventory) (initial : SourceCurrentAllocatedPartialInvariant.Context formulas solver inventory before memos)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (stored : SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeState.Stored before)
    (limits : Limits) (rows arity bound : Nat) (guards : SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge limits request.value)
    (profile : EdgeShape rows arity request.value) (heightBound : edgeHeight request.value ≤ bound) :
    ∃ requests, Trace before.checked.native.machine.heap after.checked.native.machine.heap requests ∧
      nodeRequests requests ≤ SourceCurrentAllocatedFiniteOrdinaryParentUniformBudgets.nodeBudget limits rows arity bound ∧
      edgeRequests requests ≤ SourceCurrentAllocatedFiniteOrdinaryParentUniformBudgets.edgeBudget limits rows arity bound := by
  cases reads with
  | parent parentReads =>
      rename_i edge loaded originalInherited checked fourth merge field parent
      have live : contradictory edge.entry.key.constraint = false →
          SourceEqualityGuardReadback.Cached edge.entry.key.constraint.equalities ∧
          SourceEqualityConstraintFieldLookup.load edge.entry.key.constraint before.checked.operations.constraints = .ok (some loaded) ∧
          SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints originalInherited ∧
          Values before.checked.native.machine.heap edge.children := by
        intro test
        exact ⟨(initial.ready.good.fields edge.entry.key edge resident).1, field test, inherited,
          initial.ready.semantic.ready.semantic.1.normal.facts.cached.edges _ edge resident⟩
      exact structure_from_reads formulas solver inventory edge parentReads initial.ready initial.admitted live initial.correct
        initial.stored initial.covered stored.base.base.native stored.base.base.profiles stored.base.base.output initial.globals
        limits rows arity bound guards profile heightBound

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryActualParentWork
