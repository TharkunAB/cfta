import MicroCFTA.SourceCurrentNativeMuStoppingGeneration

/-!
# Staged calculation of one blocked nested-allocation candidate
-/
namespace MicroCFTA.NativeBlockedAllocationFixture
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open InternedStoredSubstitution (leaves encode)
open InternedBinderProtocol (Reference)
open SourceCurrentCompletedBuildRootedWriters (Written)

local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000

private def pair : Nat × Nat := (0,1)
private def capture : Node := .reference (.intersection pair.1 pair.2)
private def expression : Syntax Symbol Guard :=
  .node [.mk ("outer7",.top) SourceEqualityConstraintConstructors.top
    [.binder false (.node [.mk ("inner8",.top) SourceEqualityConstraintConstructors.top [.var 1,.var 0]])]]
private def built := InternedFreshOrdinaryConstruction.build expression [capture] (empty : Heap)
private def valueOf : InternedNestedConstruction.Outcome Symbol Guard Node → Node
  | .done value _ => value
  | .pending .. => .empty
private def body : Node := valueOf built
private def base : Heap := built.state
private def reserve (heap : Heap) (key : InternedBinderProtocol.NodeKey) : Heap :=
  {heap with nodes := (Cache.intern heap.nodes key).2}
private def oracle : Heap := reserve base .empty
private def oracleDepth := SourceRecursiveIntersectionMaybeMu.callback
  (.intersection pair.1 pair.2) body .depth oracle
private def oracleOrdinary := SourceRecursiveIntersectionMaybeMu.callback
  (.intersection pair.1 pair.2) body
  (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel (valueOf oracleDepth))) oracleDepth.state
private def outerKey := muKey (valueOf oracleDepth) (valueOf oracleOrdinary)
private def warm : Heap := reserve base outerKey
private def actualDepth := SourceRecursiveIntersectionMaybeMu.callback
  (.intersection pair.1 pair.2) body .depth warm
private def actualOrdinary := SourceRecursiveIntersectionMaybeMu.callback
  (.intersection pair.1 pair.2) body
  (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel (valueOf actualDepth))) actualDepth.state
private def bound := SourceRecursiveIntersectionMaybeMu.maybeMu pair body warm
private def suffix (value : Node) : Code Symbol Guard Node :=
  .work (.pure ()) (fun _ => .pure value)
private def binder : Code Symbol Guard Node := .optionalBinder pair body suffix
private def control : Control Node := .code (.work (.pure ()) (fun _ => binder))
private def before : Checked 64 :=
  ⟨initial 64 ⟨warm,Cache.emptyState⟩,SourceEqualityConstraintMemoAllocation.empty⟩
private noncomputable def outcome := SourceEqualityNativeDemand.execute 3 control before
private def after : Checked 64 :=
  ⟨advance before.native {before.native.machine with heap := bound.state},before.operations⟩


private def firstChild : Node → Node
  | .node _ (.mk _ (first :: _) :: _) _ _ => first
  | _ => .empty
private def target : Node := firstChild (valueOf actualDepth)
private def targetEntry := match target with
  | .mu entry .. => entry
  | _ => (Cache.intern (empty : Heap).nodes .empty).1
private def targetKey := targetEntry.key
private def targetBody : Node := match target with | .mu _ body _ _ => body | _ => .empty
private def targetDepth : Node := match target with | .mu _ _ depth _ => depth | _ => .empty
private def targetOrdinary : Node := match target with | .mu _ _ _ ordinary => ordinary | _ => .empty

private theorem built_done : built = .done body base := by cbv
private theorem oracle_depth_done : oracleDepth = .done (valueOf oracleDepth) oracleDepth.state := by cbv
private theorem oracle_ordinary_done : oracleOrdinary = .done (valueOf oracleOrdinary) oracleOrdinary.state := by cbv
private theorem actual_depth_done : actualDepth = .done (valueOf oracleDepth) actualDepth.state := by cbv
private theorem actual_ordinary_done : actualOrdinary = .done (valueOf oracleOrdinary) actualOrdinary.state := by cbv
private theorem bound_pending : bound = .pending outerKey actualOrdinary.state := by cbv
private theorem target_shape : target = .mu targetEntry targetBody targetDepth targetOrdinary := by cbv
private theorem target_missing : warm.nodeRecords targetKey = none := by cbv
private theorem target_present : bound.state.nodeRecords targetKey = some target := by cbv
private theorem target_distinct : targetKey ≠ outerKey := by
  intro same
  cbv at same
  cases same
private theorem target_used : InternedFreshOrdinaryDepthHeap.usesLocal targetDepth targetOrdinary = true := by cbv
private theorem reservation_facts :
    base.nodes.table .empty = none ∧ base.nodes.table outerKey = none ∧
    oracle.nodes.next = base.nodes.next + 1 ∧ warm.nodes.next = base.nodes.next + 1 ∧
    warm.nodes.table outerKey = some (Cache.intern base.nodes outerKey).1 ∧
    warm.nodeRecords outerKey = none ∧ actualOrdinary.state.nodeRecords outerKey = none := by cbv

private theorem capture_available : Available (empty : Heap) capture := by
  apply reference_available (empty : Heap) (.intersection pair.1 pair.2)
  intro name member
  simp [Value.free] at member
private theorem initial_context : SourceCurrentConstrainedCapSourceHistory.Context (empty : Heap) [capture] :=
  SourceCurrentConstrainedCapSourceHistory.empty_context.local (.intersection pair.1 pair.2) capture_available
private theorem base_context : SourceCurrentConstrainedCapSourceHistory.Context base [capture] :=
  initial_context.build expression
private theorem warm_context : SourceCurrentConstrainedCapSourceHistory.Context warm [capture] :=
  base_context.reserve outerKey
private theorem oracle_context : SourceCurrentConstrainedCapSourceHistory.Context oracle [capture] :=
  base_context.reserve .empty
private theorem body_available_base : Available base body :=
  (InternedFreshOrdinaryFacts.build_verified expression [capture] empty
    InternedNestedFacts.empty_facts initial_context.base.inputs).result body base built_done
private theorem body_available : Available before.native.machine.heap body := by
  have growth : Grows base warm :=
    ⟨extends_refl _,InternedBinderProtocol.intern_grows base.nodes outerKey,extends_refl _,extends_refl _⟩
  have issued := InternedFreshProbeKeys.intern_issued_extends base.nodes outerKey
    base_context.base.normal.facts.coherent.valid.2
  exact body_available_base.grows base warm growth issued
private theorem semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap before.native.machine.heap :=
  ⟨⟨warm_context.base.normal,(by intro value member; cases member),
    warm_context.base.profiles,warm_context.base.freeNames⟩,warm_context.depth⟩
private theorem first_step : step control before = .yielded (.code binder) before := by cbv
private theorem binder_step : step (.code binder) before =
    .blocked (.native (.constructor outerKey)) (.code binder) after := by cbv
private theorem actual_inputs : SourceCurrentAllocatedNativePhysicalExecution.InputsThrough 3 control before := by
  refine ⟨SourceEqualityNativeDemandHeapPrimitives.WorkInputs.pure (),?_⟩
  simp only [first_step]
  refine ⟨body_available,?_⟩
  simp only [binder_step]
private theorem stopped : outcome = .blocked (.native (.constructor outerKey)) (.code binder) after := by
  simp only [outcome,SourceEqualityNativeDemand.execute,first_step,binder_step]

private theorem checked_witness :
    built = .done body base ∧
    Context base [capture] ∧ Context oracle [capture] ∧ Context warm [capture] ∧
    base.nodes.table .empty = none ∧ base.nodes.table outerKey = none ∧
    oracle.nodes.next = base.nodes.next + 1 ∧ warm.nodes.next = base.nodes.next + 1 ∧
    warm.nodes.table outerKey = some (Cache.intern base.nodes outerKey).1 ∧
    warm.nodeRecords outerKey = none ∧ actualOrdinary.state.nodeRecords outerKey = none ∧
    oracleDepth = .done (valueOf oracleDepth) oracleDepth.state ∧
    oracleOrdinary = .done (valueOf oracleOrdinary) oracleOrdinary.state ∧
    actualDepth = .done (valueOf oracleDepth) actualDepth.state ∧
    actualOrdinary = .done (valueOf oracleOrdinary) actualOrdinary.state ∧
    bound = .pending outerKey actualOrdinary.state ∧
    target = .mu targetEntry targetBody targetDepth targetOrdinary ∧
    InternedFreshOrdinaryDepthHeap.usesLocal targetDepth targetOrdinary = true ∧
    targetKey ≠ outerKey ∧ warm.nodeRecords targetKey = none ∧
    bound.state.nodeRecords targetKey = some target ∧
    SemanticHeap before.native.machine.heap ∧ Available before.native.machine.heap body ∧
    SourceCurrentAllocatedNativePhysicalExecution.InputsThrough 3 control before ∧
    outcome = .blocked (.native (.constructor outerKey)) (.code binder) after ∧
    ∃ prefixFuel remainingFuel pair siteBody next siteBefore call siteStep,
      3 = prefixFuel + 1 + remainingFuel ∧
      Trace prefixFuel control before (.code (.optionalBinder pair siteBody next)) siteBefore ∧
      SourceCurrentAllocatedNativePhysicalExecution.Inputs (.code (.optionalBinder pair siteBody next)) siteBefore ∧
      SemanticHeap siteBefore.native.machine.heap ∧ Available siteBefore.native.machine.heap siteBody ∧
      SourceRecursiveIntersectionMaybeMu.maybeMu pair siteBody siteBefore.native.machine.heap = call ∧
      siteStep = (match call with
        | .done result heap => .yielded (.code (next result))
            ⟨advance siteBefore.native {siteBefore.native.machine with heap := heap},siteBefore.operations⟩
        | .pending pending heap => .blocked (.native (.constructor pending))
            (.code (.optionalBinder pair siteBody next))
            ⟨advance siteBefore.native {siteBefore.native.machine with heap := heap},siteBefore.operations⟩) ∧
      step (.code (.optionalBinder pair siteBody next)) siteBefore = siteStep ∧
      SourceEqualityNativeDemand.execute 3 control before = resume remainingFuel siteStep ∧
      siteBefore.native.machine.heap.nodeRecords targetKey = none ∧
      call.state.nodeRecords targetKey = some (.mu targetEntry targetBody targetDepth targetOrdinary) ∧
      Grows before.native.machine.heap siteBefore.native.machine.heap ∧
      Extends before.native.machine.heap.nodes.issued siteBefore.native.machine.heap.nodes.issued ∧
      Grows call.state (SourceEqualityNativeDemand.execute 3 control before).state.native.machine.heap ∧
      Extends call.state.nodes.issued (SourceEqualityNativeDemand.execute 3 control before).state.native.machine.heap.nodes.issued ∧
      Reference.intersection pair.1 pair.2 ∈ siteBody.free ∧
      Context siteBefore.native.machine.heap (leaves siteBody) ∧
      InternedFreshOrdinaryConstruction.build
        (.binder true (encode (leaves siteBody) [.intersection pair.1 pair.2] siteBody)) (leaves siteBody)
        siteBefore.native.machine.heap = call ∧
      Written (.binder true (encode (leaves siteBody) [.intersection pair.1 pair.2] siteBody)) (leaves siteBody)
        siteBefore.native.machine.heap call.state targetKey (.mu targetEntry targetBody targetDepth targetOrdinary) := by
  have atStop : outcome.state.native.machine.heap.nodeRecords targetKey = some target := by
    rw [stopped]
    exact target_present
  have selected : (SourceEqualityNativeDemand.execute 3 control before).state.native.machine.heap.nodeRecords targetKey =
      some (.mu targetEntry targetBody targetDepth targetOrdinary) := by
    rw [←target_shape]
    exact atStop
  rcases SourceCurrentNativeMuStoppingGeneration.execute actual_inputs semantic targetKey targetEntry
      targetBody targetDepth targetOrdinary selected with prior | site
  · change warm.nodeRecords targetKey = some (.mu targetEntry targetBody targetDepth targetOrdinary) at prior
    rw [target_missing] at prior
    cases prior
  · obtain ⟨dummyMissing,outerMissing,oracleNext,warmNext,reserved,orphan,stillOrphan⟩ := reservation_facts
    exact ⟨built_done,base_context,oracle_context,warm_context,dummyMissing,outerMissing,oracleNext,warmNext,
      reserved,orphan,stillOrphan,oracle_depth_done,oracle_ordinary_done,actual_depth_done,actual_ordinary_done,
      bound_pending,target_shape,target_used,target_distinct,target_missing,target_present,semantic,
      body_available,actual_inputs,stopped,site⟩

/-- The sole optional instruction stops pending after it installs a different full used Mu that was absent at entry. -/
theorem actual_blocked_nested_creation :
    built = .done body base ∧
    Context base [capture] ∧ Context oracle [capture] ∧ Context warm [capture] ∧
    base.nodes.table .empty = none ∧ base.nodes.table outerKey = none ∧
    oracle.nodes.next = base.nodes.next + 1 ∧ warm.nodes.next = base.nodes.next + 1 ∧
    warm.nodes.table outerKey = some (Cache.intern base.nodes outerKey).1 ∧
    warm.nodeRecords outerKey = none ∧ actualOrdinary.state.nodeRecords outerKey = none ∧
    oracleDepth = .done (valueOf oracleDepth) oracleDepth.state ∧
    oracleOrdinary = .done (valueOf oracleOrdinary) oracleOrdinary.state ∧
    actualDepth = .done (valueOf oracleDepth) actualDepth.state ∧
    actualOrdinary = .done (valueOf oracleOrdinary) actualOrdinary.state ∧
    bound = .pending outerKey actualOrdinary.state ∧
    target = .mu targetEntry targetBody targetDepth targetOrdinary ∧
    InternedFreshOrdinaryDepthHeap.usesLocal targetDepth targetOrdinary = true ∧
    targetKey ≠ outerKey ∧ warm.nodeRecords targetKey = none ∧
    bound.state.nodeRecords targetKey = some target ∧
    SemanticHeap before.native.machine.heap ∧ Available before.native.machine.heap body ∧
    SourceCurrentAllocatedNativePhysicalExecution.InputsThrough 3 control before ∧
    outcome = .blocked (.native (.constructor outerKey)) (.code binder) after ∧
    ∃ prefixFuel remainingFuel pair siteBody next siteBefore call siteStep,
      3 = prefixFuel + 1 + remainingFuel ∧
      Trace prefixFuel control before (.code (.optionalBinder pair siteBody next)) siteBefore ∧
      SourceCurrentAllocatedNativePhysicalExecution.Inputs (.code (.optionalBinder pair siteBody next)) siteBefore ∧
      SemanticHeap siteBefore.native.machine.heap ∧ Available siteBefore.native.machine.heap siteBody ∧
      SourceRecursiveIntersectionMaybeMu.maybeMu pair siteBody siteBefore.native.machine.heap = call ∧
      siteStep = (match call with
        | .done result heap => .yielded (.code (next result))
            ⟨advance siteBefore.native {siteBefore.native.machine with heap := heap},siteBefore.operations⟩
        | .pending pending heap => .blocked (.native (.constructor pending))
            (.code (.optionalBinder pair siteBody next))
            ⟨advance siteBefore.native {siteBefore.native.machine with heap := heap},siteBefore.operations⟩) ∧
      step (.code (.optionalBinder pair siteBody next)) siteBefore = siteStep ∧
      SourceEqualityNativeDemand.execute 3 control before = resume remainingFuel siteStep ∧
      siteBefore.native.machine.heap.nodeRecords targetKey = none ∧
      call.state.nodeRecords targetKey = some (.mu targetEntry targetBody targetDepth targetOrdinary) ∧
      Grows before.native.machine.heap siteBefore.native.machine.heap ∧
      Extends before.native.machine.heap.nodes.issued siteBefore.native.machine.heap.nodes.issued ∧
      Grows call.state (SourceEqualityNativeDemand.execute 3 control before).state.native.machine.heap ∧
      Extends call.state.nodes.issued (SourceEqualityNativeDemand.execute 3 control before).state.native.machine.heap.nodes.issued ∧
      Reference.intersection pair.1 pair.2 ∈ siteBody.free ∧
      Context siteBefore.native.machine.heap (leaves siteBody) ∧
      InternedFreshOrdinaryConstruction.build
        (.binder true (encode (leaves siteBody) [.intersection pair.1 pair.2] siteBody)) (leaves siteBody)
        siteBefore.native.machine.heap = call ∧
      Written (.binder true (encode (leaves siteBody) [.intersection pair.1 pair.2] siteBody)) (leaves siteBody)
        siteBefore.native.machine.heap call.state targetKey (.mu targetEntry targetBody targetDepth targetOrdinary) := checked_witness

end MicroCFTA.NativeBlockedAllocationFixture

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.NativeBlockedAllocationFixture.actual_blocked_nested_creation
#print MicroCFTA.NativeBlockedAllocationFixture.actual_blocked_nested_creation
#print axioms MicroCFTA.NativeBlockedAllocationFixture.actual_blocked_nested_creation
