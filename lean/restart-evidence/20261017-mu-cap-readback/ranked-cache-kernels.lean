import MicroCFTA.SourceCurrentConstrainedCapNativeOccurrenceTrace

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.RankedCacheKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency InternedNestedFacts
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceCurrentConstrainedCapNativeOccurrenceCache
open SourceCurrentConstrainedCapPairOccurrences (Classified sourceWeight)
open SourceCurrentConstrainedCapNonplainRank (pairRank)
variable {Symbol Guard : Type} {width : Nat}

private theorem original_classified (annotation : Guard → Prop) (source : State Symbol Guard) (facts : Facts source)
    (value : Value Symbol Guard) (original : SourceRecursiveIntersectionInputView.Original value)
    (available : Available source value) (bound : Nat) : Classified (sourceWeight annotation source) bound value := by
  apply SourceCurrentConstrainedCapPairOccurrences.of_below _ bound value source facts.coherent available
  · intro name member
    obtain ⟨number, rfl⟩ := original.free_interned source facts value available name member
    exact Nat.zero_le _
  · intro name member
    obtain ⟨number, rfl⟩ := original.free_interned source facts value available name member
    cases bound with
    | zero => exact .inr rfl
    | succ bound => exact .inl (Nat.zero_lt_succ _)

/-- A closed self branch constructs its result, installs its law, and produces an exact warm hit. -/
theorem cold_self_then_warm [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (machine : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid machine)
    (request : NodeRequest Symbol Guard) (ready : NodeReady machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (key : IntersectionFlatMemoKeyDomain.Triple width)
    (requested : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key)
    (branch : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .self)
    (depth : Nat) (bindings : OriginalBindings annotation machine.heap request.domain.key)
    (inputs : NodeInputs machine.heap request)
    (leftCap : SourceCurrentConstrainedCap.Cap annotation depth request.left)
    (rightCap : SourceCurrentConstrainedCap.Cap annotation depth request.right) :
    ∃ after,
      SourceRecursiveIntersectionNative.execute emptyGuard conjoin 3
        (requestNode request.domain request.left request.right) (initial width machine) = .done request.left after ∧
      SourceCurrentAllocatedNativePhysicalCache.Valid after ∧
      SourceCurrentConstrainedCapNativeOccurrenceCache.Stored annotation machine.heap after ∧
      lookupNode width request after = (.memoized 0, after) ∧
      demandNode 0 after = (.ready request.left, after) ∧
      SourceCurrentConstrainedCapPairOccurrences.Classified (SourceCurrentConstrainedCapPairOccurrences.sourceWeight annotation machine.heap)
        (SourceCurrentConstrainedCapNonplainRank.pairRank annotation request.left request.right) request.left := by
  have law : NodeLaw annotation machine.heap request request.left := by
    intro _ _ supported _ _
    exact original_classified annotation machine.heap valid.1 request.left supported.1 supported.2.2.1 _
  let before := initial width machine
  let chosen := (lookupNode width request before).2
  let running := (demandNode 0 chosen).2
  let after := finishNode 0 request.left running
  have selected : lookupNode width request before = (.memoized 0, chosen) := by
    simp [chosen, before, initial, lookupNode, requested, FlatMemoThunk.lookupOrInsert, FlatMemoThunk.empty]
  have demanded : demandNode 0 chosen = (.evaluate request, running) := by
    simp [running, chosen, before, initial, lookupNode, requested, demandNode,
      FlatMemoThunk.lookupOrInsert, FlatMemoThunk.empty, FlatMemoThunk.demand, Cache.put]
  have started := SourceCurrentConstrainedCapNativeOccurrenceCache.node_started annotation machine.heap request request
    before chosen running 0 (SourceCurrentAllocatedNativePhysicalCache.initial_valid machine valid)
    (SourceCurrentConstrainedCapNativeOccurrenceCache.initial_stored annotation machine.heap width machine)
    ready safe selected demanded
  have available := (started.2.1.nodes.checked 0 _ started.2.2.2).1.2.1
  have afterValid := SourceCurrentAllocatedNativePhysicalCache.finishNode_valid running started.2.1
    0 request request.left started.2.2.2 available
  have afterStored := SourceCurrentConstrainedCapNativeOccurrenceCache.finishNode_stored annotation machine.heap running
    0 request request.left started.2.1 started.2.2.1 started.2.2.2 (fun _ _ left _ => left) law
  have cell : after.nodes.cells 0 = some ⟨request, .returned request.left⟩ := by
    simp [after, finishNode, FlatMemoThunk.finish, started.2.2.2, FlatMemoThunk.setStatus, Cache.put]
  have published : after.nodes.table key = some 0 := by
    simp [after, running, chosen, before, initial, lookupNode, requested, demandNode, finishNode,
      FlatMemoThunk.lookupOrInsert, FlatMemoThunk.empty, FlatMemoThunk.demand, FlatMemoThunk.finish,
      FlatMemoThunk.setStatus, Cache.put]
  have afterReady : NodeReady after.machine request :=
    (afterValid.nodes.checked 0 _ cell).1
  have hit := SourceCurrentAllocatedNativePhysicalCache.node_ready_receipt after afterValid request request afterReady
    key ⟨requested, safe⟩ 0 published request.left cell
  refine ⟨after, ?_, afterValid, afterStored, hit.2.1, hit.2.2.1, law depth bindings inputs leftCap rightCap⟩
  have compiled : compileNode request = .pure request.left := by
    simp only [compileNode, branch]
  have first : SourceRecursiveIntersectionNative.step emptyGuard conjoin (.node request .pure) before =
      .yielded (.finishNode 0 request.left (.pure request.left)) running := by
    simp only [SourceRecursiveIntersectionNative.step, selected, demanded, compiled, Code.bind]
  change SourceRecursiveIntersectionNative.execute emptyGuard conjoin 3 (.node request .pure) before = _
  rw [SourceRecursiveIntersectionNative.execute, first]
  rfl

/-- The row budget follows repeated zipped positions even when the input row arities differ. -/
theorem repeated_zip_budget (annotation : Guard → Prop) (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (first second : Interned (EdgeKey Symbol Guard)) (value : Value Symbol Guard) :
    let request : EdgeRequest Symbol Guard := ⟨domain, .mk first [value, value, .empty], .mk second [value, value]⟩
    edgeBudget annotation request = pairRank annotation value value ∧
      edgeBudget annotation request < pairRank annotation value value + 1 := by
  dsimp only
  have exactBudget : edgeBudget annotation ⟨domain, .mk first [value, value, .empty], .mk second [value, value]⟩ =
      pairRank annotation value value := by
    simp [edgeBudget, childBudget, EdgeValue.children]
  refine ⟨exactBudget, ?_⟩
  apply edgeBudget_lt annotation _ _ (by omega)
  intro pair member
  simp only [EdgeValue.children, List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact Nat.lt_succ_self _

section ActualTrace
local notation "ConcreteSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "ConcreteGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State

/-- The same zero-step self body derives both laws before its literal captured finish. -/
theorem actual_self_publication [DecidableEq ConcreteSymbol] [DecidableEq (EdgeKey ConcreteSymbol ConcreteGuard)]
    (annotation : ConcreteGuard → Prop) (source : State ConcreteSymbol ConcreteGuard)
    (inventory : List IntersectionFlatMemoKeyDomain.DomainKey) (initialDomains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey)
    (request : NodeRequest ConcreteSymbol ConcreteGuard) (before : Checked width) (handle : Nat)
    (known : SourceCurrentAllocatedRecursivePrefixState.Current source inventory initialDomains before)
    (stored : SourceCurrentConstrainedCapNativeTraceGlue.Stored annotation before)
    (ranked : SourceCurrentConstrainedCapNativeOccurrenceCache.Stored annotation source before.native)
    (facts : Facts source)
    (running : before.native.nodes.cells handle = some ⟨request, .evaluating⟩)
    (branch : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .self) :
    SourceCurrentConstrainedCapNativeTraceGlue.Receipt annotation source inventory initialDomains 1
      ((.code (compileNode request) : SourceEqualityNativeDemand.Control (Value ConcreteSymbol ConcreteGuard)).bind
        (fun value => .finishNode handle value (.pure value)))
      before request.left {before with native := finishNode handle request.left before.native}
      (fun state value => Available state.heap value)
      (fun _ value => (∀ scope, SourceCurrentConstrainedCapNativeLaws.NodeLaw annotation scope request value) ∧
        SourceCurrentConstrainedCapNativeOccurrenceCache.NodeLaw annotation source request value) ∧
    SourceCurrentConstrainedCapNativeOccurrenceCache.Stored annotation source (finishNode handle request.left before.native) ∧
    (finishNode handle request.left before.native).nodes.cells handle = some ⟨request, .returned request.left⟩ := by
  have available := (known.good.native.nodes.checked handle _ running).1.2.1
  have compiled : compileNode request = .pure request.left := by simp only [compileNode, branch]
  have physical : SourceCurrentAllocatedRecursivePrefixReceipt.Receipt source inventory initialDomains 0
      (.code (compileNode request)) before (.code (.pure request.left)) before
      (fun state value => Available state.heap value) := by
    rw [compiled]
    exact SourceCurrentAllocatedRecursivePrefixReceipt.zero _ _ known trivial trivial trivial
      (by intro value same; cases same; exact available)
  have law : SourceCurrentConstrainedCapNativeOccurrenceCache.NodeLaw annotation source request request.left := by
    intro _ _ supported _ _
    exact original_classified annotation source facts request.left supported.1 supported.2.2.1 _
  exact SourceCurrentConstrainedCapNativeOccurrenceTrace.finish_node request known running
    ⟨physical, stored, ⟨fun _ _ _ left _ => left, law⟩⟩ ranked

#print axioms actual_self_publication
#check @actual_self_publication
end ActualTrace

#print axioms cold_self_then_warm
#check @cold_self_then_warm
#print axioms repeated_zip_budget
#check @repeated_zip_budget
end MicroCFTA.RankedCacheKernels
