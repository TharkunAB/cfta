import MicroCFTA.SourceCurrentNativeOptionalOwner

/-!
# A source-built pair reaches its own compiled optional instruction

Both operands are actual raw Mu results. The admitted prefix starts at a
node query. It stops at the compiled optional instruction before that
instruction executes or the owner returns.
-/
noncomputable section
namespace MicroCFTA.NativeCompiledOwnerFixture
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
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

private def firstSource : Syntax Symbol Guard := .binder false (.union [])
private def secondSource : Syntax Symbol Guard :=
  .binder false (.node [.mk ("leaf",.top) SourceEqualityConstraintConstructors.top []])
private def firstBuilt := InternedFreshOrdinaryConstruction.build firstSource [] (empty : Heap)
private def left : Node := .mu ⟨0,.mu ⟨.empty,.empty⟩⟩ .empty .empty .empty
private def firstHeap : Heap := firstBuilt.state
private def secondBuilt := InternedFreshOrdinaryConstruction.build secondSource [] firstHeap
private def leaf : Node := .node ⟨1,.node [0]⟩
  [.mk ⟨0,⟨("leaf",.top),[],SourceEqualityConstraintConstructors.top⟩⟩ []] 0 []
private def right : Node := .mu ⟨2,.mu ⟨.node 1,.node 1⟩⟩ leaf leaf leaf
private def heap : Heap := secondBuilt.state
private def before : Checked 8 :=
  ⟨initial 8 ⟨heap,Cache.emptyState⟩,SourceEqualityConstraintMemoAllocation.empty⟩
private def request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain,left,right⟩
private def first : Nat := (SourceRecursiveIntersectionControl.identity left).getD 0
private def second : Nat := (SourceRecursiveIntersectionControl.identity right).getD 0
private def pair := SourceRecursiveIntersectionControl.pair first second
private def finish (value : Node) : Code Symbol Guard Node := .finishNode 0 value (.pure value)
private def compilerBefore : Checked 8 := (step (.code (requestNode request.domain left right)) before).state
private def entered := SourceRecursiveIntersectionEnvironment.enter compilerBefore.native.machine.domains
  request.domain.key left right first second
private def childBefore : Checked 8 :=
  {compilerBefore with native := advance compilerBefore.native {compilerBefore.native.machine with domains := entered.2}}
private def child : NodeRequest Symbol Guard := ⟨entered.1,body left,body right⟩
private def childNext (value : Node) : Code Symbol Guard Node := .optionalBinder pair value finish

private def siteBefore : Checked 8 := (step (.code (.node child childNext)) childBefore).state

private theorem first_done : firstBuilt = .done left firstHeap := by cbv
private theorem second_done : secondBuilt = .done right heap := by cbv
private theorem shapes : (∃ entry stored depth ordinary, left = .mu entry stored depth ordinary) ∧
    (∃ entry stored depth ordinary, right = .mu entry stored depth ordinary) ∧ left ≠ right := by
  constructor
  · exact ⟨_,_,_,_,rfl⟩
  constructor
  · exact ⟨_,_,_,_,rfl⟩
  · intro same
    have identities := congrArg SourceRecursiveIntersectionControl.identity same
    change some 0 = some 2 at identities
    cases identities
private theorem decision : SourceRecursiveIntersectionControl.decision request.domain.key left right = .bothMu := by cbv
private theorem first_available : Available firstHeap left :=
  (InternedFreshOrdinaryFacts.build_verified firstSource [] empty InternedNestedFacts.empty_facts
    (by intro value member; cases member)).result left firstHeap first_done
private theorem first_facts : InternedNestedFacts.Facts firstHeap :=
  (InternedFreshOrdinaryFacts.build_verified firstSource [] empty InternedNestedFacts.empty_facts
    (by intro value member; cases member)).facts
private theorem second_available : Available heap right :=
  (InternedFreshOrdinaryFacts.build_verified secondSource [] firstHeap first_facts
    (by intro value member; cases member)).result right heap second_done
private theorem left_available : Available heap left := by
  have checked := InternedFreshOrdinaryFacts.build_verified secondSource [] firstHeap first_facts
    (by intro value member; cases member)
  exact first_available.grows firstHeap heap checked.growth checked.history
private theorem semantic : SemanticHeap heap :=
  SourceRecursiveIntersectionSemanticHeap.source secondSource [] firstHeap
    (SourceRecursiveIntersectionSemanticHeap.source firstSource [] empty
      SourceRecursiveIntersectionSemanticHeap.empty_heap (by intro value member; cases member))
    (by intro value member; cases member)
private theorem query_inputs : SourceCurrentAllocatedNativePhysicalExecution.Inputs
    (.code (requestNode request.domain left right)) before := by
  refine ⟨⟨empty_domain _,left_available,second_available⟩,?_⟩
  intro key actual
  exact ⟨by decide,by decide,.mu 0,.mu 2,rfl,rfl,by unfold IntersectionFlatMemoKey.Safe IntersectionFlatMemoKey.code; decide,by unfold IntersectionFlatMemoKey.Safe IntersectionFlatMemoKey.code; decide⟩
private theorem enter_inputs : SourceCurrentAllocatedNativePhysicalExecution.Inputs
    (.code ((compileNode request).bind finish)) compilerBefore := by
  have selected : compileNode request = compileMu request.domain left right := by cbv
  rw [selected]
  change Domain compilerBefore.native.machine request.domain ∧ Available heap left ∧ Available heap right
  exact ⟨empty_domain _,left_available,second_available⟩
private theorem child_inputs : SourceCurrentAllocatedNativePhysicalExecution.Inputs
    (.code (.node child childNext)) childBefore := by
  have valid : SourceRecursiveIntersectionKernel.Valid compilerBefore.native.machine :=
    ⟨(InternedFreshOrdinaryFacts.build_verified secondSource [] firstHeap first_facts
      (by intro value member; cases member)).facts,Cache.empty_valid⟩
  have known := (SourceRecursiveIntersectionKernel.entered compilerBefore.native.machine valid request.domain (empty_domain _) left right
    left_available second_available first second).2.2
  refine ⟨⟨known,?_,?_⟩,?_⟩
  · change Available heap .empty
    exact empty_available _
  · change Available heap (body right)
    exact body_available heap right second_available
  · intro key actual
    exact ⟨by decide,by decide,.empty,.node 1,rfl,rfl,True.intro,by unfold IntersectionFlatMemoKey.Safe IntersectionFlatMemoKey.code; decide⟩
private theorem query_step : step (.code (requestNode request.domain left right)) before =
    .yielded (.code ((compileNode request).bind finish)) compilerBefore := by cbv
private theorem enter_step : step (.code ((compileNode request).bind finish)) compilerBefore =
    .yielded (.code (.node child childNext)) childBefore := by cbv
private theorem child_step : step (.code (.node child childNext)) childBefore =
    .yielded (.code (.finishNode 1 .empty (.optionalBinder pair .empty finish))) siteBefore := by cbv
private theorem finish_inputs : SourceCurrentAllocatedNativePhysicalExecution.Inputs
    (.code (.finishNode 1 .empty (.optionalBinder pair .empty finish))) siteBefore := by
  refine ⟨child,?_,empty_available _⟩
  cbv
private theorem finish_step : step (.code (.finishNode 1 .empty (.optionalBinder pair .empty finish))) siteBefore =
    .yielded (.code (.optionalBinder pair .empty finish))
      ⟨SourceRecursiveIntersectionThunks.finishNode 1 .empty siteBefore.native,siteBefore.operations⟩ := by rfl
private def after : Checked 8 :=
  ⟨SourceRecursiveIntersectionThunks.finishNode 1 .empty siteBefore.native,siteBefore.operations⟩
private theorem actual : Trace 4 (.code (requestNode request.domain left right)) before
    (.code (.optionalBinder pair .empty finish)) after := by
  exact .cons _ _ _ _ _ _ 3 query_inputs query_step
    (.cons _ _ _ _ _ _ 2 enter_inputs enter_step
      (.cons _ _ _ _ _ _ 1 child_inputs child_step
        (.cons _ _ _ _ _ _ 0 finish_inputs finish_step (.refl _ _))))

/-- A real source-built node query reaches its own optional site without completing its owner. -/
theorem compiled_site :
    firstBuilt = .done left firstHeap ∧ secondBuilt = .done right heap ∧
    (∃ entry stored depth ordinary, left = .mu entry stored depth ordinary) ∧
    (∃ entry stored depth ordinary, right = .mu entry stored depth ordinary) ∧
    left ≠ right ∧ SourceRecursiveIntersectionControl.decision request.domain.key left right = .bothMu ∧
    SemanticHeap heap ∧ Available heap left ∧ Available heap right ∧
    Trace 4 (.code (requestNode request.domain left right)) before
      (.code (.optionalBinder pair .empty finish)) after ∧
    SourceCurrentNativeOptionalOwnerReceipt.Owner 4 (.code (requestNode request.domain left right)) before
      pair .empty finish after :=
  ⟨first_done,second_done,shapes.1,shapes.2.1,shapes.2.2,decision,semantic,left_available,second_available,actual,
    SourceCurrentNativeOptionalOwner.request request 4 before after pair .empty finish actual⟩

end MicroCFTA.NativeCompiledOwnerFixture
