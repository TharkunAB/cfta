import MicroCFTA.SourceCurrentNativeMuOptionalSite

/-!
# A caller-written optional binder installs a selected Mu

The source builds an open ordinary body with an actual repeated-pair
capture. A pure instruction precedes the optional binder. Another pure
instruction follows it. The actual three-step trace supplies all checks.
One locator application retains the same recovered occurrence.
-/
namespace MicroCFTA.NativeOptionalSiteFixture
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

private def pair : Nat × Nat := (0,1)
private def capture : Node := .reference (.intersection pair.1 pair.2)
private def inputs : List Node := [capture]
private def expression : Syntax Symbol Guard :=
  .node [.mk ("loop",.top) SourceEqualityConstraintConstructors.top [.var 0]]
private def built := InternedFreshOrdinaryConstruction.build expression inputs (empty : Heap)
private def body : Node := match built with | .done value _ => value | .pending .. => .empty
private def heap : Heap := built.state
private def before : Checked 8 :=
  ⟨initial 8 ⟨heap,Cache.emptyState⟩,SourceEqualityConstraintMemoAllocation.empty⟩
private def bound := SourceRecursiveIntersectionMaybeMu.maybeMu pair body heap
private def result : Node := match bound with | .done value _ => value | .pending .. => .empty
private def operationHeap : Heap := bound.state
private def after : Checked 8 :=
  ⟨advance before.native {before.native.machine with heap := operationHeap},before.operations⟩
private def entry := match result with
  | .mu entry _ _ _ => entry
  | _ => (Cache.intern (empty : Heap).nodes .empty).1
private def storedBody : Node := match result with | .mu _ body _ _ => body | _ => .empty
private def depth : Node := match result with | .mu _ _ depth _ => depth | _ => .empty
private def ordinary : Node := match result with | .mu _ _ _ ordinary => ordinary | _ => .empty
private def suffix (value : Node) : Code Symbol Guard Node :=
  .work (.pure ()) (fun _ => .pure value)
private def binder : Code Symbol Guard Node := .optionalBinder pair body suffix
private def control : Control Node := .code (.work (.pure ()) (fun _ => binder))

private theorem built_done : built = .done body heap := by cbv
private theorem bound_done : bound = .done result operationHeap := by cbv
private theorem shape : result = .mu entry storedBody depth ordinary := by cbv
private theorem missing : before.native.machine.heap.nodeRecords entry.key = none := by cbv
private theorem present : after.native.machine.heap.nodeRecords entry.key = some result := by cbv
private theorem capture_available : Available (empty : Heap) capture := by
  apply reference_available (empty : Heap) (.intersection pair.1 pair.2)
  intro name member
  simp [Value.free] at member
private theorem inputs_available : InternedNestedProvenance.Values (empty : Heap) inputs := by
  intro value member
  have same : value = capture := List.mem_singleton.mp member
  subst value
  exact capture_available
private theorem semantic : SemanticHeap before.native.machine.heap :=
  SourceRecursiveIntersectionSemanticHeap.source expression inputs empty
    SourceRecursiveIntersectionSemanticHeap.empty_heap inputs_available
private theorem body_available : Available before.native.machine.heap body :=
  (InternedFreshOrdinaryFacts.build_verified expression inputs empty InternedNestedFacts.empty_facts inputs_available).result
    body heap built_done
private theorem first_step : step control before = .yielded (.code binder) before := by cbv
private theorem binder_step : step (.code binder) before = .yielded (.code (suffix result)) after := by cbv
private theorem last_step : step (.code (suffix result)) after = .yielded (.code (.pure result)) after := by cbv
private theorem actual : Trace 3 control before (.code (.pure result)) after := by
  refine .cons control before (.code binder) before (.code (.pure result)) after 2 ?_ first_step ?_
  · exact SourceEqualityNativeDemandHeapPrimitives.WorkInputs.pure ()
  · refine .cons (.code binder) before (.code (suffix result)) after (.code (.pure result)) after 1
      body_available binder_step ?_
    exact .cons (.code (suffix result)) after (.code (.pure result)) after (.code (.pure result)) after 0
      (SourceEqualityNativeDemandHeapPrimitives.WorkInputs.pure ()) last_step (.refl _ _)

private theorem checked_witness :
    built = .done body heap ∧ SemanticHeap before.native.machine.heap ∧
    Available before.native.machine.heap body ∧
    bound = .done result operationHeap ∧ result = .mu entry storedBody depth ordinary ∧
    before.native.machine.heap.nodeRecords entry.key = none ∧
    after.native.machine.heap.nodeRecords entry.key = some result ∧
    Trace 3 control before (.code (.pure result)) after ∧
  ∃ prefixFuel suffixFuel sitePair siteBody next siteBefore siteAfter siteResult siteHeap,
    3 = prefixFuel + 1 + suffixFuel ∧
    Trace prefixFuel control before (.code (.optionalBinder sitePair siteBody next)) siteBefore ∧
    SemanticHeap siteBefore.native.machine.heap ∧ Available siteBefore.native.machine.heap siteBody ∧
    SourceRecursiveIntersectionMaybeMu.maybeMu sitePair siteBody siteBefore.native.machine.heap = .done siteResult siteHeap ∧
    siteAfter = ⟨advance siteBefore.native {siteBefore.native.machine with heap := siteHeap},siteBefore.operations⟩ ∧
    step (.code (.optionalBinder sitePair siteBody next)) siteBefore = .yielded (.code (next siteResult)) siteAfter ∧
    Trace suffixFuel (.code (next siteResult)) siteAfter (.code (.pure result)) after ∧
    siteBefore.native.machine.heap.nodeRecords entry.key = none ∧ siteHeap.nodeRecords entry.key = some result ∧
    Grows before.native.machine.heap siteBefore.native.machine.heap ∧
    Extends before.native.machine.heap.nodes.issued siteBefore.native.machine.heap.nodes.issued ∧
    Grows siteHeap after.native.machine.heap ∧ Extends siteHeap.nodes.issued after.native.machine.heap.nodes.issued := by
  have selected : after.native.machine.heap.nodeRecords entry.key = some (.mu entry storedBody depth ordinary) := by
    rw [←shape]
    exact present
  rcases SourceCurrentNativeMuOptionalSite.trace actual semantic entry.key entry storedBody depth ordinary selected with prior | site
  · rw [missing] at prior
    cases prior
  · refine ⟨built_done,semantic,body_available,bound_done,shape,missing,present,actual,?_⟩
    simpa only [←shape] using site

/-- The actual three-step caller-written trace derives its selected new Mu's exact optional-binder occurrence. -/
theorem actual_optional_site :
    built = .done body heap ∧ SemanticHeap before.native.machine.heap ∧
    Available before.native.machine.heap body ∧
    bound = .done result operationHeap ∧ result = .mu entry storedBody depth ordinary ∧
    before.native.machine.heap.nodeRecords entry.key = none ∧
    after.native.machine.heap.nodeRecords entry.key = some result ∧
    Trace 3 control before (.code (.pure result)) after ∧
  ∃ prefixFuel suffixFuel sitePair siteBody next siteBefore siteAfter siteResult siteHeap,
    3 = prefixFuel + 1 + suffixFuel ∧
    Trace prefixFuel control before (.code (.optionalBinder sitePair siteBody next)) siteBefore ∧
    SemanticHeap siteBefore.native.machine.heap ∧ Available siteBefore.native.machine.heap siteBody ∧
    SourceRecursiveIntersectionMaybeMu.maybeMu sitePair siteBody siteBefore.native.machine.heap = .done siteResult siteHeap ∧
    siteAfter = ⟨advance siteBefore.native {siteBefore.native.machine with heap := siteHeap},siteBefore.operations⟩ ∧
    step (.code (.optionalBinder sitePair siteBody next)) siteBefore = .yielded (.code (next siteResult)) siteAfter ∧
    Trace suffixFuel (.code (next siteResult)) siteAfter (.code (.pure result)) after ∧
    siteBefore.native.machine.heap.nodeRecords entry.key = none ∧ siteHeap.nodeRecords entry.key = some result ∧
    Grows before.native.machine.heap siteBefore.native.machine.heap ∧
    Extends before.native.machine.heap.nodes.issued siteBefore.native.machine.heap.nodes.issued ∧
    Grows siteHeap after.native.machine.heap ∧ Extends siteHeap.nodes.issued after.native.machine.heap.nodes.issued := checked_witness

end MicroCFTA.NativeOptionalSiteFixture
