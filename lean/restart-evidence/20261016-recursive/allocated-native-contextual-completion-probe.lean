import MicroCFTA.SourceCurrentAllocatedNativeContextualCompletion
namespace MicroCFTA.ContextualCompletionProbe
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView IntersectSchedule SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "WordRanges" => SourceCurrentAllocatedNativeRequestBounds.WordRanges
local notation "ActiveAbove" => SourceRecursiveIntersectionNative.ActiveAbove
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) :=
  SourceEqualityPCSNativeEdge.guardDecidableEq
#print axioms MicroCFTA.SourceCurrentAllocatedNativeContextualCode.certified_bind
#print axioms MicroCFTA.SourceCurrentAllocatedNativeContextualCompletion.Receipt.done
#print axioms MicroCFTA.SourceCurrentAllocatedNativeContextualCompletion.node_complete
#print axioms MicroCFTA.SourceCurrentAllocatedNativeContextualCompletion.edge_complete
#print axioms MicroCFTA.SourceCurrentAllocatedNativeContextualCompletion.request_complete
#print axioms MicroCFTA.SourceCurrentAllocatedNativeContextualCompletion.edge_request_complete
#print axioms MicroCFTA.SourceCurrentAllocatedNativeContextualCompletion.initial_complete
#print axioms MicroCFTA.SourceCurrentAllocatedNativeContextualCompletion.cold_complete
#check @MicroCFTA.SourceCurrentAllocatedNativeContextualCode.certified_bind
#check @MicroCFTA.SourceCurrentAllocatedNativeContextualCompletion.Receipt.done
#check @MicroCFTA.SourceCurrentAllocatedNativeContextualCompletion.node_complete
#check @MicroCFTA.SourceCurrentAllocatedNativeContextualCompletion.edge_complete
#check @MicroCFTA.SourceCurrentAllocatedNativeContextualCompletion.request_complete
#check @MicroCFTA.SourceCurrentAllocatedNativeContextualCompletion.edge_request_complete
#check @MicroCFTA.SourceCurrentAllocatedNativeContextualCompletion.initial_complete
#check @MicroCFTA.SourceCurrentAllocatedNativeContextualCompletion.cold_complete

example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {A : Type} {width fuel : Nat} {view : IntersectSchedule.View Symbol}
    {model : InputMeaning view} {ranked : RankedInput view model.valid} {holds : Guard → Term Symbol → Bool}
    {control : Control A} {before after : Checked width} {value : A}
    {post semanticPost : Machine Symbol Guard → A → Prop}
    (receipt : SourceCurrentAllocatedNativeContextualCompletion.Receipt
      (semanticView := view) (model := model) (ranked := ranked) (semanticHolds := holds)
      fuel control before value after post semanticPost) :
    execute (fuel + 1) control before = .done value after ∧
    SourceCurrentAllocatedNativeContextCache.Contextual view model ranked holds after.native ∧
    SemanticReady after.native.machine.heap ∧ post after.native.machine value ∧ semanticPost after.native.machine value ∧
    SourceCurrentAllocatedNativePhysicalExecution.InputsThrough (fuel + 1) control before :=
  ⟨receipt.done, receipt.contextual, receipt.semantic, receipt.result, receipt.law, receipt.trace.plan⟩

example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (machine : Machine Symbol Guard) (operations : SourceEqualityConstraintMemoAllocation.State)
    (valid : Good (⟨initial width machine, operations⟩ : Checked width))
    (semantic : SemanticReady machine.heap)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available machine.heap left) (rightAvailable : Available machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (ranges : WordRanges (.code (requestNode IntersectionEmptyDomain.emptyDomain left right))
      (⟨initial width machine, operations⟩ : Checked width)) :
    ∃ fuel value after,
      (∀ extra, execute (fuel + 1 + extra) (.code (requestNode IntersectionEmptyDomain.emptyDomain left right))
        (⟨initial width machine, operations⟩ : Checked width) = .done value after) ∧
      Good after ∧ SemanticReady after.native.machine.heap ∧ Available after.native.machine.heap value ∧
      SourceRecursiveIntersectionNative.Idle after.native ∧
      ∀ output term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output value term ↔
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output left term ∧
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output right term := by
  obtain ⟨model, ranked, fuel, value, after, receipt, idle, exactness⟩ :=
    SourceCurrentAllocatedNativeContextualCompletion.cold_complete formulas solver machine operations valid semantic
      left right leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed ranges
  exact ⟨fuel, value, after, (fun extra => done_stable (fuel + 1) extra _ _ _ _ receipt.done),
    receipt.good, receipt.semantic, receipt.result, idle, exactness⟩

example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : InternedNestedFacts.Facts source)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inputModel : InputMeaning (view source (SourceEqualityPCSGuard.holds formulas solver)))
    (inputRanked : RankedInput (view source (SourceEqualityPCSGuard.holds formulas solver)) inputModel.valid)
    (request : EdgeRequest Symbol Guard) (scope : EdgeScope source request)
    (complete : Completes (view source (SourceEqualityPCSGuard.holds formulas solver)) (SourceRecursiveIntersectionNative.edgeSemantic (SourceEqualityPCSGuard.holds formulas solver) request))
    (state : Checked width) (valid : Good state)
    (contextual : SourceCurrentAllocatedNativeContextCache.Contextual
      (view source (SourceEqualityPCSGuard.holds formulas solver)) inputModel inputRanked (SourceEqualityPCSGuard.holds formulas solver) state.native)
    (semantic : SemanticReady state.native.machine.heap)
    (symbols : request.left.entry.key.symbol = request.right.entry.key.symbol) (ready : EdgeReady state.native.machine request)
    (growth : Grows source state.native.machine.heap) (history : Extends source.nodes.issued state.native.machine.heap.nodes.issued)
    (active : ActiveAbove (view source (SourceEqualityPCSGuard.holds formulas solver)) (SourceEqualityPCSGuard.holds formulas solver)
      (requiredFuel (view source (SourceEqualityPCSGuard.holds formulas solver)) (SourceRecursiveIntersectionNative.edgeSemantic (SourceEqualityPCSGuard.holds formulas solver) request) complete + 1) state.native)
    (ranges : WordRanges (.code (requestEdge request.domain request.left request.right)) state) :
    ∃ fuel value after,
      execute (fuel + 1) (.code (requestEdge request.domain request.left request.right)) state = .done value after ∧
      SourceCurrentAllocatedNativeContextCache.EdgeLaw
        (view source (SourceEqualityPCSGuard.holds formulas solver)) inputModel inputRanked
        (SourceEqualityPCSGuard.holds formulas solver) request value ∧
      SourceCurrentAllocatedNativeContextCache.Contextual
        (view source (SourceEqualityPCSGuard.holds formulas solver)) inputModel inputRanked
        (SourceEqualityPCSGuard.holds formulas solver) after.native ∧
      Good after ∧ SemanticReady after.native.machine.heap ∧ EdgeResident after.native.machine.heap value := by
  obtain ⟨fuel, value, after, receipt⟩ := SourceCurrentAllocatedNativeContextualCompletion.edge_request_complete
    source facts formulas solver inputModel inputRanked request scope complete state valid contextual semantic
    symbols ready growth history active ranges
  exact ⟨fuel, value, after, receipt.done, receipt.law, receipt.contextual, receipt.good, receipt.semantic, receipt.result⟩

end MicroCFTA.ContextualCompletionProbe
