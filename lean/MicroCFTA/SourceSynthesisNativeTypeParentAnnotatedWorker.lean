import MicroCFTA.SourceSynthesisNativeTypeParentHeap
import MicroCFTA.SourceSynthesisNativeTypeLocalTrivialWorker
import MicroCFTA.SourceCurrentAllocatedParentWorkerActual

/-!
# Type facts through a literal annotated Parent row

Top has no own class records. Its live local branch scans no records and
requires no paths. Singleton propagation retains the original annotation.
The contradictory branch returns the one Empty child. Both branches use
the actual checked constructor and retain its complete returned state.

The caller supplies its initial context, Type facts, and successful Parent
execution. The resident law also uses the existing local range plan to
derive actual reads and the returned caller context. These laws do not
prove completion, failed-prefix safety, or all reached Type classifications.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeParentAnnotatedWorker
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedPrecheck (Receipt)
open SourceRecursiveIntersectionKernel (Extension)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Request" => SourceCurrentAllocatedPartialState.EdgeRequest
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Resident" => InternedEdgeResidency.EdgeResident
local notation "Ready" => SourceSynthesisNativeTypeSharedState.Ready
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap
local notation "initial" => SourceCurrentAllocatedSharedTargetState.initial
local notation "prefixState" => SourceCurrentAllocatedPrecheck.state
local notation "raw" => SourceEqualityConjoinAllocation.readback
variable {width : Nat}

private theorem singleton_propagate (annotation : Node) :
    EqualityLeafProjectionRuntimeEmpty.propagate [annotation] = [annotation] := by
  unfold EqualityLeafProjectionRuntimeEmpty.propagate
  split
  · rename_i erased
    have member := (EqualityLeafProjectionRuntimeEmpty.empty_test [annotation]).mp erased
    have same : annotation = .empty := (List.mem_singleton.mp member).symm
    subst annotation
    rfl
  · rfl

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

omit [DecidableEq Node] in
private theorem top_records
    {formulas solver inventory original loaded inherited before own records}
    (receipt : Receipt (width := width) formulas solver inventory original loaded inherited before own (.classes records))
    (guard : original = top) : records = [] := by
  obtain ⟨_, originals, ownRead, _, ordered, _⟩ := receipt.classes records rfl
  rw [guard] at ownRead
  have ownEmpty : SourceEqualityPhysicalPayload.own top = .ok (some ([] : List SourceEqualityClassOrder.Record)) := rfl
  have same : originals = [] := Option.some.inj (Except.ok.inj (ownRead.symm.trans ownEmpty))
  subst originals
  exact ordered

private theorem classes_nil (g s r e p h m c n budget : Nat) (values : List Node)
    (before : Checked width) (fourth : Fourth) (memo : Memo) :
    SourceCurrentAllocatedLocalWorker.classes g s r e p h m c n budget [] values before fourth memo =
      .done (EqualityLeafProjectionRuntimeEmpty.propagate values) before fourth memo := by
  have noPaths : SourceEqualitySelectedRequired.paths ([] : EqualityNormalize.Constraints) = [] := by
    simp [SourceEqualitySelectedRequired.paths, EqualityNormalize.canonicalClass]
  simp only [SourceCurrentAllocatedLocalWorker.classes, SourceCurrentAllocatedLocalWorker.scan,
    SourceCurrentAllocatedRecordScanWorker.scan, SourceCurrentAllocatedLocalWorker.Outcome.bind,
    List.map_nil, noPaths]
  simp only [SourceCurrentAllocatedLocalWorker.required, SourceEqualityRequiredExecution.requireAll_identity,
    SourceCurrentAllocatedLocalWorker.pass, SourceCurrentAllocatedClassWorker.pass_nil]
  have same : SourceCurrentConjunctionClassScan.advanceHeap before before.native.machine.heap = before := by
    cases before with
    | mk native operations => cases native <;> rfl
  rw [same]

private theorem local_top (lib : Library) (g s r e p h m c n budget : Nat)
    {formulas solver inventory original loaded inherited before own branch memo}
    (receipt : Receipt (width := width) formulas solver inventory original loaded inherited before own branch)
    (guard : original = top) (annotation : Node) (fourth : Fourth)
    (ready : Ready lib (initial before memo)) (available : Values before.native.machine.heap [annotation])
    (closed : ClosedValues [annotation]) (guards : GuardHeap (Origin lib) before.native.machine.heap) :
    ∃ child, SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget loaded inherited
        [annotation] before fourth memo = .done [child] (prefixState before loaded inherited) fourth memo ∧
      (child = annotation ∨ child = .empty) ∧ Ready lib (initial (prefixState before loaded inherited) memo) := by
  cases branch with
  | unchanged =>
      have returned := SourceSynthesisNativeTypeLocalTrivialWorker.unchanged lib g s r e p h m c n budget
        fourth receipt ready available closed guards
      exact ⟨annotation, returned.1, Or.inl rfl, returned.2.1⟩
  | emptyChildren =>
      have returned := SourceSynthesisNativeTypeLocalTrivialWorker.emptyChildren lib g s r e p h m c n budget
        (values := [annotation]) fourth receipt ready guards
      exact ⟨.empty, returned.1, Or.inr rfl, returned.2.1⟩
  | classes records =>
      have same := top_records receipt guard
      subst records
      have next := (SourceSynthesisNativeTypeLocalPrefix.precheck lib receipt ready).1
      refine ⟨annotation, ?_, Or.inl rfl, next⟩
      simp only [SourceCurrentAllocatedLocalWorker.reduce, receipt.actual]
      simpa only [SourceCurrentAllocatedPrecheck.state, singleton_propagate] using
        classes_nil g s r e p h m c n budget [annotation] (prefixState before loaded inherited) fourth memo

/-- Actual Top singleton reduction retains the original annotation or the literal Empty child. -/
theorem annotated (lib : Library)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {g s r e p h m c n budget : Nat} {source result : Edge} {inherited : EqValue}
    {before : Caller width} {after : Checked width} {savedFourth : Fourth} {saved : Memo} {memos : Memos}
    (actual : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget
      source.entry.key.symbol source.entry.key.constraint inherited source.children
      before.checked before.fourth before.merge = .done result after savedFourth saved)
    (context : Context formulas solver inventory before memos)
    (ready : Ready lib (initial before.checked before.merge))
    (guards : GuardHeap (Origin lib) before.checked.native.machine.heap)
    (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (resident : Resident before.checked.native.machine.heap source)
    {annotation : Node} (guard : source.entry.key.constraint = top) (children : source.children = [annotation])
    (typed : Annotated (Origin lib) annotation) (closed : annotation.free = []) :
    Ready lib (initial after saved) ∧ Extension before.checked.native.machine after.native.machine ∧
      Resident after.native.machine.heap result ∧ ClosedValues result.children ∧
      GuardHeap (Origin lib) after.native.machine.heap ∧ result.entry.key.symbol = source.entry.key.symbol ∧
      result.entry.key.constraint = top ∧ (result.children = [annotation] ∨ result.children = [.empty]) ∧
      ∀ child ∈ result.children, Annotated (Origin lib) child := by
  obtain ⟨cached, loaded, found⟩ := context.ready.good.fields source.entry.key source resident
  have available := context.ready.semantic.ready.semantic.1.normal.facts.cached.edges _ source resident
  have annotationAvailable := available annotation (by rw [children]; exact List.mem_cons_self)
  have singletonAvailable : Values before.checked.native.machine.heap [annotation] := by
    intro value member
    cases List.mem_singleton.mp member
    exact annotationAvailable
  have singletonClosed : ClosedValues [annotation] := by
    intro value member
    cases List.mem_singleton.mp member
    exact closed
  obtain ⟨own, branch, receipt⟩ := SourceCurrentAllocatedPrecheck.loaded_complete formulas solver inventory
    before.checked context.ready context.admitted source.entry.key.constraint cached loaded found inherited inheritedReady
  obtain ⟨child, reduced, choice, nextReady⟩ := local_top lib g s r e p h m c n budget receipt guard annotation
    before.fourth ready singletonAvailable singletonClosed guards
  have childAvailable : Values (prefixState before.checked loaded inherited).native.machine.heap [child] := by
    intro value member
    cases List.mem_singleton.mp member
    rcases choice with same | same
    · cases same; exact annotationAvailable
    · cases same; exact empty_available _
  have childClosed : ClosedValues [child] := by
    intro value member
    cases List.mem_singleton.mp member
    rcases choice with same | same
    · cases same; exact closed
    · cases same; rfl
  have childTyped : Annotated (Origin lib) child := by
    rcases choice with same | same
    · cases same; exact typed
    · cases same; exact .empty
  have field : SourceCurrentConjunctionEquality.FieldAvailable before.checked.operations source.entry.key.constraint :=
    ⟨cached, loaded, found⟩
  have nextField : SourceCurrentConjunctionEquality.FieldAvailable
      (prefixState before.checked loaded inherited).operations (raw loaded) := by
    rw [receipt.readback]
    exact field.grows receipt.grows
  obtain ⟨made, reached, construction⟩ := SourceCurrentAllocatedMkEdge.finite formulas solver inventory
    source.entry.key.symbol loaded [child] (prefixState before.checked loaded inherited) receipt.ready receipt.admitted
    (receipt.storedReady.grows receipt.grows.constraint_growth) nextField childAvailable
  have notRejected : SourceEqualityMkEdgeAllocation.contradictory source.entry.key.constraint = false := by
    rw [guard]
    rfl
  have complete : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget source.entry.key.symbol
      source.entry.key.constraint inherited source.children before.checked before.fourth before.merge =
      .done made reached before.fourth before.merge := by
    simp only [SourceCurrentAllocatedParentWorker.edge, notRejected, Bool.false_eq_true, ite_false, found, children,
      SourceCurrentAllocatedParentWorker.reduceChildren, reduced, SourceCurrentAllocatedParentWorker.Outcome.bind,
      SourceCurrentAllocatedParentWorker.build, construction.actual]
  obtain ⟨sameResult, sameState, sameFourth, sameMemo⟩ :=
    SourceCurrentAllocatedParentWorker.Outcome.done.inj (complete.symm.trans actual)
  subst result
  subst after
  subst savedFourth
  subst saved
  obtain ⟨finalReady, extension, returned, returnedClosed, finalGuards⟩ :=
    SourceSynthesisNativeTypeParentHeap.build lib construction nextReady guards childClosed
  have keep : SourceEqualityMkEdgeAllocation.accepted (raw loaded) ([child] : List Node).length = true := by
    rw [receipt.readback, guard]
    rfl
  have returnedGuard : made.entry.key.constraint = top :=
    (show made.entry.key.constraint = raw loaded from by
      simpa only [keep, ↓reduceIte] using construction.guard).trans (receipt.readback.trans guard)
  have returnedChildren : made.children = [child] := by
    simpa only [keep, ↓reduceIte] using construction.children
  refine ⟨finalReady, receipt.extension.trans extension, returned, returnedClosed, finalGuards,
    construction.symbol, returnedGuard, ?_, ?_⟩
  · rw [returnedChildren]
    rcases choice with same | same
    · exact Or.inl (congrArg (fun value : Node => [value]) same)
    · exact Or.inr (congrArg (fun value : Node => [value]) same)
  · intro value member
    rw [returnedChildren] at member
    cases List.mem_singleton.mp member
    exact childTyped

/-- The resident range plan also derives actual reads and the same returned caller context. -/
theorem resident (lib : Library)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {g s r e p h m c n budget : Nat} {request : Request}
    {before : Caller width} {after : Checked width} {result : Edge}
    {savedFourth : Fourth} {saved : Memo} {memos : Memos}
    (actual : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget request.value.entry.key.symbol
      request.value.entry.key.constraint request.inherited request.value.children before.checked before.fourth before.merge =
      .done result after savedFourth saved)
    (context : Context formulas solver inventory before memos)
    (ready : Ready lib (initial before.checked before.merge))
    (guards : GuardHeap (Origin lib) before.checked.native.machine.heap)
    (inheritedReady : EqReady before.checked.operations.constraints request.inherited)
    (included : Resident before.checked.native.machine.heap request.value)
    (ranges : SourceCurrentAllocatedParentWorkerActual.ResidentRanges budget request before)
    {annotation : Node} (guard : request.value.entry.key.constraint = top) (children : request.value.children = [annotation])
    (typed : Annotated (Origin lib) annotation) (closed : annotation.free = []) :
    ∃ next final,
      ∃ body : SourceCurrentAllocatedPartialGraph.EdgeBody budget request before result
          (SourceCurrentAllocatedPartialState.advance before after savedFourth saved),
        SourceCurrentAllocatedPartialSourceReads.EdgeBodyReads formulas solver body memos final ∧
        SourceCurrentAllocatedPartialEdgeCall.Receipt formulas solver next request before result
          (SourceCurrentAllocatedPartialState.advance before after savedFourth saved) final ∧
        Post formulas solver next before (SourceCurrentAllocatedPartialState.advance before after savedFourth saved) final ∧
        Ready lib (initial after saved) ∧ Extension before.checked.native.machine after.native.machine ∧
        Resident after.native.machine.heap result ∧ ClosedValues result.children ∧
        GuardHeap (Origin lib) after.native.machine.heap ∧ result.entry.key.symbol = request.value.entry.key.symbol ∧
        result.entry.key.constraint = top ∧ (result.children = [annotation] ∨ result.children = [.empty]) ∧
        ∀ child ∈ result.children, Annotated (Origin lib) child := by
  obtain ⟨next, final, body, reads, receipt, post⟩ := SourceCurrentAllocatedParentWorkerActual.resident_verified
    formulas solver context inheritedReady included ranges actual
  exact ⟨next, final, body, reads, receipt, post,
    annotated lib formulas solver actual context ready guards inheritedReady included guard children typed closed⟩

end MicroCFTA.SourceSynthesisNativeTypeParentAnnotatedWorker
