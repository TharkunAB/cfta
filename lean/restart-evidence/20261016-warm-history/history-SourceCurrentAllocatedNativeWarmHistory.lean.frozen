import MicroCFTA.SourceCurrentAllocatedNativeWarmQuery
import MicroCFTA.SourceCurrentAllocatedNativeCompletedMemo

/-!
# Serial checked queries in one fixed input model

The literal source walk runs each query before its remaining tail.
Each completed prefix derives the next physical and cache invariants.
One original input model applies to every returned memo cell.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeWarmHistory
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView IntersectSchedule SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedNativeRequestBounds (WordRanges)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Query" => Value Symbol Guard × Value Symbol Guard
variable {width : Nat}

/-- The ordered code requests the original pairs at the empty domain. -/
def program (pairs : List Query) : Code Symbol Guard (List (Value Symbol Guard)) :=
  walk (fun pair => requestNode IntersectionEmptyDomain.emptyDomain pair.1 pair.2) pairs

/-- Each original query belongs to the same immutable source input model. -/
def Admissible (source : InternedConstructorTemplates.State Symbol Guard)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inputs : FiniteInput (view source (SourceEqualityPCSGuard.holds formulas solver))) (pair : Query) : Prop :=
  Original pair.1 ∧ Original pair.2 ∧ Available source pair.1 ∧ Available source pair.2 ∧
    pair.1.free = [] ∧ pair.2.free = [] ∧ inputs.valid (inputOf pair.1) ∧ inputs.valid (inputOf pair.2)

/-- A cacheable original query retains its literal final returned cell. -/
def Memoized (state : Checked width) (pair : Query) (value : Value Symbol Guard) : Prop :=
  ∀ key, SourceRecursiveIntersectionMemo.requestKey width IntersectionEmptyDomain.emptyDomain pair.1 pair.2 = some key →
    ∃ handle, state.native.nodes.table key = some handle ∧ state.native.nodes.cells handle =
      some ⟨⟨IntersectionEmptyDomain.emptyDomain, pair.1, pair.2⟩, .returned value⟩

/-- The exact walk retains all results and the fixed contextual and scope caches. -/
structure Receipt [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inputs : FiniteInput (view source (SourceEqualityPCSGuard.holds formulas solver)))
    (fuel : Nat) (pairs : List Query) (before : Checked width) (values : List (Value Symbol Guard)) (after : Checked width) : Prop
    extends SourceCurrentAllocatedNativePhysicalTraceCompletion.Receipt fuel (.code (program pairs)) before values after
      (fun final results => ∀ value ∈ results, Available final.heap value) where
  contextual : SourceCurrentAllocatedNativeContextCache.Contextual
    (view source (SourceEqualityPCSGuard.holds formulas solver))
    (finiteInputMeaning (view source (SourceEqualityPCSGuard.holds formulas solver)) inputs)
    (finiteRankedInput (view source (SourceEqualityPCSGuard.holds formulas solver)) inputs)
    (SourceEqualityPCSGuard.holds formulas solver) after.native
  scopedCache : SourceCurrentAllocatedNativeScopeCache.Scoped after.native
  semantic : SemanticReady after.native.machine.heap
  idle : SourceRecursiveIntersectionNative.Idle after.native
  closed : ∀ value ∈ values, value.free = []
  laws : All₂ (fun pair value => SourceCurrentAllocatedNativeContextCache.NodeLaw
    (view source (SourceEqualityPCSGuard.holds formulas solver))
    (finiteInputMeaning (view source (SourceEqualityPCSGuard.holds formulas solver)) inputs)
    (finiteRankedInput (view source (SourceEqualityPCSGuard.holds formulas solver)) inputs)
    (SourceEqualityPCSGuard.holds formulas solver) ⟨IntersectionEmptyDomain.emptyDomain, pair.1, pair.2⟩ value) pairs values
  meaning : All₂ (fun pair value => ∀ output term,
    InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output value term ↔
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output pair.1 term ∧
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output pair.2 term) pairs values
  memoized : All₂ (Memoized after) pairs values

/-- The history receipt completes the same literal walk and full checked state. -/
theorem Receipt.done [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {source : InternedConstructorTemplates.State Symbol Guard}
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inputs : FiniteInput (view source (SourceEqualityPCSGuard.holds formulas solver))}
    {fuel : Nat} {pairs : List Query} {before after : Checked width} {values : List (Value Symbol Guard)}
    (receipt : Receipt source formulas solver inputs fuel pairs before values after) :
    execute (fuel + 1) (.code (program pairs)) before = .done values after := receipt.toReceipt.done

/-- Each cacheable historical query repeats at the final state without effects. -/
theorem Receipt.warm [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {source : InternedConstructorTemplates.State Symbol Guard}
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inputs : FiniteInput (view source (SourceEqualityPCSGuard.holds formulas solver))}
    {fuel : Nat} {pairs : List Query} {before after : Checked width} {values : List (Value Symbol Guard)}
    (receipt : Receipt source formulas solver inputs fuel pairs before values after) :
    All₂ (fun pair value => ∀ key,
      SourceRecursiveIntersectionMemo.requestKey width IntersectionEmptyDomain.emptyDomain pair.1 pair.2 = some key →
      execute 2 (.code (requestNode IntersectionEmptyDomain.emptyDomain pair.1 pair.2)) after = .done value after) pairs values := by
  apply All₂.imp _ receipt.memoized
  intro pair value memoized key requested
  obtain ⟨handle, published, returned⟩ := memoized key requested
  exact SourceCurrentAllocatedNativeCompletedMemo.warm_node
    ⟨IntersectionEmptyDomain.emptyDomain, pair.1, pair.2⟩ after value key handle requested published returned

private theorem operations_trans {before middle after : SourceEqualityConstraintMemoAllocation.State}
    (first : SourceEqualityConstraintMemoAllocation.Grows before middle)
    (second : SourceEqualityConstraintMemoAllocation.Grows middle after) : SourceEqualityConstraintMemoAllocation.Grows before after :=
  ⟨SourceEqualityConstraintAllocation.steps_trans first.constraints second.constraints,
    extends_trans first.combinations second.combinations, extends_trans first.descents second.descents⟩

/-- Every reached request and tail derives its own ranges from the actual whole walk. -/
theorem walk_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : InternedNestedFacts.Facts source)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inputs : FiniteInput (view source (SourceEqualityPCSGuard.holds formulas solver))) (pairs : List Query)
    (state : Checked width) (valid : Good state)
    (contextual : SourceCurrentAllocatedNativeContextCache.Contextual
      (view source (SourceEqualityPCSGuard.holds formulas solver))
      (finiteInputMeaning (view source (SourceEqualityPCSGuard.holds formulas solver)) inputs)
      (finiteRankedInput (view source (SourceEqualityPCSGuard.holds formulas solver)) inputs)
      (SourceEqualityPCSGuard.holds formulas solver) state.native)
    (scopedCache : SourceCurrentAllocatedNativeScopeCache.Scoped state.native)
    (semantic : SemanticReady state.native.machine.heap) (idle : SourceRecursiveIntersectionNative.Idle state.native)
    (growth : Grows source state.native.machine.heap) (history : Extends source.nodes.issued state.native.machine.heap.nodes.issued)
    (admissible : ∀ pair ∈ pairs, Admissible source formulas solver inputs pair)
    (ranges : WordRanges (.code (program pairs)) state) :
    ∃ fuel values after, Receipt source formulas solver inputs fuel pairs state values after := by
  induction pairs generalizing state with
  | nil =>
      exact ⟨0, [], state, ⟨⟨.refl _ _, valid, .refl _, SourceEqualityRequiredCache.pure_keeps _ valid.heap,
        SourceEqualityConstraintMemoAllocation.grows_refl _, (by intro value member; cases member)⟩,
        contextual, scopedCache, semantic, idle, (by intro value member; cases member), .nil, .nil, .nil⟩⟩
  | cons first rest ih =>
      let next := fun value => (program rest).bind fun values => .pure (value :: values)
      obtain ⟨leftOriginal, rightOriginal, leftAvailable, rightAvailable, leftClosed, rightClosed, leftValid, rightValid⟩ :=
        admissible first List.mem_cons_self
      have headRanges := ranges.before_bind (.code (requestNode IntersectionEmptyDomain.emptyDomain first.1 first.2)) next state
      obtain ⟨headFuel, value, middle, head⟩ := SourceCurrentAllocatedNativeWarmQuery.query_complete
        source facts formulas solver inputs state valid contextual scopedCache semantic idle growth history
        first.1 first.2 leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed leftValid rightValid headRanges
      have reachedRanges := ranges.after_body (.code (requestNode IntersectionEmptyDomain.emptyDomain first.1 first.2))
        next state middle headFuel value head.trace.steps
      have tailRanges := reachedRanges.before_bind (.code (program rest)) (fun values => .pure (value :: values)) middle
      obtain ⟨tailFuel, values, after, tail⟩ := ih middle head.good head.contextual head.scopedCache head.semantic head.idle
        (grows_trans growth head.extension.heap) (extends_trans history head.extension.history)
        (fun pair member => admissible pair (List.mem_cons_of_mem first member)) tailRanges
      have retained := SourceCurrentAllocatedNativeCompletedMemo.done_retained (tailFuel + 1) (.code (program rest))
        middle after values head.good.native.shape tail.done
      have ready : NodeReady state.native.machine ⟨IntersectionEmptyDomain.emptyDomain, first.1, first.2⟩ :=
        ⟨empty_domain _, leftAvailable.grows source _ growth history, rightAvailable.grows source _ growth history⟩
      have headMemoized : Memoized after first value := by
        intro key requested
        obtain ⟨handle, published, returned⟩ := SourceCurrentAllocatedNativeCompletedMemo.completed_node (headFuel + 1)
          ⟨IntersectionEmptyDomain.emptyDomain, first.1, first.2⟩ state middle value valid.native ready
          ((headRanges.current _ _) key requested) key requested head.done
        exact ⟨handle, retained.nodeKeys key handle published,
          retained.nodes handle ⟨IntersectionEmptyDomain.emptyDomain, first.1, first.2⟩ value returned⟩
      have trace := (head.trace.bind next).trans (tail.trace.bind (fun values => .pure (value :: values)))
      refine ⟨headFuel + tailFuel, value :: values, after,
        ⟨⟨trace, tail.good, head.extension.trans tail.extension, head.keeps.trans tail.keeps,
          operations_trans head.operations tail.operations, ?_⟩,
          tail.contextual, tail.scopedCache, tail.semantic, tail.idle, ?_, .cons head.law tail.laws, .cons head.meaning tail.meaning,
          .cons headMemoized tail.memoized⟩⟩
      · intro result member
        cases member with
        | head => exact tail.extension.available value head.result
        | tail _ member => exact tail.result result member
      · intro result member
        cases member with
        | head => exact head.closed
        | tail _ member => exact tail.closed result member

end MicroCFTA.SourceCurrentAllocatedNativeWarmHistory
