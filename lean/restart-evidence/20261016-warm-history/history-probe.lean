import MicroCFTA.SourceCurrentAllocatedNativeWarmHistory
namespace MicroCFTA.WarmHistoryProbe
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView IntersectSchedule SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedNativeRequestBounds (WordRanges)
open SourceCurrentAllocatedNativeWarmHistory
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Query" => Value Symbol Guard × Value Symbol Guard
variable {width : Nat}
#print axioms MicroCFTA.SourceCurrentAllocatedNativeWarmHistory.Receipt.done
#print axioms MicroCFTA.SourceCurrentAllocatedNativeWarmHistory.Receipt.warm
#print axioms MicroCFTA.SourceCurrentAllocatedNativeWarmHistory.walk_complete
#check @MicroCFTA.SourceCurrentAllocatedNativeWarmHistory.Receipt.done
#check @MicroCFTA.SourceCurrentAllocatedNativeWarmHistory.Receipt.warm
#check @MicroCFTA.SourceCurrentAllocatedNativeWarmHistory.walk_complete

example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {source : InternedConstructorTemplates.State Symbol Guard}
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inputs : FiniteInput (view source (SourceEqualityPCSGuard.holds formulas solver))}
    {fuel : Nat} {pairs : List Query} {before after : Checked width} {values : List (Value Symbol Guard)}
    (receipt : Receipt source formulas solver inputs fuel pairs before values after) :
    pairs.length = values.length ∧ execute (fuel + 1) (.code (program pairs)) before = .done values after ∧
    SourceCurrentAllocatedNativePhysicalExecution.InputsThrough (fuel + 1) (.code (program pairs)) before ∧
    All₂ (fun pair value => ∀ key,
      SourceRecursiveIntersectionMemo.requestKey width IntersectionEmptyDomain.emptyDomain pair.1 pair.2 = some key →
      execute 2 (.code (requestNode IntersectionEmptyDomain.emptyDomain pair.1 pair.2)) after = .done value after) pairs values :=
  ⟨receipt.meaning.length_eq, receipt.done, receipt.trace.plan, receipt.warm⟩

example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
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
    ∃ fuel values after,
      (∀ extra, execute (fuel + 1 + extra) (.code (program pairs)) state = .done values after) ∧
      Good after ∧ SourceCurrentAllocatedNativeScopeCache.Scoped after.native ∧
      SemanticReady after.native.machine.heap ∧ SourceRecursiveIntersectionNative.Idle after.native ∧
      (∀ value ∈ values, Available after.native.machine.heap value ∧ value.free = []) ∧
      All₂ (fun pair value => ∀ output term,
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output value term ↔
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output pair.1 term ∧
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output pair.2 term) pairs values := by
  obtain ⟨fuel, values, after, receipt⟩ := walk_complete source facts formulas solver inputs pairs state valid contextual
    scopedCache semantic idle growth history admissible ranges
  exact ⟨fuel, values, after, (fun extra => done_stable (fuel + 1) extra _ _ _ _ receipt.done), receipt.good,
    receipt.scopedCache, receipt.semantic, receipt.idle, (fun value member => ⟨receipt.result value member, receipt.closed value member⟩),
    receipt.meaning⟩

example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : InternedNestedFacts.Facts source)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inputs : FiniteInput (view source (SourceEqualityPCSGuard.holds formulas solver))) (pair : Query)
    (state : Checked width) (valid : Good state)
    (contextual : SourceCurrentAllocatedNativeContextCache.Contextual
      (view source (SourceEqualityPCSGuard.holds formulas solver))
      (finiteInputMeaning (view source (SourceEqualityPCSGuard.holds formulas solver)) inputs)
      (finiteRankedInput (view source (SourceEqualityPCSGuard.holds formulas solver)) inputs)
      (SourceEqualityPCSGuard.holds formulas solver) state.native)
    (scopedCache : SourceCurrentAllocatedNativeScopeCache.Scoped state.native)
    (semantic : SemanticReady state.native.machine.heap) (idle : SourceRecursiveIntersectionNative.Idle state.native)
    (growth : Grows source state.native.machine.heap) (history : Extends source.nodes.issued state.native.machine.heap.nodes.issued)
    (admissible : Admissible source formulas solver inputs pair)
    (key : IntersectionFlatMemoKeyDomain.Triple width)
    (requested : SourceRecursiveIntersectionMemo.requestKey width IntersectionEmptyDomain.emptyDomain pair.1 pair.2 = some key)
    (ranges : WordRanges (.code (program [pair, pair])) state) :
    ∃ fuel value after, execute (fuel + 1) (.code (program [pair, pair])) state = .done [value, value] after ∧
      execute 2 (.code (requestNode IntersectionEmptyDomain.emptyDomain pair.1 pair.2)) after = .done value after := by
  have domains : ∀ candidate ∈ [pair, pair], Admissible source formulas solver inputs candidate := by
    intro candidate member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact admissible
  obtain ⟨fuel, values, after, receipt⟩ := walk_complete source facts formulas solver inputs [pair, pair] state valid contextual
    scopedCache semantic idle growth history domains ranges
  have done := receipt.done
  have warm := receipt.warm
  cases warm with
  | cons first tail =>
      cases tail with
      | cons second last =>
          cases last
          have same := Outcome.done.inj ((first key requested).symm.trans (second key requested))
          rcases same.1 with rfl
          exact ⟨fuel, _, after, done, first key requested⟩

end MicroCFTA.WarmHistoryProbe
