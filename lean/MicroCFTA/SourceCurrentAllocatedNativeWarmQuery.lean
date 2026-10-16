import MicroCFTA.SourceCurrentAllocatedNativeColdClosedExact

/-!
# Exact closed queries in one fixed original input model

Each query uses the same source heap and finite input interpretation.
Actual earlier results can therefore supply both returned cache invariants.
The request induction derives completion, meaning, and syntactic scope.
The initial physical state and reached machine ranges remain explicit.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeWarmQuery
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView IntersectSchedule SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedNativeRequestBounds (WordRanges)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}

/-- One actual return retains the fixed model, closedness, and original operand language. -/
structure Receipt [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inputs : FiniteInput (view source (SourceEqualityPCSGuard.holds formulas solver)))
    (fuel : Nat) (left right : Value Symbol Guard) (before : Checked width)
    (value : Value Symbol Guard) (after : Checked width) : Prop
    extends toContextualReceipt : SourceCurrentAllocatedNativeContextualCompletion.Receipt
      (semanticView := view source (SourceEqualityPCSGuard.holds formulas solver))
      (model := finiteInputMeaning (view source (SourceEqualityPCSGuard.holds formulas solver)) inputs)
      (ranked := finiteRankedInput (view source (SourceEqualityPCSGuard.holds formulas solver)) inputs)
      (semanticHolds := SourceEqualityPCSGuard.holds formulas solver)
      fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before value after
      (fun final result => Available final.heap result)
      (fun _ result => SourceCurrentAllocatedNativeContextCache.NodeLaw
        (view source (SourceEqualityPCSGuard.holds formulas solver))
        (finiteInputMeaning (view source (SourceEqualityPCSGuard.holds formulas solver)) inputs)
        (finiteRankedInput (view source (SourceEqualityPCSGuard.holds formulas solver)) inputs)
        (SourceEqualityPCSGuard.holds formulas solver) ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ result) where
  scopedCache : SourceCurrentAllocatedNativeScopeCache.Scoped after.native
  idle : SourceRecursiveIntersectionNative.Idle after.native
  closed : value.free = []
  meaning : ∀ output term,
    InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output value term ↔
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output left term ∧
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output right term

/-- The receipt completes the literal checked query with the same full state. -/
theorem Receipt.done [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {source : InternedConstructorTemplates.State Symbol Guard}
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inputs : FiniteInput (view source (SourceEqualityPCSGuard.holds formulas solver))}
    {fuel : Nat} {left right value : Value Symbol Guard} {before after : Checked width}
    (receipt : Receipt source formulas solver inputs fuel left right before value after) :
    execute (fuel + 1) (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before = .done value after :=
  receipt.toContextualReceipt.done

/-- An original resident operand has exact physical meaning in the fixed finite input model. -/
theorem input_meaning (source : InternedConstructorTemplates.State Symbol Guard) (facts : InternedNestedFacts.Facts source)
    (holds : Guard → Term Symbol → Bool) (inputs : FiniteInput (view source holds))
    (value : Value Symbol Guard) (original : Original value) (available : Available source value)
    (closed : value.free = []) (valid : inputs.valid (inputOf value))
    (output : InternedGuardedLanguage.Env Symbol) (term : Term Symbol) :
    InternedGuardedLanguage.meaning holds output value term ↔
      inputLanguage (finiteInputMeaning (view source holds) inputs).languages (inputOf value) term := by
  rw [SourceRecursiveIntersectionGuardedInput.input_exact source facts holds value original available closed output]
  exact (finiteLanguages_exact (view source holds) inputs (inputOf value) valid term).symm

/-- Fixed-model cache invariants admit the next original query and derive its exact closed return. -/
theorem query_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : InternedNestedFacts.Facts source)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inputs : FiniteInput (view source (SourceEqualityPCSGuard.holds formulas solver)))
    (state : Checked width) (valid : Good state)
    (contextual : SourceCurrentAllocatedNativeContextCache.Contextual
      (view source (SourceEqualityPCSGuard.holds formulas solver))
      (finiteInputMeaning (view source (SourceEqualityPCSGuard.holds formulas solver)) inputs)
      (finiteRankedInput (view source (SourceEqualityPCSGuard.holds formulas solver)) inputs)
      (SourceEqualityPCSGuard.holds formulas solver) state.native)
    (scopedCache : SourceCurrentAllocatedNativeScopeCache.Scoped state.native)
    (semantic : SemanticReady state.native.machine.heap) (idle : SourceRecursiveIntersectionNative.Idle state.native)
    (growth : Grows source state.native.machine.heap)
    (history : Extends source.nodes.issued state.native.machine.heap.nodes.issued)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available source left) (rightAvailable : Available source right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (leftValid : inputs.valid (inputOf left)) (rightValid : inputs.valid (inputOf right))
    (ranges : WordRanges (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) state) :
    ∃ fuel value after, Receipt source formulas solver inputs fuel left right state value after := by
  let holds := SourceEqualityPCSGuard.holds formulas solver
  let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
  let model := finiteInputMeaning (view source holds) inputs
  let ranked := finiteRankedInput (view source holds) inputs
  have complete : Completes (view source holds) (SourceRecursiveIntersectionNative.nodeSemantic request) :=
    SourceRecursiveIntersectionRequestProgress.initial_complete source facts holds left right leftOriginal rightOriginal
      leftAvailable rightAvailable leftClosed rightClosed
  have scope : NodeScope source request := initial_scope source left right leftOriginal rightOriginal leftAvailable rightAvailable
  have ready : NodeReady state.native.machine request :=
    ⟨empty_domain _, leftAvailable.grows source _ growth history, rightAvailable.grows source _ growth history⟩
  have active := idle.active (view source holds) holds
    (requiredFuel (view source holds) (SourceRecursiveIntersectionNative.nodeSemantic request) complete + 1) state.native
  obtain ⟨fuel, value, after, receipt⟩ := SourceCurrentAllocatedNativeContextualCompletion.request_complete
    source facts formulas solver model ranked request scope complete state valid contextual semantic ready growth history active ranges
  obtain ⟨scopeFuel, scopedValue, scopedAfter, scopeReceipt⟩ := SourceCurrentAllocatedNativeScopeCompletion.request_complete
    source facts holds request scope complete state valid scopedCache semantic ready growth history active ranges
  have same := SourceCurrentAllocatedNativeColdClosedExact.completed_unique (fuel + 1) (scopeFuel + 1) _ _
    after scopedAfter value scopedValue receipt.done scopeReceipt.done
  rcases same with ⟨rfl, rfl⟩
  have afterIdle := SourceCurrentAllocatedNativeRunning.done_idle (fuel + 1) _ state after value
    (by intro value; trivial) valid.native.shape idle receipt.done
  have closed : value.free = [] := by
    have resultScope : SourceRecursiveIntersectionResultScope.Scope [] value := scopeReceipt.law
    exact SourceRecursiveIntersectionResultScope.empty_scope value resultScope
  have nodeInputs : SourceCurrentAllocatedNativeContextCache.NodeInputs (view source holds) model request :=
    ⟨leftOriginal, rightOriginal, leftValid, rightValid⟩
  refine ⟨fuel, value, after, receipt, scopeReceipt.scopedCache, afterIdle, closed, ?_⟩
  intro output term
  rw [SourceCurrentAllocatedNativeClosedReceipts.node_closed_exact (view source holds) model ranked holds
    (fun _ _ => Iff.rfl) request value nodeInputs receipt.law rfl output term]
  rw [input_meaning source facts holds inputs left leftOriginal leftAvailable leftClosed leftValid output term,
    input_meaning source facts holds inputs right rightOriginal rightAvailable rightClosed rightValid output term]

end MicroCFTA.SourceCurrentAllocatedNativeWarmQuery
