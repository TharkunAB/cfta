import MicroCFTA.SourceFreshOrdinaryNativeEntryCorrect

/-!
# Unique public reference results and exact physical-root readback

Actual cold traces determine one finite table and final cache. Reference
compilation therefore determines one complete query result. Successful
results have the independent guarded language of the original physical root.
-/
namespace MicroCFTA.SourceFreshOrdinaryNativeEntry
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open SourceGuards SourceObservations SourceSymbolicIndex
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceColdSharedRows (Rows Supported)
open SourceFreshOrdinaryColdSharedRows (Trace keys)
open SourceFreshOrdinaryNativeEntryPrecheck (check)

variable {bits : Nat} {Formula Key : Type} [DecidableEq Formula] [DecidableEq Key] [Ord Key]
    [DecidableEq (EdgeKey (Label Formula) (Constraint Formula))]
    (formulas : Formulas Formula) (solver : Entailment Formula) (order : Label Formula → Key)
    (value : Value (Label Formula) (Constraint Formula))

local notation "N" => SourceRecursiveIntersectionThunks.State (bits + 2) (Label Formula) (Constraint Formula)
local notation "Api" => SourceSizedDispatcher.Api (Label Formula)

/-- Actual prechecks, cold trace uniqueness, and pure compilation determine one complete public reference result. -/
theorem Reference.unique (state : N) (first second : Except SourceCyclicAutomaton.Error Api)
    (left : Reference formulas solver order value state first) (right : Reference formulas solver order value state second) : first = second := by
  cases left with
  | empty selected => cases right <;> simp_all
  | openRoot selected => cases right <;> simp_all
  | rows firstRows firstFinal firstDomain firstSupported firstClosed firstActive selected firstTrace firstResult firstCompiled =>
      cases right with
      | empty other | openRoot other => simp_all
      | rows secondRows secondFinal secondDomain secondSupported secondClosed secondActive other secondTrace secondResult secondCompiled =>
          obtain ⟨rfl, rfl⟩ := firstTrace.unique secondTrace
          have same := Option.some.inj (firstCompiled.symm.trans secondCompiled)
          cases same
          rfl

/-- Every successful public reference result reads one exact independent physical-root language. -/
theorem Reference.success_readback (emptyGuard : Constraint Formula)
    (conjoin : Constraint Formula → Constraint Formula → Constraint Formula)
    (state : N) (ready : SourceFreshOrdinaryNativeCallback.Ready emptyGuard conjoin state)
    (available : Available state.machine.heap value) (result : Except SourceCyclicAutomaton.Error Api) (api : Api)
    (actual : Reference formulas solver order value state result) (success : result = .ok api)
    (ambient : InternedGuardedLanguage.Env (Label Formula)) :
    ∃ (State : Type) (A : Automaton State (Label Formula)) (root : State),
      api = SourceSizedDispatcher.referenceApi A root ∧
      ∀ term, Accepts A root term ↔ InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient value term := by
  cases actual with
  | empty selected =>
      have same := Except.ok.inj success
      subst api
      have empty := (SourceFreshOrdinaryNativeEntryPrecheck.check_empty_iff value).mp selected
      subst value
      refine ⟨Unit, (fun _ => []), (), (SourceFreshOrdinaryNativeEmptyApi.reference ()).symm, ?_⟩
      intro term
      constructor
      · intro accepted
        cases accepted with
        | node edge children member runs guard => cases member
      · intro impossible
        simp only [InternedGuardedLanguage.meaning] at impossible
  | openRoot selected => cases success
  | rows rows final domain supported closed active selected trace result compiled =>
      cases result with
      | error error => cases success
      | ok output =>
          have same := Except.ok.inj success
          subst api
          have valueClosed := ((SourceFreshOrdinaryNativeEntryPrecheck.check_rows_iff value).mp selected).2
          obtain ⟨finalReady, _, _, _, finalAvailable, _, resident, replayed, children, _, _, _, _⟩ :=
            SourceFreshOrdinaryColdNativeTable.for_trace emptyGuard conjoin state ready value available valueClosed rows final trace
          obtain ⟨_, _, language⟩ := SourceCyclicRows.compile_exact formulas solver
            (SourceFreshOrdinaryColdCyclic.input rows (keys final rows) value domain supported closed [] active) order output compiled
          refine ⟨_, output, _, rfl, ?_⟩
          intro term
          exact (language term).trans (SourceFreshOrdinaryColdCyclic.root_language rows (keys final rows) value domain supported closed [] active
            final finalReady.semantic finalReady.covered finalReady.guarded finalReady.budget replayed resident children
            finalAvailable valueClosed formulas solver ambient term)

end MicroCFTA.SourceFreshOrdinaryNativeEntry
