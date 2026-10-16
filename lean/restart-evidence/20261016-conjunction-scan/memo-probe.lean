import MicroCFTA.SourceCurrentAllocatedConjunctionMemo

#print axioms MicroCFTA.SourceCurrentAllocatedConjunctionMemo.ready
#print axioms MicroCFTA.SourceCurrentAllocatedConjunctionMemo.advance_good
#print axioms MicroCFTA.SourceCurrentAllocatedConjunctionMemo.advance_contextual
#print axioms MicroCFTA.SourceCurrentAllocatedConjunctionMemo.advance_scoped
#print axioms MicroCFTA.SourceCurrentAllocatedConjunctionMemo.advance_idle
#print axioms MicroCFTA.SourceCurrentAllocatedConjunctionMemo.advance_self
#print axioms MicroCFTA.SourceCurrentAllocatedConjunctionMemo.Receipt
#print axioms MicroCFTA.SourceCurrentAllocatedConjunctionMemo.lift_effects
#print axioms MicroCFTA.SourceCurrentAllocatedConjunctionMemo.call_effects
#print axioms MicroCFTA.SourceCurrentAllocatedConjunctionMemo.finite
#check @MicroCFTA.SourceCurrentAllocatedConjunctionMemo.ready
#check @MicroCFTA.SourceCurrentAllocatedConjunctionMemo.advance_good
#check @MicroCFTA.SourceCurrentAllocatedConjunctionMemo.advance_contextual
#check @MicroCFTA.SourceCurrentAllocatedConjunctionMemo.advance_scoped
#check @MicroCFTA.SourceCurrentAllocatedConjunctionMemo.advance_idle
#check @MicroCFTA.SourceCurrentAllocatedConjunctionMemo.advance_self
#check @MicroCFTA.SourceCurrentAllocatedConjunctionMemo.Receipt
#check @MicroCFTA.SourceCurrentAllocatedConjunctionMemo.lift_effects
#check @MicroCFTA.SourceCurrentAllocatedConjunctionMemo.call_effects
#check @MicroCFTA.SourceCurrentAllocatedConjunctionMemo.finite

namespace MicroCFTA.AllocatedConjunctionMemoProbe
open Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedConjunctionMemo
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {width : Nat}

-- The current actual call retains both cache laws in their fixed interpretation.
example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid) (holds : Guard → Term Symbol → Bool)
    (budget : Nat) (memo saved : SourceCurrentEmptinessMemo.Memo) (query : Value Symbol Guard)
    (before : Checked width) (answer : Bool) (after : Physical)
    (actual : SourceCurrentConjunctionMemo.Call budget memo query (physical before) answer after saved)
    (good : Good before) (semantic : SemanticReady before.native.machine.heap)
    (costs : CostHeap before.native.machine.heap) (idle : SourceRecursiveIntersectionNative.Idle before.native)
    (available : Available before.native.machine.heap query)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo)
    (contextual : SourceCurrentAllocatedNativeContextCache.Contextual view model ranked holds before.native)
    (scopes : SourceCurrentAllocatedNativeScopeCache.Scoped before.native) :
    Receipt before after ∧
      SourceCurrentAllocatedNativeContextCache.Contextual view model ranked holds (advancePhysical before after).native ∧
      SourceCurrentAllocatedNativeScopeCache.Scoped (advancePhysical before after).native ∧
      Available (advancePhysical before after).native.machine.heap query ∧
      physical (advancePhysical before after) = after ∧
      SourceCurrentEmptinessMemo.Correct formulas solver after.heap saved ∧
      SourceCurrentEmptinessMemo.Extends memo saved := by
  obtain ⟨receipt, finalCorrect, _, retained⟩ := call_effects formulas solver actual good semantic costs idle available correct
  exact ⟨receipt, advance_contextual view model ranked holds before after contextual, advance_scoped before after scopes,
    receipt.effects.keeps.available query available, SourceCurrentAllocatedQueryMemo.physical_advance before after,
    finalCorrect, retained⟩

-- Cold fourth-memo completion needs no earlier query, result law, or body trace.
example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (budget : Nat) (query : Value Symbol Guard) (before : Checked width) (good : Good before)
    (semantic : SemanticReady before.native.machine.heap) (costs : CostHeap before.native.machine.heap)
    (idle : SourceRecursiveIntersectionNative.Idle before.native) (available : Available before.native.machine.heap query) :
    ∃ answer after saved,
      SourceCurrentConjunctionMemo.Call budget SourceCurrentEmptinessMemo.empty query (physical before) answer after saved ∧
      Receipt before after ∧ Good (advancePhysical before after) ∧
      CostHeap (advancePhysical before after).native.machine.heap ∧
      (advancePhysical before after).native.machine.domains = before.native.machine.domains ∧
      SourceCurrentEmptinessMemo.Correct formulas solver after.heap saved ∧
      (answer = true → ∀ ambient term, ¬InternedGuardedLanguage.meaning
        (SourceEqualityPCSGuard.holds formulas solver) ambient query term) := by
  obtain ⟨answer, after, saved, actual, receipt, correct, sound, _⟩ := finite formulas solver budget
    SourceCurrentEmptinessMemo.empty query before good semantic costs idle available
    (SourceCurrentEmptinessMemo.empty_correct formulas solver before.native.machine.heap)
  exact ⟨answer, after, saved, actual, receipt, receipt.good, receipt.effects.ready.costs,
    receipt.tables.2.2, correct, sound.2⟩

-- A completed hit bypasses the body and preserves the entire checked state.
example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (budget : Nat) (memo : SourceCurrentEmptinessMemo.Memo) (query original : Value Symbol Guard)
    (answer : Bool) (before : Checked width) (found : memo query.referenceOf = some (original, answer))
    (good : Good before) (semantic : SemanticReady before.native.machine.heap)
    (costs : CostHeap before.native.machine.heap) (idle : SourceRecursiveIntersectionNative.Idle before.native)
    (available : Available before.native.machine.heap query)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo) :
    SourceCurrentConjunctionMemo.Call budget memo query (physical before) answer (physical before) memo ∧
      Receipt before (physical before) ∧ advancePhysical before (physical before) = before ∧
      SourceCurrentEmptinessMemo.AnswerSound formulas solver query answer := by
  have actual : SourceCurrentConjunctionMemo.Call budget memo query (physical before) answer (physical before) memo := .hit found
  obtain ⟨receipt, _, sound, _⟩ := call_effects formulas solver actual good semantic costs idle available correct
  exact ⟨actual, receipt, advance_self before, sound⟩

-- Every constructor-only effect retains existing returned-cell laws, even without a memo call.
example (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid) (holds : Guard → Term Symbol → Bool)
    (before : Checked width) (after : Physical) (good : Good before)
    (idle : SourceRecursiveIntersectionNative.Idle before.native)
    (effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before) after)
    (contextual : SourceCurrentAllocatedNativeContextCache.Contextual view model ranked holds before.native)
    (scopes : SourceCurrentAllocatedNativeScopeCache.Scoped before.native) :
    Receipt before after ∧
      SourceCurrentAllocatedNativeContextCache.Contextual view model ranked holds (advancePhysical before after).native ∧
      SourceCurrentAllocatedNativeScopeCache.Scoped (advancePhysical before after).native :=
  ⟨lift_effects before after good idle effects, advance_contextual view model ranked holds before after contextual,
    advance_scoped before after scopes⟩

end MicroCFTA.AllocatedConjunctionMemoProbe
