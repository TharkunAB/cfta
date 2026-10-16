import MicroCFTA.SourceCurrentAllocatedConjunctionCaller

namespace CurrentConjunctionCallerKernels
open MicroCFTA Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedPartialState (advance)
open SourceCurrentAllocatedPartialInvariant (Context Post)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Inventory" => SourceCurrentAllocatedNativeInventoryState.Inventory
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Call" => SourceCurrentConjunctionMemo.Call
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

theorem consecutive {inventory : Inventory} {before : Caller width} {memos : Memos}
    (firstBudget secondBudget : Nat) (firstQuery secondQuery : Value Symbol Guard)
    (initial : Context formulas solver inventory before memos)
    (firstAvailable : Available before.checked.native.machine.heap firstQuery)
    (secondAvailable : Available before.checked.native.machine.heap secondQuery) :
    ∃ answer middle saved,
      Call firstBudget before.fourth firstQuery (physical before.checked) answer middle saved ∧
      ∃ secondAnswer after secondSaved final,
        Call secondBudget saved secondQuery middle secondAnswer after secondSaved ∧
        Post formulas solver inventory before
          (advance (advance before (advancePhysical before.checked middle) saved before.merge)
            (advancePhysical (advancePhysical before.checked middle) after) secondSaved before.merge) final ∧
        SourceCurrentEmptinessMemo.AnswerSound formulas solver secondQuery secondAnswer ∧
        Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  obtain ⟨answer, middle, saved, firstFinal, first, _, post, _, _, kept, querySame⟩ :=
    SourceCurrentAllocatedConjunctionCaller.finite formulas solver firstBudget initial firstAvailable
  have nextAvailable := post.effects.keeps.available _ secondAvailable
  obtain ⟨secondAnswer, after, secondSaved, final, second, _, later, sound, _, retained, queryKept⟩ :=
    SourceCurrentAllocatedConjunctionCaller.finite formulas solver secondBudget post.context nextAvailable
  refine ⟨answer, middle, saved, first, secondAnswer, after, secondSaved, final, ?_,
    post.trans later, sound, extends_trans kept retained, queryKept.trans querySame⟩
  simpa only [SourceCurrentAllocatedPartialState.advance, SourceCurrentAllocatedQueryMemo.physical_advance] using second

theorem open_answer {inventory : Inventory} {before : Caller width} {memos : Memos}
    {budget : Nat} {query : Value Symbol Guard} {answer : Bool} {after} {saved}
    (actual : Call budget before.fourth query (physical before.checked) answer after saved)
    (initial : Context formulas solver inventory before memos)
    (available : Available before.checked.native.machine.heap query) (openInput : query.free ≠ []) : answer = false := by
  obtain ⟨_, _, _, sound, _⟩ := SourceCurrentAllocatedConjunctionCaller.actual formulas solver actual initial available
  exact sound.1 openInput

theorem true_rejects {inventory : Inventory} {before : Caller width} {memos : Memos}
    {budget : Nat} {query : Value Symbol Guard} {after} {saved}
    (actual : Call budget before.fourth query (physical before.checked) true after saved)
    (initial : Context formulas solver inventory before memos)
    (available : Available before.checked.native.machine.heap query) :
    ∀ ambient term, ¬InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient query term := by
  obtain ⟨_, _, _, sound, _⟩ := SourceCurrentAllocatedConjunctionCaller.actual formulas solver actual initial available
  exact sound.2 rfl

#print axioms consecutive
#print axioms open_answer
#print axioms true_rejects
end CurrentConjunctionCallerKernels
