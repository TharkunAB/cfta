import MicroCFTA.SourceCurrentSubstitutionRowExecution
import MicroCFTA.SourceCurrentStoredPlanEquivalence

/-!
# Ordered calls of actual stored substitution

Each child uses its own captured leaves and the original replacement map.
Recapturing the shared lexical plan preserves every intermediate heap.
The result permits nested binders and repeated or reordered capture slots.
-/
namespace MicroCFTA.SourceCurrentStoredSubstitutionCalls
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedNestedProvenance (Values)
open InternedStoredSubstitution (Environment leaves manyLeaves input)
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceCurrentSubstitutionRowExecution (ChildTrace)

/-- Each ordered child performs its actual stored substitution before the next child starts. -/
inductive Calls [DecidableEq (EdgeKey Symbol Guard)] (environment : Environment Symbol Guard) :
    List (Value Symbol Guard) → State Symbol Guard → List (Value Symbol Guard) → State Symbol Guard → Prop where
  /-- Empty child lists leave the current heap unchanged. -/
  | nil (state) : Calls environment [] state [] state
  /-- A completed child call retains both its actual heaps and the remaining calls. -/
  | cons (original originals before middle after output outputs)
      (called : execute original environment before = .done output middle)
      (rest : Calls environment originals middle outputs after) :
      Calls environment (original :: originals) before (output :: outputs) after

variable {environment : Environment Symbol Guard} {originals outputs : List (Value Symbol Guard)}
  {before after : State Symbol Guard}

/-- The actual child sequence has one result for each original occurrence. -/
theorem Calls.length [DecidableEq (EdgeKey Symbol Guard)]
    (calls : Calls environment originals before outputs after) : outputs.length = originals.length := by
  induction calls with
  | nil => rfl
  | cons _ _ _ _ _ _ _ _ _ ih => exact congrArg Nat.succ ih

/-- Every child index retains the same source occurrence and exact preceding and following calls. -/
theorem Calls.indexed [DecidableEq (EdgeKey Symbol Guard)]
    (calls : Calls environment originals before outputs after)
    (index : Nat) (output : Value Symbol Guard) (selected : outputs[index]? = some output) :
    ∃ original current next, originals[index]? = some original ∧
      Calls environment (originals.take index) before (outputs.take index) current ∧
      execute original environment current = .done output next ∧
      Calls environment (originals.drop (index + 1)) next (outputs.drop (index + 1)) after := by
  induction calls generalizing index with
  | nil => simp only [List.getElem?_nil] at selected; cases selected
  | cons original originals before middle after value values called rest ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at selected
          subst output
          exact ⟨original, before, middle, rfl, .nil before, called, rest⟩
      | succ index =>
          obtain ⟨source, current, next, found, earlier, child, later⟩ :=
            ih index (by simpa only [List.getElem?_cons_succ] using selected)
          refine ⟨source, current, next, found, ?_, child, ?_⟩
          · simpa only [List.take_succ_cons] using
              Calls.cons original _ before middle current value _ called earlier
          · simpa only [List.drop_succ_cons, Nat.add_assoc] using later

/-- A shared encoded trace derives the literal stored calls with their own captures at every child heap. -/
theorem from_encoded [DecidableEq (EdgeKey Symbol Guard)]
    (context : List (Value Symbol Guard)) (environment : Environment Symbol Guard)
    (source : State Symbol Guard) (coherent : Coherent source) (contextAvailable : Values source context)
    {originals outputs : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (trace : ChildTrace context [] (context.map (input environment)) originals before outputs after)
    (available : Values source originals) (covered : ∀ leaf ∈ manyLeaves originals, leaf ∈ context) :
    Calls environment originals before outputs after := by
  induction trace with
  | nil => exact .nil _
  | cons original originals before middle after output outputs called rest ih =>
      have childCovered : ∀ leaf ∈ leaves original, leaf ∈ context :=
        fun leaf member => covered leaf (by simp [manyLeaves, member])
      rw [SourceCurrentStoredPlanEquivalence.recapture context original environment source before
        coherent contextAvailable (available original List.mem_cons_self) childCovered] at called
      exact .cons original originals before middle after output outputs called
        (ih (fun value member => available value (List.mem_cons_of_mem _ member))
          (fun leaf member => covered leaf (by simp [manyLeaves, member])))

end MicroCFTA.SourceCurrentStoredSubstitutionCalls
