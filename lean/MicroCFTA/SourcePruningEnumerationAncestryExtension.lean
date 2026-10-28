import MicroCFTA.EnumerationCompressionFrame
import MicroCFTA.SourcePruningEnumerationKeyShapeBudget

/-!
# Retained recursion keys at every slot

The relation compares complete per-slot recursion histories.
It includes old keys at the next fresh counter.
It makes no claim about the current expansion history.
-/
namespace MicroCFTA.SourcePruningEnumerationAncestryExtension
open EnumerationState EnumerationCorrectness EnumerationCompressionFrame
open SourcePruningEnumerationKeyShapeBudget
variable {Symbol Guard : Type}

/-- Every slot retains every recursion key from the original state. -/
def Extends (before after : State Symbol Guard) : Prop :=
  ∀ slot key, key ∈ before.recursionAncestry slot → key ∈ after.recursionAncestry slot

/-- An unchanged state retains all per-slot keys. -/
theorem Extends.refl (state : State Symbol Guard) : Extends state state :=
  fun _ _ member => member

/-- Successive extensions retain the original per-slot keys. -/
theorem Extends.trans {before middle after : State Symbol Guard}
    (first : Extends before middle) (second : Extends middle after) : Extends before after :=
  fun slot key member => second slot key (first slot key member)

/-- A complete path-compression frame retains every key. -/
theorem Extends.frame {before after : State Symbol Guard} (frame : Frame before after) :
    Extends before after := by
  intro slot key member
  simpa only [frame.recursionAncestry] using member

/-- Actual allocation retains old keys even at its fresh counter. -/
theorem Extends.allocated (before : State Symbol Guard) (node : Option Nat) :
    Extends before (allocated node before) := by
  intro slot key member
  by_cases fresh : slot = before.counter
  · subst slot
    simp only [EnumerationState.allocated, ↓reduceIte, List.mem_eraseDups, List.mem_append]
    exact Or.inr member
  · simpa only [EnumerationState.allocated, ite_eq_right fresh] using member

/-- Actual assimilation retains the target's old keys and every other slot's keys. -/
theorem Extends.assimilated (before : State Symbol Guard) (target source : Nat)
    (merged : UVarValue Symbol) : Extends before (assimilated before target source merged) := by
  intro slot key member
  by_cases same : slot = target
  · subst slot
    simp only [EnumerationCorrectness.assimilated, ↓reduceIte,
      List.mem_eraseDups, List.mem_append]
    exact Or.inr member
  · simpa only [EnumerationCorrectness.assimilated, ite_eq_right same] using member

/-- An extension cannot increase a fixed slot's unused shape count at a fixed handle. -/
theorem Extends.unused_le {before after : State Symbol Guard} (extended : Extends before after)
    (carrier : List (List (List (List Nat)))) (handle slot : Nat) :
    (unused carrier handle (after.recursionAncestry slot)).length ≤
      (unused carrier handle (before.recursionAncestry slot)).length :=
  unused_mono carrier handle _ _ (extended slot)

end MicroCFTA.SourcePruningEnumerationAncestryExtension
