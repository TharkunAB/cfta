import MicroCFTA.InternedFreshOrdinaryActiveOrigins
import MicroCFTA.SourceCurrentStoredLiteralRowLineage

/-!
# Exact original slots for row-bearing source captures

Actual callback crossings add literal references before the original inputs.
A literal reference has no structural row. A row-bearing lookup therefore
retains its exact index in the original input suffix.
-/
namespace MicroCFTA.SourceCurrentSourceCaptureOriginalSlots
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryActiveOrigins (Crossing Path)
open SourceCurrentStoredLiteralRowLineage (RowAt)

private theorem reference_prefix [DecidableEq (EdgeKey Symbol Guard)]
    (crossings : List (Crossing Symbol Guard)) (initial : List (Value Symbol Guard))
    (captured : Value Symbol Guard) (row : EdgeValue Symbol Guard) (inside : RowAt captured row)
    (slot : Nat)
    (found : (crossings.map (fun crossing => Value.reference crossing.name) ++ initial)[slot]? = some captured) :
    ∃ originalSlot, slot = crossings.length + originalSlot ∧ initial[originalSlot]? = some captured := by
  induction crossings generalizing slot with
  | nil => exact ⟨slot,by simp,by simpa only [List.map_nil,List.nil_append] using found⟩
  | cons crossing crossings ih =>
      cases slot with
      | zero =>
          have same : Value.reference crossing.name = captured := by
            simpa only [List.map_cons,List.cons_append,List.getElem?_cons_zero,Option.some.injEq] using found
          subst captured
          cases inside
      | succ slot =>
          have tail : (crossings.map (fun crossing => Value.reference crossing.name) ++ initial)[slot]? = some captured := by
            simpa only [List.map_cons,List.cons_append,List.getElem?_cons_succ] using found
          obtain ⟨originalSlot,offset,selected⟩ := ih slot tail
          exact ⟨originalSlot,by simp only [List.length_cons]; omega,selected⟩

/-- A row-bearing capture retains its exact original index after the callback prefix. -/
theorem original_slot [DecidableEq (EdgeKey Symbol Guard)]
    {root expression : Syntax Symbol Guard} {initial inputs : List (Value Symbol Guard)}
    {crossings : List (Crossing Symbol Guard)}
    (path : Path root initial expression inputs crossings) (slot : Nat)
    (captured : Value Symbol Guard) (found : inputs[slot]? = some captured)
    (row : EdgeValue Symbol Guard) (inside : RowAt captured row) :
    ∃ originalSlot, slot = crossings.length + originalSlot ∧ initial[originalSlot]? = some captured := by
  apply reference_prefix crossings initial captured row inside slot
  simpa only [path.inputs] using found

/-- Empty original inputs exclude every row-bearing capture along the supplied source path. -/
theorem empty_initial [DecidableEq (EdgeKey Symbol Guard)]
    {root expression : Syntax Symbol Guard} {inputs : List (Value Symbol Guard)}
    {crossings : List (Crossing Symbol Guard)}
    (path : Path root [] expression inputs crossings) (slot : Nat)
    (captured : Value Symbol Guard) (found : inputs[slot]? = some captured)
    (row : EdgeValue Symbol Guard) : ¬ RowAt captured row := by
  intro inside
  obtain ⟨originalSlot,_offset,selected⟩ := original_slot path slot captured found row inside
  simp only [List.getElem?_nil] at selected
  cases selected

end MicroCFTA.SourceCurrentSourceCaptureOriginalSlots

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.SourceCurrentSourceCaptureOriginalSlots.original_slot
#print MicroCFTA.SourceCurrentSourceCaptureOriginalSlots.original_slot
#print axioms MicroCFTA.SourceCurrentSourceCaptureOriginalSlots.original_slot
#check @MicroCFTA.SourceCurrentSourceCaptureOriginalSlots.empty_initial
#print MicroCFTA.SourceCurrentSourceCaptureOriginalSlots.empty_initial
#print axioms MicroCFTA.SourceCurrentSourceCaptureOriginalSlots.empty_initial
