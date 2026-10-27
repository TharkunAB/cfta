import MicroCFTA.SourceFlatPruningShallowChild
import MicroCFTA.SourceFlatPruningCompletedIndex
import MicroCFTA.SourcePruningEnumerationCachedChild

/-!
# Flat native cached child operations

Allocation preserves the original conditional flag update.
Slot writes use the current direct roots for lost and gained counts.
-/

namespace MicroCFTA.SourceFlatPruningCachedChild

open EnumerationState EnumerationFlatCached
open SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- Classify and allocate one slot without a representative lookup. -/
def allocate (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (node : Option Nat) (before : Cached Symbol EnumGuard) : Option (Nat × Cached Symbol EnumGuard) :=
  (SourcePruningEnumerationNativeIndex.candidate heap (.unenumerated node [])).map fun flag =>
    (before.core.counter,
      ⟨EnumerationFlatState.allocated node before.core,
        fun slot => if flag then
          if slot = before.core.counter then true else before.expandable slot
          else before.expandable slot,
        before.waiting⟩)

/-- Read the original raw bucket before replacing both native indexes. -/
def writeSlot (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (target : Nat) (value : UVarValue Symbol) (before : Cached Symbol EnumGuard) :
    Option (Cached Symbol EnumGuard) :=
  (before.core.values[target]?).bind fun old =>
    EnumerationFlatNativeIndex.write heap target value
      (EnumerationSchedule.references value) (EnumerationSchedule.references old) before

/-- Allocate an ordinary child and store its complete suspended bucket. -/
def prepareOrdinary (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (scs : List Suspended) (value : InternedConstructorTemplates.Value Symbol NativeGuard)
    (before : Cached Symbol EnumGuard) : Option (Fragments.Fragment Symbol × Cached Symbol EnumGuard) :=
  match value with
  | .node _ _ _ _ =>
      if scs.any (fun sc => EqualityTrie.isTerminal sc.trie) then none
      else
        (encodeNode value).bind fun handle =>
          (allocate heap (some handle) before).bind fun allocation =>
            (writeSlot heap allocation.1 (.unenumerated (some handle) scs) allocation.2).map
              fun after => (.hole allocation.1, after)
  | _ => none

/-- A completed old allocation returns the same fresh ID and related complete cache. -/
theorem allocate_completed (related : Related flat earlier)
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (node : Option Nat)
    (completed : SourcePruningEnumerationCachedChild.allocate heap node earlier = some (uv, after)) :
    ∃ next, allocate heap node flat = some (uv, next) ∧ Related next after := by
  simp only [SourcePruningEnumerationCachedChild.allocate, Option.map_eq_some_iff] at completed
  obtain ⟨flag, classified, same⟩ := completed
  obtain ⟨uvSame, afterSame⟩ := Prod.mk.inj same
  subst uv
  subst after
  let next : Cached Symbol EnumGuard :=
    ⟨EnumerationFlatState.allocated node flat.core,
      fun slot => if flag then
        if slot = flat.core.counter then true else flat.expandable slot
        else flat.expandable slot,
      flat.waiting⟩
  refine ⟨next, ?_, ?_⟩
  · simp only [allocate, classified, Option.map_some]
    change some (flat.core.counter, next) = some (earlier.core.counter, next)
    rw [related.core.counter]
  · refine ⟨EnumerationFlatState.allocated_related related.core node, ?_, related.waiting⟩
    change (fun slot => if flag then
      if slot = flat.core.counter then true else flat.expandable slot else flat.expandable slot) = _
    rw [related.core.counter, related.expandable]

/-- Actual old count success supplies both flat count folds at that same old bound. -/
theorem writeSlot_completed (related : Related flat earlier)
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel target : Nat) (value : UVarValue Symbol)
    (completed : SourcePruningEnumerationCachedChild.writeSlot heap fuel target value earlier = some after) :
    ∃ next, writeSlot heap target value flat = some next ∧ Related next after := by
  unfold SourcePruningEnumerationCachedChild.writeSlot at completed
  cases stored : earlier.core.values[target]? with
  | none =>
      simp only [stored, Option.bind_none] at completed
      cases completed
  | some old =>
      simp only [stored, Option.bind_some] at completed
      obtain ⟨next, written, states⟩ := SourceFlatPruningCompletedIndex.write_related related
        heap fuel target value (EnumerationSchedule.references value) (EnumerationSchedule.references old) completed
      refine ⟨next, ?_, states⟩
      simp only [writeSlot, related.core.values, stored, Option.bind_some, written]

/-- A completed old ordinary preparation replays its actual allocation and write. -/
theorem prepareOrdinary_completed (related : Related flat earlier)
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel : Nat) (scs : List Suspended) (value : InternedConstructorTemplates.Value Symbol NativeGuard)
    (completed : SourcePruningEnumerationCachedChild.prepareOrdinary heap fuel scs value earlier =
      some (fragment, after)) :
    ∃ next, prepareOrdinary heap scs value flat = some (fragment, next) ∧ Related next after := by
  cases value with
  | empty | reference _ | union _ _ _ _ | mu _ _ _ _ =>
      simp only [SourcePruningEnumerationCachedChild.prepareOrdinary] at completed
      cases completed
  | node entry edges depth free =>
      by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
      · simp only [SourcePruningEnumerationCachedChild.prepareOrdinary, terminal, ↓reduceIte] at completed
        cases completed
      · simp only [SourcePruningEnumerationCachedChild.prepareOrdinary, terminal, Bool.false_eq_true,
          ↓reduceIte, encodeNode, Option.bind_some, Option.bind_eq_some_iff,
          Option.map_eq_some_iff] at completed
        obtain ⟨allocation, allocated, writtenAfter, written, same⟩ := completed
        obtain ⟨uv, allocatedCache⟩ := allocation
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
        obtain ⟨flatAllocated, flatAllocation, allocations⟩ := allocate_completed related
          heap (some (entry.identity + 1)) allocated
        obtain ⟨next, flatWritten, states⟩ := writeSlot_completed allocations
          heap fuel uv (.unenumerated (some (entry.identity + 1)) scs) written
        refine ⟨next, ?_, states⟩
        simp only [prepareOrdinary, terminal, Bool.false_eq_true, ↓reduceIte, encodeNode,
          Option.bind_some, flatAllocation, flatWritten, Option.map_some]

end MicroCFTA.SourceFlatPruningCachedChild
