import MicroCFTA.SourceFlatPruningCachedChild
import MicroCFTA.SourcePruningEnumerationCachedPrepare

/-!
# Flat cached shallow child preparation

Empty is a supported rejection. References and terminal buckets stay partial.
Ordinary children store their bucket. Recursive boundaries allocate an empty bucket.
-/

namespace MicroCFTA.SourceFlatPruningCachedPrepare

open EnumerationState EnumerationFlatCached
open InternedConstructorTemplates SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- Prepare the same supported cached branches with direct-root counts. -/
def prepareChild (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (scs : List Suspended) (value : Value Symbol NativeGuard) (before : Cached Symbol EnumGuard) :
    Option (List (Fragments.Fragment Symbol × Cached Symbol EnumGuard)) :=
  match value with
  | .empty => some []
  | .reference _ => none
  | .node _ _ _ _ =>
      (SourceFlatPruningCachedChild.prepareOrdinary heap scs value before).map fun result => [result]
  | .union _ _ _ _ | .mu _ _ _ _ =>
      if scs.any (fun sc => EqualityTrie.isTerminal sc.trie) then none
      else
        (encodeNode value).bind fun handle =>
          (SourceFlatPruningCachedChild.allocate heap (some handle) before).map fun allocation =>
            [(.hole allocation.1, allocation.2)]

/-- Retain the fragment and the complete cache at every ordered row. -/
def RowsRelated (flat : List (Fragments.Fragment Symbol × Cached Symbol EnumGuard))
    (earlier : List (Fragments.Fragment Symbol × EnumerationExpandableIndex.Cached Symbol EnumGuard)) : Prop :=
  Language.All₂ (fun left right => left.1 = right.1 ∧ Related left.2 right.2) flat earlier

/-- Every completed old preparation gives the actual related flat rows. -/
theorem prepareChild_completed (related : Related flat earlier)
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel : Nat) (scs : List Suspended) (value : Value Symbol NativeGuard)
    (completed : SourcePruningEnumerationCachedPrepare.prepareChild heap fuel scs value earlier = some rows) :
    ∃ next, prepareChild heap scs value flat = some next ∧ RowsRelated next rows := by
  cases value with
  | empty =>
      simp only [SourcePruningEnumerationCachedPrepare.prepareChild, Option.some.injEq] at completed
      subst rows
      exact ⟨[], rfl, .nil⟩
  | reference name =>
      simp only [SourcePruningEnumerationCachedPrepare.prepareChild] at completed
      cases completed
  | node entry edges depth free =>
      simp only [SourcePruningEnumerationCachedPrepare.prepareChild, Option.map_eq_some_iff] at completed
      obtain ⟨result, prepared, rowsSame⟩ := completed
      obtain ⟨fragment, after⟩ := result
      subst rows
      obtain ⟨next, flatPrepared, states⟩ := SourceFlatPruningCachedChild.prepareOrdinary_completed
        related heap fuel scs (.node entry edges depth free) prepared
      refine ⟨[(fragment, next)], ?_, .cons ⟨rfl, states⟩ .nil⟩
      simp only [prepareChild, flatPrepared, Option.map_some]
  | union entry _ _ _ | mu entry _ _ _ =>
      by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
      · simp only [SourcePruningEnumerationCachedPrepare.prepareChild, terminal, ↓reduceIte] at completed
        cases completed
      · simp only [SourcePruningEnumerationCachedPrepare.prepareChild, terminal, Bool.false_eq_true,
          ↓reduceIte, encodeNode, Option.bind_some, Option.map_eq_some_iff] at completed
        obtain ⟨allocation, allocated, rowsSame⟩ := completed
        obtain ⟨uv, after⟩ := allocation
        subst rows
        obtain ⟨next, flatAllocated, states⟩ := SourceFlatPruningCachedChild.allocate_completed related
          heap (some (entry.identity + 1)) allocated
        refine ⟨[(.hole uv, next)], ?_, .cons ⟨rfl, states⟩ .nil⟩
        simp only [prepareChild, terminal, Bool.false_eq_true, ↓reduceIte, encodeNode,
          Option.bind_some, flatAllocated, Option.map_some]

/-- Every present flat sidecar erases to the actual flat shallow action. -/
theorem erase_some (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (scs : List Suspended) (value : Value Symbol NativeGuard) (before : Cached Symbol EnumGuard)
    (rows : List (Fragments.Fragment Symbol × Cached Symbol EnumGuard))
    (cached : prepareChild heap scs value before = some rows) :
    (SourceFlatPruningShallowChild.prepareChild scs value).map (fun action => action before.core) =
      some (rows.map fun row => .ok (row.1, row.2.core)) := by
  cases value with
  | empty =>
      simp only [prepareChild, Option.some.injEq] at cached
      subst rows
      rfl
  | reference name =>
      simp only [prepareChild] at cached
      cases cached
  | node entry edges depth free =>
      by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
      · simp only [prepareChild, SourceFlatPruningCachedChild.prepareOrdinary, terminal, ↓reduceIte] at cached
        cases cached
      · simp only [prepareChild, Option.map_eq_some_iff] at cached
        obtain ⟨result, prepared, rowsSame⟩ := cached
        subst rows
        simp only [SourceFlatPruningCachedChild.prepareOrdinary, terminal, Bool.false_eq_true,
          ↓reduceIte, encodeNode, Option.bind_some, Option.bind_eq_some_iff,
          Option.map_eq_some_iff] at prepared
        obtain ⟨allocation, allocated, after, written, resultSame⟩ := prepared
        subst result
        simp only [SourceFlatPruningCachedChild.allocate, Option.map_eq_some_iff] at allocated
        obtain ⟨flag, _classified, allocationSame⟩ := allocated
        subst allocation
        simp only [SourceFlatPruningCachedChild.writeSlot, Option.bind_eq_some_iff,
          EnumerationFlatNativeIndex.write, Option.map_eq_some_iff] at written
        obtain ⟨old, _stored, afterFlag, _afterClassified, afterSame⟩ := written
        subst after
        simp only [SourceFlatPruningShallowChild.prepareChild, terminal, Bool.false_eq_true,
          ↓reduceIte, encodeNode, Option.map_some, List.map_cons, List.map_nil]
        rfl
  | union entry _ _ _ | mu entry _ _ _ =>
      by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
      · simp only [prepareChild, terminal, ↓reduceIte] at cached
        cases cached
      · simp only [prepareChild, terminal, Bool.false_eq_true, ↓reduceIte, encodeNode,
          Option.bind_some, Option.map_eq_some_iff] at cached
        obtain ⟨allocation, allocated, rowsSame⟩ := cached
        subst rows
        simp only [SourceFlatPruningCachedChild.allocate, Option.map_eq_some_iff] at allocated
        obtain ⟨flag, _classified, allocationSame⟩ := allocated
        subst allocation
        simp only [SourceFlatPruningShallowChild.prepareChild, terminal, Bool.false_eq_true,
          ↓reduceIte, encodeNode, Option.map_some, List.map_cons, List.map_nil]
        rfl

end MicroCFTA.SourceFlatPruningCachedPrepare
