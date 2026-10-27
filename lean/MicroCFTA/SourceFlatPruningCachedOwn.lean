import MicroCFTA.SourceFlatPruningCachedPrepare
import MicroCFTA.SourcePruningEnumerationCachedOwn

/-!
# Flat own-class allocation and ordered child staging

The traversal allocates one raw ID per projected trie, in list order.
The prepared payload retains each optional flat child action.
-/

namespace MicroCFTA.SourceFlatPruningCachedOwn

open EnumerationState EnumerationFlatCached
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable {EnumGuard NativeGuard : Type}

/-- Allocate every projected class in the original order. -/
def suspendMany (heap : InternedConstructorTemplates.State Symbol NativeGuard) :
    List EqualityTrie.Trie → Cached Symbol EnumGuard → Option (List Suspended × Cached Symbol EnumGuard)
  | [], before => some ([], before)
  | trie :: rest, before =>
      (SourceFlatPruningCachedChild.allocate heap none before).bind fun allocation =>
        (suspendMany heap rest allocation.2).map fun result =>
          (⟨trie, allocation.1⟩ :: result.1, result.2)

/-- Allocate own classes and retain the ordered optional child actions. -/
noncomputable def prepare (heap : InternedConstructorTemplates.State Symbol Constraint)
    (scs : List Suspended) (edge : EdgeValue Symbol Constraint) (before : Cached Symbol Constraint) :
    Option (List ((Symbol × List (Value Symbol Constraint × List Suspended ×
      Option (EnumerationFlatState.Action Symbol Constraint (Fragments.Fragment Symbol))) ×
        Option Constraint) × Cached Symbol Constraint)) :=
  if arityAllows edge.children.length scs then
    match SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none => none
    | some (tries, residual) =>
        (suspendMany heap tries before).map fun result =>
          [((edge.entry.key.symbol,
            edge.children.zipIdx.map (fun indexed =>
              (indexed.1, descendScs indexed.2 scs ++ descendScs indexed.2 result.1,
                SourceFlatPruningShallowChild.prepareChild (EnumGuard := Constraint)
                  (descendScs indexed.2 scs ++ descendScs indexed.2 result.1) indexed.1)), residual), result.2)]
  else some []

/-- Relate each native child, actual bucket and optional captured action. -/
def StageRelated
    (flat : Value Symbol Constraint × List Suspended ×
      Option (EnumerationFlatState.Action Symbol Constraint (Fragments.Fragment Symbol)))
    (earlier : Value Symbol Constraint × List Suspended ×
      Option (EnumerateM Symbol Constraint (Fragments.Fragment Symbol))) : Prop :=
  flat.1 = earlier.1 ∧ flat.2.1 = earlier.2.1 ∧
    SourceFlatPruningShallowChild.OptionalActions flat.2.2 earlier.2.2

/-- Retain rejection, partiality and the complete ordered staged payload. -/
def PreparedRelated
    (flat : Option (List ((Symbol × List (Value Symbol Constraint × List Suspended ×
      Option (EnumerationFlatState.Action Symbol Constraint (Fragments.Fragment Symbol))) ×
        Option Constraint) × Cached Symbol Constraint)))
    (earlier : Option (List ((Symbol × List (Value Symbol Constraint × List Suspended ×
      Option (EnumerateM Symbol Constraint (Fragments.Fragment Symbol))) ×
        Option Constraint) × EnumerationExpandableIndex.Cached Symbol Constraint))) : Prop :=
  match flat, earlier with
  | none, none => True
  | some flat, some earlier =>
      Language.All₂ (fun left right =>
        left.1.1 = right.1.1 ∧
        Language.All₂ StageRelated left.1.2.1 right.1.2.1 ∧
        left.1.2.2 = right.1.2.2 ∧ Related left.2 right.2) flat earlier
  | _, _ => False

/-- The actual traversals return the same suspended IDs and related complete caches. -/
theorem suspendMany_related
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (tries : List EqualityTrie.Trie) :
    ∀ {flat : Cached Symbol EnumGuard} {earlier : EnumerationExpandableIndex.Cached Symbol EnumGuard},
      Related flat earlier →
      ∃ (own : List Suspended) (next : Cached Symbol EnumGuard)
        (after : EnumerationExpandableIndex.Cached Symbol EnumGuard),
        suspendMany heap tries flat = some (own, next) ∧
        SourcePruningEnumerationCachedOwn.suspendMany heap tries earlier = some (own, after) ∧
        Related next after := by
  induction tries with
  | nil =>
      intro flat earlier related
      exact ⟨[], flat, earlier, rfl, rfl, related⟩
  | cons trie rest ih =>
      intro flat earlier related
      let middle : Cached Symbol EnumGuard :=
        ⟨EnumerationFlatState.allocated none flat.core, flat.expandable, flat.waiting⟩
      let oldMiddle : EnumerationExpandableIndex.Cached Symbol EnumGuard :=
        ⟨EnumerationState.allocated none earlier.core, earlier.expandable, earlier.waiting⟩
      have allocated : SourceFlatPruningCachedChild.allocate heap none flat =
          some (flat.core.counter, middle) := rfl
      have oldAllocated : SourcePruningEnumerationCachedChild.allocate heap none earlier =
          some (earlier.core.counter, oldMiddle) := rfl
      have middleRelated : Related middle oldMiddle :=
        ⟨EnumerationFlatState.allocated_related related.core none, related.expandable, related.waiting⟩
      obtain ⟨own, next, after, tail, oldTail, states⟩ := ih middleRelated
      refine ⟨⟨trie, earlier.core.counter⟩ :: own, next, after, ?_, ?_, states⟩
      · simp only [suspendMany, allocated, Option.bind_some, tail, Option.map_some, related.core.counter]
      · simp only [SourcePruningEnumerationCachedOwn.suspendMany, oldAllocated,
          Option.bind_some, oldTail, Option.map_some]

/-- A completed old own traversal identifies the actual flat traversal without new bounds. -/
theorem suspendMany_completed (related : Related flat earlier)
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (tries : List EqualityTrie.Trie)
    (observed : SourcePruningEnumerationCachedOwn.suspendMany heap tries earlier = some (own, after)) :
    ∃ next, suspendMany heap tries flat = some (own, next) ∧ Related next after := by
  obtain ⟨recorded, next, oldAfter, actual, oldActual, states⟩ := suspendMany_related heap tries related
  have same := Option.some.inj (oldActual.symm.trans observed)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  exact ⟨next, actual, states⟩

/-- The selected own prefix preserves every optional action and both cached indexes. -/
theorem prepare_related (related : Related flat earlier)
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (scs : List Suspended) (edge : EdgeValue Symbol Constraint) :
    PreparedRelated (prepare heap scs edge flat)
      (SourcePruningEnumerationCachedOwn.prepare heap scs edge earlier) := by
  by_cases allowed : arityAllows edge.children.length scs = true
  · cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none =>
        simp only [prepare, SourcePruningEnumerationCachedOwn.prepare, allowed, ↓reduceIte,
          projected, PreparedRelated]
    | some pair =>
        obtain ⟨tries, residual⟩ := pair
        obtain ⟨own, next, after, actual, oldActual, states⟩ := suspendMany_related heap tries related
        have staged : Language.All₂ StageRelated
            (edge.children.zipIdx.map fun indexed =>
              (indexed.1, descendScs indexed.2 scs ++ descendScs indexed.2 own,
                SourceFlatPruningShallowChild.prepareChild (EnumGuard := Constraint)
                  (descendScs indexed.2 scs ++ descendScs indexed.2 own) indexed.1))
            (edge.children.zipIdx.map fun indexed =>
              (indexed.1, descendScs indexed.2 scs ++ descendScs indexed.2 own,
                SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint)
                  (descendScs indexed.2 scs ++ descendScs indexed.2 own) indexed.1)) := by
          induction edge.children.zipIdx with
          | nil => exact .nil
          | cons indexed rest ih =>
              exact .cons ⟨rfl, rfl, SourceFlatPruningShallowChild.prepareChild_related _ _⟩ ih
        simp only [prepare, SourcePruningEnumerationCachedOwn.prepare, allowed, ↓reduceIte,
          projected, actual, oldActual, Option.map_some, PreparedRelated]
        exact .cons ⟨rfl, staged, rfl, states⟩ .nil
  · simp only [prepare, SourcePruningEnumerationCachedOwn.prepare, allowed, PreparedRelated]
    exact .nil

end MicroCFTA.SourceFlatPruningCachedOwn
