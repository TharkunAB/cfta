import MicroCFTA.SourceCurrentRequiredExposureSafe
import MicroCFTA.SourceCurrentRequiredUnionNormal
import MicroCFTA.SourceEqualityRequiredSemanticCache

/-!
# Required exposure safety from the cached finite shortcut

Coherent depth and free-name fields pass the finite shortcut to children.
Actual union irreducibility and the existing normalization fields exclude
a closed union at depth zero. Ordinary guards remain unrestricted.
-/
namespace MicroCFTA.SourceCurrentRequiredFiniteExposure
open InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentRequiredUnionNormal SourceCurrentRequiredRowOrigins
open SourceEqualityNeeded
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => State Symbol Guard

private theorem child_closed (values : List (Value Symbol Guard)) (closed : childFree values = [])
    (value : Value Symbol Guard) (member : value ∈ values) : value.free = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro name included
  have found := (childFree_member values name).mpr ⟨value, member, included⟩
  rw [closed] at found
  cases found

private theorem ordinary_edges (values : List (Value Symbol Guard))
    (nodes : ∀ value ∈ values, ∃ entry rows level free, value = .node entry rows level free) :
    ∃ rows, ordinaryEdges values = some rows := by
  induction values with
  | nil => exact ⟨[], rfl⟩
  | cons first rest ih =>
      obtain ⟨entry, rows, level, free, rfl⟩ := nodes first List.mem_cons_self
      obtain ⟨later, done⟩ := ih (fun value member => nodes value (List.mem_cons_of_mem _ member))
      exact ⟨rows ++ later, by simp only [ordinaryEdges, done, Option.map_some]⟩

/-- A closed depth-zero available record has an ordinary head under actual union normalization. -/
theorem ordinary_of_zero_closed (state : Heap) (semantic : SemanticReady state)
    (normal : UnionNormal state) (value : Value Symbol Guard) (available : Available state value)
    (zero : value.depth = 0) (closed : value.free = []) : Ordinary value := by
  have coherent := semantic.ready.semantic.1.normal.facts.coherent
  cases value with
  | empty | node => trivial
  | reference name => simp only [Value.free, List.cons_ne_self] at closed
  | mu entry body depth ordinary => simp only [Value.depth, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false] at zero
  | union entry members level free =>
      have irreducible : ordinaryEdges members = none := normal entry.key _ (available.resident entry rfl)
      have flat := InternedUnionNormalForm.resident_flat state semantic.ready.semantic.1.normal.flat _ available.resident
      have nonempty := InternedUnionNonemptyMembers.resident_membersNonempty state
        semantic.ready.semantic.1.normal.members _ available.resident
      have exactFree := InternedNormalizationFree.union_free state coherent entry members level free available.resident
      have allClosed : childFree members = [] := exactFree.symm.trans closed
      have nodes : ∀ value ∈ members, ∃ entry rows level free, value = .node entry rows level free := by
        intro value member
        have childZero := InternedUnionSeparation.child_depth state coherent
          (.union entry members level free) value available member
        rw [zero] at childZero
        have childClosed := child_closed members allClosed value member
        cases value with
        | empty => exact False.elim (nonempty .empty member rfl)
        | reference name => simp only [Value.free, List.cons_ne_self] at childClosed
        | union actual own depth free => exact False.elim (flat _ member)
        | mu actual body depth ordinary => simp only [Value.depth] at childZero; omega
        | node actual rows depth free => exact ⟨actual, rows, depth, free, rfl⟩
      obtain ⟨rows, done⟩ := ordinary_edges members nodes
      rw [irreducible] at done
      cases done

/-- The initial finite shortcut supplies exposure safety for every requirement without plain-guard premises. -/
theorem finite_exposure (needed : Needed) (state : Heap) (semantic : SemanticReady state)
    (normal : UnionNormal state) (value : Value Symbol Guard) (available : Available state value)
    (zero : value.depth = 0) (closed : value.free = []) : ExposureSafe needed value := by
  have coherent := semantic.ready.semantic.1.normal.facts.coherent
  revert needed zero closed
  induction available with
  | intro value resident issued children ih =>
      intro needed zero closed
      have available : Available state value := .intro value resident issued children
      have ordinary := ordinary_of_zero_closed state semantic normal value available zero closed
      cases value with
      | empty => exact .empty needed
      | reference | union | mu => cases ordinary
      | node entry rows level free =>
          cases needed with
          | node entries =>
              apply ExposureSafe.ordinary entries entry rows level free
              intro row member index childNeeded _ child found
              have inside : child ∈ row.children := List.mem_of_getElem? found
              have selected : child ∈ rows.flatMap EdgeValue.children := List.mem_flatMap.mpr ⟨row, member, inside⟩
              have childZero := InternedUnionSeparation.child_depth state coherent
                (.node entry rows level free) child available selected
              rw [zero] at childZero
              have exactFree := InternedNormalizationFree.node_free state coherent entry rows level free resident
              have childClosed := child_closed _ (exactFree.symm.trans closed) child selected
              exact ih child selected childNeeded (Nat.eq_zero_of_le_zero childZero) childClosed

end MicroCFTA.SourceCurrentRequiredFiniteExposure
