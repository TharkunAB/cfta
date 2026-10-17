import MicroCFTA.SourceCurrentNativeStrippedAlternatives
import MicroCFTA.InternedStoredMuOrigins

/-!
# Stripped alternatives through the actual callback root filter

A retained outer reference prevents ordinary merging after own-reference
removal. The actual callback filter therefore retains the same ordered
alternatives after all selected lexical references are removed.
-/
namespace MicroCFTA.SourceCurrentNativeStrippedFilter
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedNestedProvenance InternedStoredMuOrigins
open InternedRootAlternativeLists InternedNormalizedUnionReplay
open SourceCurrentNativeStrippedAlternatives
open InternedBinderProtocol (Reference)

private theorem strip_as_filter (names : List Reference) (values : List (Value Symbol Guard)) :
    stripMany names values = values.filter (fun value => names.all (fun name => value.referenceOf != .ref name)) := by
  induction names generalizing values with
  | nil => simp [stripMany]
  | cons name names ih => simp only [stripMany, ih, remove, List.filter_filter, List.all_cons]

/-- Removing an already selected reference does not change the final stripped list. -/
theorem strip_remove (names : List Reference) (own : Reference) (selected : own ∈ names)
    (values : List (Value Symbol Guard)) : stripMany names (remove own values) = stripMany names values := by
  rw [strip_as_filter, strip_as_filter]
  simp only [remove, List.filter_filter]
  apply List.filter_congr
  intro value
  by_cases all : names.all (fun name => value.referenceOf != .ref name) = true
  · have kept := (List.all_eq_true.mp all) own selected
    simp only [all, kept, Bool.and_self]
  · have failed : names.all (fun name => value.referenceOf != .ref name) = false := Bool.eq_false_iff.mpr all
    simp only [failed, Bool.and_false]

/-- A surviving distinct outer reference makes actual own filtering preserve stripped alternatives. -/
theorem filter [DecidableEq (EdgeKey Symbol Guard)] (names : List Reference) (own : Reference)
    (value : Value Symbol Guard) (state : State Symbol Guard) (normal : Normal state)
    (available : Available state value) (selected : own ∈ names)
    (outer : ∃ name, name ≠ own ∧ Value.reference name ∈ unionMembers value) :
    stripMany names (unionMembers (run (withoutSelfReference own value) state).1) =
      stripMany names (unionMembers value) := by
  cases value with
  | empty | reference | node | mu => rfl
  | union entry members depth free =>
      by_cases present : members.any (fun member => member.referenceOf == .ref own) = true
      · obtain ⟨name, different, included⟩ := outer
        have retained : Value.reference name ∈ remove own members := by
          simp only [remove, List.mem_filter]
          exact ⟨included, by simpa only [Value.referenceOf, bne_iff_ne, InternedBinderProtocol.NodeRef.ref.injEq] using different⟩
        have inputs : Values state (remove own members) := by
          intro member included
          exact available.children member (List.mem_filter.mp included).1
        have atomic := InternedUnionNormalForm.resident_flat state normal.flat _ available.resident
        have proper := InternedUnionNonemptyMembers.resident_membersNonempty state normal.members _ available.resident
        have flattened := InternedNormalizedUnionReplay.flattened (remove own members)
          (fun member included => atomic member (List.mem_filter.mp included).1)
          (fun member included => proper member (List.mem_filter.mp included).1)
        have readback := union_members (remove own members) state normal.facts inputs
          ⟨name, by simpa only [flattened] using retained⟩
        have shape := InternedNonemptyRecords.resident_nonempty state normal.proper _ available.resident
        have unique : ((remove own members).map Value.referenceOf).Nodup :=
          (List.filter_sublist.map Value.referenceOf).nodup shape.2
        simp only [withoutSelfReference, present, ↓reduceIte]
        change stripMany names (unionMembers (run (makeUnion (remove own members)) state).1) = stripMany names members
        rw [readback, flattened, distinct_of_nodup _ unique, strip_remove names own selected]
      · simp only [withoutSelfReference, present, Bool.false_eq_true, ↓reduceIte, run]

end MicroCFTA.SourceCurrentNativeStrippedFilter
