import MicroCFTA.InternedNormalizedUnionReplay
import MicroCFTA.InternedUnionSeparation

/-!
# Ordered root alternatives after removal of several lexical arguments

A literal reference prevents the ordinary union merge. Actual union
readback then retains the canonical member list. Removing several bare
references commutes with first-identity source deduplication.
-/
namespace MicroCFTA.SourceCurrentNativeStrippedAlternatives
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedNestedProvenance InternedRootAlternativeLists
open InternedUnionFilterFusion InternedUnionSeparation
open InternedBinderProtocol (Reference)

/-- Remove each selected bare reference without changing the order of other alternatives. -/
def stripMany : List Reference → List (Value Symbol Guard) → List (Value Symbol Guard)
  | [], values => values
  | name :: names, values => stripMany names (remove name values)

/-- Removing several reference identities commutes with source deduplication. -/
theorem strip_distinct (names : List Reference) (values : List (Value Symbol Guard)) :
    stripMany names (distinctNodes values) = distinctNodes (stripMany names values) := by
  induction names generalizing values with
  | nil => rfl
  | cons name names ih =>
      simp only [stripMany, remove_distinct, ih]

/-- Any original bare reference prevents ordinary merging and retains the exact canonical member list. -/
theorem union_members [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (inputs : Values state values)
    (present : ∃ name, Value.reference name ∈ values.flatMap unionMembers) :
    unionMembers (run (makeUnion values) state).1 = distinctNodes (values.flatMap unionMembers) := by
  obtain ⟨name, original⟩ := present
  obtain ⟨kept, member, identity⟩ := distinctNodes_covers (values.flatMap unionMembers) (.reference name) original
  have same : kept = .reference name := (referenceOf_self_iff name kept).mp identity
  rw [same] at member
  cases selected : distinctNodes (values.flatMap unionMembers) with
  | nil => simp [selected] at member
  | cons first rest =>
      cases rest with
      | nil =>
          have firstSelf : first = .reference name := by simpa only [selected, List.mem_singleton] using member.symm
          simp [makeUnion, selected, firstSelf, run, unionMembers]
      | cons second tail =>
          have ordinary := ordinary_none name (first :: second :: tail) (by simpa only [selected] using member)
          obtain ⟨entry, returned⟩ := union_readback values first second tail state facts inputs selected ordinary
          simp only [returned, unionMembers, selected]

/-- Actual union normalization preserves the ordered stripped alternatives when a bare reference occurs. -/
theorem union_stripped [DecidableEq (EdgeKey Symbol Guard)] (names : List Reference)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (inputs : Values state values)
    (present : ∃ name, Value.reference name ∈ values.flatMap unionMembers) :
    stripMany names (unionMembers (run (makeUnion values) state).1) =
      distinctNodes (stripMany names (values.flatMap unionMembers)) := by
  rw [union_members values state facts inputs present, strip_distinct]

end MicroCFTA.SourceCurrentNativeStrippedAlternatives
