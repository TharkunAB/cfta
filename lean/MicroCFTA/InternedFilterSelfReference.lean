import MicroCFTA.InternedCallbackEmptiness
import MicroCFTA.InternedUnionNormalForm
import MicroCFTA.InternedGateRank

/-!
# Root filtering preserves the direct-self case

An ordinary constructor cannot return a literal reference. A union can
return one only from a flattened operand. Actual root self filtering
removes that operand from flat source unions. It cannot create a bare
self result that was absent before filtering.
-/
namespace MicroCFTA.InternedFilterSelfReference
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance InternedNestedMissReadback
open InternedUnionNormalForm InternedGateRank
open InternedBinderProtocol (Reference NodeKey)

/-- Complete ordinary-node readback never returns a literal recursive reference. -/
theorem makeNode_not_reference [DecidableEq (EdgeKey Symbol Guard)] (name : Reference)
    (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard) (coherent : Coherent state) :
    (run (makeNode edges) state).1 ≠ .reference name := by
  unfold makeNode
  dsimp only
  split
  · simp [run]
  · rename_i first rest _
    simp only [run]
    obtain ⟨entry, fields⟩ := requested_fields
      (.node ((first :: rest).map (fun edge => edge.entry.identity))) (identifyNode (first :: rest)) state coherent
      (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩)
    intro same
    rw [same] at fields
    exact fields

/-- A union without the selected flattened reference cannot return that reference. -/
theorem makeUnion_not_reference [DecidableEq (EdgeKey Symbol Guard)] (name : Reference)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard) (coherent : Coherent state)
    (absent : .reference name ∉ values.flatMap unionMembers) :
    (run (makeUnion values) state).1 ≠ .reference name := by
  cases normalized : distinctNodes (values.flatMap unionMembers) with
  | nil => simp [makeUnion, normalized, run]
  | cons first rest =>
      cases rest with
      | nil =>
          intro same
          have equal : first = .reference name := by simpa only [makeUnion, normalized, run] using same
          exact absent (equal ▸ distinctNodes_member _ first (by simp [normalized]))
      | cons second tail =>
          cases ordinary : ordinaryEdges (first :: second :: tail) with
          | some edges => simpa only [makeUnion, normalized, ordinary] using makeNode_not_reference name edges state coherent
          | none =>
              simp only [makeUnion, normalized, ordinary, run]
              obtain ⟨entry, fields⟩ := requested_fields
                (.union ((first :: second :: tail).map Value.referenceOf))
                (fun entry => .union entry (first :: second :: tail)
                  (maximumDepth (first :: second :: tail)) (childFree (first :: second :: tail)))
                state coherent (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩)
              intro same
              rw [same] at fields
              exact fields

/-- A flat source union loses every candidate that could return the removed literal reference. -/
theorem filter_self_iff [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (value : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (flat : Flat state) (available : Available state value) :
    (run (withoutSelfReference name value) state).1 = .reference name ↔ value = .reference name := by
  cases value <;> simp only [withoutSelfReference, run] <;> try exact Iff.rfl
  case union entry members depth free =>
    split
    · constructor
      · intro same
        apply False.elim
        apply makeUnion_not_reference name _ state coherent ?_ same
        intro present
        obtain ⟨source, member, included⟩ := List.mem_flatMap.mp present
        have atomic := resident_flat state flat _ available.resident source (List.mem_filter.mp member).1
        have different := (withoutSelfReference_members name members source).mp member |>.2
        cases source <;> simp_all [Atomic, unionMembers]
      · intro impossible; cases impossible
    · exact Iff.rfl

/-- Arbitrary source callback normalization preserves the exact direct-self result, including pending executions. -/
theorem callback_self_iff [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (name : Reference) (state : State Symbol Guard)
    (facts : Facts state) (inputs : Values state environment) (argument : Available state (.reference name))
    (flat : Flat state) :
    (∃ after, callback body environment name state = .done (.reference name) after) ↔
      ∃ after, build body (.reference name :: environment) state = .done (.reference name) after := by
  have all : Values state (.reference name :: environment) := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact argument
    · exact inputs value member
  cases returned : build body (.reference name :: environment) state with
  | pending key after => simp [callback, returned, Outcome.bind]
  | done value after =>
      have checked := build_verified body _ state facts all
      have afterFacts : Facts after := by simpa only [returned, Outcome.state] using checked.facts
      have afterFlat : Flat after := by simpa only [returned, Outcome.state] using build_flat body _ state facts all flat
      have same := filter_self_iff name value after afterFacts.coherent afterFlat (checked.result value after returned)
      simpa [callback, returned, Outcome.bind, work] using same

end MicroCFTA.InternedFilterSelfReference
