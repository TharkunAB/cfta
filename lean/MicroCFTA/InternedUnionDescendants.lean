import MicroCFTA.InternedBinderRetention
import MicroCFTA.InternedLiveEdges

/-!
# Recursive descendant retention through every source union branch

Stored ordinary nodes contain only live edges. A union that merges their
edges therefore retains every actual recursive descendant. The remaining
branches use complete canonical record readback. This extends retention
from a bare Mu operand to Mu records below constructors and unions.
-/
namespace MicroCFTA.InternedUnionDescendants
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedUnionSeparation InternedUnionRetention
open InternedEdgeResidency InternedLiveEdges
open InternedBinderProtocol (NodeKey Reference)

/-- Concatenate two finite stored-child paths. -/
theorem retains_trans (first : Retains middle value) (second : Retains needle middle) : Retains needle value := by
  induction first with
  | here => exact second
  | step member _ ih => exact .step member ih

/-- Flattening a root union retains a member containing any Mu descendant. -/
theorem flatten_retains (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (value : Value Symbol Guard) (retained : Retains (.mu entry body depth ordinary) value) :
    ∃ member ∈ unionMembers value, Retains (.mu entry body depth ordinary) member := by
  cases value with
  | empty => cases retained with | step member _ => simp [semanticChildren] at member
  | union source members level free =>
      cases retained with
      | step member tail => exact ⟨_, member, tail⟩
  | reference | node | mu => exact ⟨_, by simp [unionMembers], retained⟩

/-- Complete cached union fields retain every named canonical member as a stored child. -/
theorem union_readback_member (state : State Symbol Guard) (coherent : Coherent state)
    (members : List (Value Symbol Guard)) (entry : Interned NodeKey) (result member : Value Symbol Guard)
    (fields : NodeFields (.union (members.map Value.referenceOf)) entry result)
    (resultAvailable : Available state result) (memberAvailable : Available state member)
    (present : member ∈ members) : Retains member result := by
  cases result with
  | empty | reference | node | mu => simp [NodeFields, muKey] at fields
  | union actual actualMembers depth free =>
      have sameIds : members.map Value.referenceOf = actualMembers.map Value.referenceOf := NodeKey.union.inj fields.2.1
      have hasId : member.referenceOf ∈ actualMembers.map Value.referenceOf := by
        rw [← sameIds]
        exact List.mem_map.mpr ⟨member, present, rfl⟩
      obtain ⟨selected, included, equalId⟩ := List.mem_map.mp hasId
      have selectedAvailable := resultAvailable.children selected included
      have equal := resident_reference_injective state coherent selected member
        selectedAvailable.resident memberAvailable.resident equalId
      exact .step (by simpa [semanticChildren, ← equal] using included) .here

/-- An all-ordinary union contains every source operand's complete edge list. -/
theorem ordinaryEdges_contains (values : List (Value Symbol Guard)) (edges : List (EdgeValue Symbol Guard))
    (found : ordinaryEdges values = some edges) (value : Value Symbol Guard) (present : value ∈ values) :
    (∃ entry own depth free, value = .node entry own depth free ∧ ∀ edge ∈ own, edge ∈ edges) := by
  induction values generalizing edges with
  | nil => simp at present
  | cons first rest ih =>
      cases first <;> simp only [ordinaryEdges] at found <;> try contradiction
      case node entry own depth free =>
        cases tail : ordinaryEdges rest with
        | none => simp [tail] at found
        | some later =>
            have same : own ++ later = edges := by simpa [tail] using found
            subst edges
            rcases List.mem_cons.mp present with rfl | member
            · exact ⟨entry, own, depth, free, rfl, fun edge included => List.mem_append_left later included⟩
            · obtain ⟨entry, own, depth, free, equal, included⟩ := ih later tail member
              exact ⟨entry, own, depth, free, equal, fun edge member => List.mem_append_right _ (included edge member)⟩

/-- Every flattened operand retains its recursive descendants through the
actual singleton, ordinary-merge, and interned-union branches. -/
theorem flattened_retains_mu [DecidableEq (EdgeKey Symbol Guard)]
    (state : State Symbol Guard) (coherent : Coherent state) (cached : Cached state)
    (linked : Linked state) (live : Live state)
    (values : List (Value Symbol Guard)) (available : ∀ value ∈ values, Available state value)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (source : Value Symbol Guard) (member : source ∈ values.flatMap unionMembers)
    (retained : Retains (.mu entry body depth ordinary) source) :
    Retains (.mu entry body depth ordinary) (run (makeUnion values) state).1 := by
  have allAvailable : ∀ value ∈ values.flatMap unionMembers, Available state value := by
    intro value present
    obtain ⟨original, included, selected⟩ := List.mem_flatMap.mp present
    exact unionMembers_available original (available original included) value selected
  have sourceAvailable := allAvailable source member
  have present := distinctNodes_retains state coherent _ (fun value member => (allAvailable value member).resident) source member
  have normalizedAvailable : ∀ value ∈ distinctNodes (values.flatMap unionMembers), Available state value :=
    fun value member => allAvailable value (distinctNodes_member _ value member)
  cases normalized : distinctNodes (values.flatMap unionMembers) with
  | nil => simp [normalized] at present
  | cons first rest =>
      cases rest with
      | nil =>
          have same : source = first := by simpa [normalized] using present
          simpa only [makeUnion, normalized, run, ← same] using retained
      | cons second tail =>
          have sourceMember : source ∈ first :: second :: tail := by simpa [normalized] using present
          have memberAvailable : ∀ value ∈ first :: second :: tail, Available state value := by
            simpa [normalized] using normalizedAvailable
          cases ordinaryResult : ordinaryEdges (first :: second :: tail) with
          | some edges =>
              obtain ⟨sourceEntry, sourceEdges, sourceDepth, sourceFree, sourceEq, included⟩ :=
                ordinaryEdges_contains _ edges ordinaryResult source sourceMember
              subst source
              cases retained with
              | step childMember childRetained =>
                  obtain ⟨edge, edgeMember, childInEdge⟩ := List.mem_flatMap.mp childMember
                  have edgeResident := ordinaryEdges_resident _ edges state linked
                    (fun value member => (memberAvailable value member).resident) ordinaryResult
                  have edgeLive := resident_live state live _ sourceAvailable.resident edge edgeMember
                  have result := makeNode_retains edges state coherent linked edgeResident edge
                    (included edge edgeMember) edgeLive _ _ childInEdge childRetained
                  simpa only [makeUnion, normalized, ordinaryResult] using result
          | none =>
              let members := first :: second :: tail
              let key := NodeKey.union (members.map Value.referenceOf)
              let identify := fun entry => Value.union entry members (maximumDepth members) (childFree members)
              let result := (nodeStep key identify state).1
              let after := (nodeStep key identify state).2
              have built := makeUnion_available values state coherent cached available
              have outputAvailable : Available after result := by simpa only [makeUnion, normalized, ordinaryResult, run] using built.2.2
              have afterCoherent : Coherent after := by simpa only [makeUnion, normalized, ordinaryResult, run] using built.1
              have sourceAfter : Available after source := by
                simpa only [makeUnion, normalized, ordinaryResult, run] using
                  available_after_run (makeUnion values) state coherent.valid sourceAvailable
              obtain ⟨actual, fields⟩ := InternedGateRank.requested_fields key identify state coherent
                (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩)
              have path := union_readback_member after afterCoherent members actual result source fields
                outputAvailable sourceAfter sourceMember
              have complete := retains_trans path retained
              simpa only [makeUnion, normalized, ordinaryResult, run] using complete

/-- Every original source operand retains its recursive descendants after
root flattening and complete source union reconstruction. -/
theorem makeUnion_retains_mu [DecidableEq (EdgeKey Symbol Guard)]
    (state : State Symbol Guard) (coherent : Coherent state) (cached : Cached state)
    (linked : Linked state) (live : Live state)
    (values : List (Value Symbol Guard)) (available : ∀ value ∈ values, Available state value)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (source : Value Symbol Guard) (member : source ∈ values)
    (retained : Retains (.mu entry body depth ordinary) source) :
    Retains (.mu entry body depth ordinary) (run (makeUnion values) state).1 := by
  obtain ⟨inner, included, path⟩ := flatten_retains entry body depth ordinary source retained
  exact flattened_retains_mu state coherent cached linked live values available entry body depth ordinary
    inner (List.mem_flatMap.mpr ⟨source, member, included⟩) path

/-- Current source self-reference removal preserves every actual Mu
descendant, including descendants below an all-ordinary union merge. -/
theorem filter_retains_mu [DecidableEq (EdgeKey Symbol Guard)]
    (state : State Symbol Guard) (coherent : Coherent state) (cached : Cached state)
    (linked : Linked state) (live : Live state) (name : Reference) (value : Value Symbol Guard)
    (available : Available state value) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (retained : Retains (.mu entry body depth ordinary) value) :
    Retains (.mu entry body depth ordinary) (run (withoutSelfReference name value) state).1 := by
  cases value <;> simp only [withoutSelfReference, run] <;> try exact retained
  case union source members level free =>
    split
    · cases retained with
      | step member path =>
          apply makeUnion_retains_mu state coherent cached linked live _
            (fun value included => available.children value (List.mem_filter.mp included).1)
            entry body depth ordinary _ ?_ path
          apply (withoutSelfReference_members name members _).mpr
          refine ⟨member, ?_⟩
          intro same
          exact InternedBinderRetention.no_mu_under_reference entry body depth ordinary name (same ▸ path)
    · exact retained

end MicroCFTA.InternedUnionDescendants
