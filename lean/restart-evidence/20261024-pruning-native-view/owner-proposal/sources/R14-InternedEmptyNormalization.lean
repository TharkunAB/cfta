import MicroCFTA.InternedNonemptyRecords
import MicroCFTA.InternedFreeOccurrenceNode

/-!
# Exact empty-result cases of actual ordinary and union construction

Canonical ordinary readback is empty precisely when every requested edge
has an empty child. A source union is empty precisely when every operand
is empty. The union theorem uses derived stored cardinality and live-edge
invariants, including complete cache hits.
-/
namespace MicroCFTA.InternedEmptyNormalization
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedEdgeResidency InternedLiveEdges InternedUnionRetention InternedUnionDescendants
open InternedNonemptyRecords
open InternedBinderProtocol (Reference NodeKey NodeRef)

/-- Only the actual EmptyNode constructor has the empty source identity. -/
theorem reference_empty (value : Value Symbol Guard) : value.referenceOf = .empty ↔ value = .empty := by
  cases value <;> simp [Value.referenceOf]

/-- Actual node normalization is empty exactly when all original edges contain an empty child. -/
theorem makeNode_empty_iff [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (linked : Linked state)
    (resident : ∀ edge ∈ edges, EdgeResident state edge) :
    (run (makeNode edges) state).1.referenceOf = .empty ↔
      ∀ edge ∈ edges, edge.children.any (fun child => child.referenceOf == .empty) = true := by
  have selected : ∀ edge ∈ canonicalEdges (surviving edges), EdgeResident state edge :=
    fun edge member => resident edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  have shape : (run (makeNode edges) state).1.referenceOf = .empty ↔ canonicalEdges (surviving edges) = [] := by
    unfold makeNode
    dsimp only
    split
    · rename_i same
      simp [run, Value.referenceOf, same]
    · rename_i first rest same
      obtain ⟨entry, actual⟩ := identifyNode_readback (first :: rest) state coherent linked (by simpa [same] using selected)
      simp only [run, actual, identifyNode, Value.referenceOf]
      simp [same]
  rw [shape]
  constructor
  · intro empty edge member
    cases alive : edge.children.any (fun child => child.referenceOf == .empty) with
    | true => rfl
    | false =>
        have survives : edge ∈ surviving edges := by simp [surviving, member, alive]
        have retained := canonicalEdges_retains state coherent _ edge
          (fun value included => resident value (List.mem_filter.mp included).1) survives
        exact False.elim (List.not_mem_nil (empty ▸ retained))
  · intro allEmpty
    have none : surviving edges = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro edge member
      simp [allEmpty edge member]
    rw [none]
    simp [canonicalEdges, EnumerationBuilderCaches.canonicalIds]

/-- Flattening an available proper nonempty operand retains a nonempty member. -/
theorem flatten_nonempty (value : Value Symbol Guard) (proper : StoredNonempty value)
    (nonempty : value.referenceOf ≠ .empty) :
    ∃ member ∈ unionMembers value, member.referenceOf ≠ .empty := by
  cases value with
  | empty => simp [Value.referenceOf] at nonempty
  | reference | node | mu => exact ⟨_, by simp [unionMembers], nonempty⟩
  | union entry members depth free => exact union_has_nonempty entry members depth free proper

/-- A complete union-key record cannot have the EmptyNode identity. -/
theorem union_fields_nonempty (members : List NodeRef) (entry : Interned NodeKey) (value : Value Symbol Guard)
    (fields : NodeFields (.union members) entry value) : value.referenceOf ≠ .empty := by
  cases value <;> simp_all [NodeFields, muKey, Value.referenceOf]

/-- Source union normalization retains a nonempty operand even when it merges ordinary edges. -/
theorem makeUnion_nonempty [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (linked : Linked state)
    (live : Live state) (proper : NonemptyRecords state) (available : ∀ value ∈ values, Available state value)
    (source : Value Symbol Guard) (member : source ∈ values) (nonempty : source.referenceOf ≠ .empty) :
    (run (makeUnion values) state).1.referenceOf ≠ .empty := by
  obtain ⟨selected, included, selectedNonempty⟩ :=
    flatten_nonempty source (resident_nonempty state proper source (available source member).resident) nonempty
  have allAvailable : ∀ value ∈ values.flatMap unionMembers, Available state value := by
    intro value present
    obtain ⟨outer, outerMember, inner⟩ := List.mem_flatMap.mp present
    exact unionMembers_available outer (available outer outerMember) value inner
  have flatMember : selected ∈ values.flatMap unionMembers := List.mem_flatMap.mpr ⟨source, member, included⟩
  have selectedAvailable := allAvailable selected flatMember
  have retained := distinctNodes_retains state coherent _ (fun value member => (allAvailable value member).resident) selected flatMember
  have normalizedAvailable : ∀ value ∈ distinctNodes (values.flatMap unionMembers), Available state value :=
    fun value member => allAvailable value (distinctNodes_member _ value member)
  cases normalized : distinctNodes (values.flatMap unionMembers) with
  | nil => simp [normalized] at retained
  | cons first rest =>
      cases rest with
      | nil =>
          have same : selected = first := by simpa [normalized] using retained
          simpa only [makeUnion, normalized, run, ← same] using selectedNonempty
      | cons second tail =>
          have sourceMember : selected ∈ first :: second :: tail := by simpa [normalized] using retained
          have memberAvailable : ∀ value ∈ first :: second :: tail, Available state value := by simpa [normalized] using normalizedAvailable
          cases ordinaryResult : ordinaryEdges (first :: second :: tail) with
          | some edges =>
              obtain ⟨sourceEntry, sourceEdges, sourceDepth, sourceFree, same, edgesIncluded⟩ :=
                ordinaryEdges_contains _ edges ordinaryResult selected sourceMember
              subst selected
              have hasEdges : sourceEdges ≠ [] := resident_nonempty state proper _ selectedAvailable.resident
              obtain ⟨edge, edgeMember⟩ := List.exists_mem_of_ne_nil sourceEdges hasEdges
              have edgeLive := resident_live state live _ selectedAvailable.resident edge edgeMember
              have resident := ordinaryEdges_resident _ edges state linked (fun value member => (memberAvailable value member).resident) ordinaryResult
              intro empty
              have allEmpty := (makeNode_empty_iff edges state coherent linked resident).mp
                (by simpa only [makeUnion, normalized, ordinaryResult] using empty)
              have contradict := allEmpty edge (edgesIncluded edge edgeMember)
              simp [edgeLive] at contradict
          | none =>
              let members := first :: second :: tail
              let key := NodeKey.union (members.map Value.referenceOf)
              let identify := fun entry => Value.union entry members (maximumDepth members) (childFree members)
              obtain ⟨actual, fields⟩ := InternedGateRank.requested_fields key identify state coherent
                (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩)
              simpa only [makeUnion, normalized, ordinaryResult, run] using union_fields_nonempty _ actual _ fields

/-- Actual source union is empty exactly when all its available operands are EmptyNode. -/
theorem makeUnion_empty_iff [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (linked : Linked state)
    (live : Live state) (proper : NonemptyRecords state) (available : ∀ value ∈ values, Available state value) :
    (run (makeUnion values) state).1.referenceOf = .empty ↔ ∀ value ∈ values, value.referenceOf = .empty := by
  constructor
  · intro empty value member
    by_cases nonempty : value.referenceOf = .empty
    · exact nonempty
    · exact False.elim (makeUnion_nonempty values state coherent linked live proper available value member nonempty empty)
  · intro allEmpty
    have flattened : values.flatMap unionMembers = [] := by
      apply List.flatMap_eq_nil_iff.mpr
      intro value member
      have empty := (reference_empty value).mp (allEmpty value member)
      simp [empty, unionMembers]
    simp [makeUnion, flattened, distinctNodes, run, Value.referenceOf]

end MicroCFTA.InternedEmptyNormalization
