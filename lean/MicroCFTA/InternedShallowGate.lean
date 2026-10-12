import MicroCFTA.InternedNormalizationDepth

/-!
# Actual shallow Mu unfolding after source self-union filtering

Cached body depth zero excludes open nested Mu preparation. Source flat
unions and root filtering derive the constructor guard. The resulting
prepared substitution has a strict head-rank decrease.
-/
namespace MicroCFTA.InternedShallowGate
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedTemplateProvenance InternedNormalizationFree InternedNormalizationDepth
open InternedUnionNormalForm InternedPreparedSubstitution InternedGateRank
open InternedBinderProtocol (NodeKey Reference)

/-- Root flattening preserves the selected-name guard. -/
theorem guarded_flatten {value : Value Symbol Guard} (guarded : GuardedValue name value) :
    ∀ member ∈ unionMembers value, GuardedValue name member := by
  cases guarded with
  | empty => simp [unionMembers]
  | reference other different => simpa [unionMembers] using (GuardedValue.reference other different : GuardedValue name (.reference other : Value Symbol Guard))
  | node entry edges depth free => simpa [unionMembers] using GuardedValue.node (name := name) entry edges depth free
  | union entry members depth free children => exact children

/-- Any ordinary result guards every reference introduced below its root. -/
theorem makeNode_guarded [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) : GuardedValue name (run (makeNode edges) state).1 := by
  unfold makeNode
  dsimp only
  split
  · exact .empty
  · rename_i first rest _
    simp only [run]
    obtain ⟨entry, fields⟩ := requested_fields
      (.node ((first :: rest).map (fun edge => edge.entry.identity)))
      (identifyNode (first :: rest)) state coherent (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩)
    generalize found : (nodeStep _ _ state).1 = value at fields ⊢
    cases value <;> simp [NodeFields, muKey] at fields <;> try contradiction
    exact .node _ _ _ _

/-- Complete cached union readback contains the requested immutable member records. -/
theorem union_readback_guarded (name : Reference) (state : State Symbol Guard) (coherent : Coherent state)
    (members : List (Value Symbol Guard)) (entry : Interned NodeKey) (value : Value Symbol Guard)
    (fields : NodeFields (.union (members.map Value.referenceOf)) entry value)
    (output : Available state value) (inputs : ∀ member ∈ members, Available state member)
    (guarded : ∀ member ∈ members, GuardedValue name member) : GuardedValue name value := by
  cases value with
  | empty | reference | node | mu => simp [NodeFields, muKey] at fields
  | union actual actualMembers depth free =>
      have equal := value_lists_equal state coherent members actualMembers
        (fun value member => (inputs value member).resident)
        (fun value member => (output.children value member).resident)
        (NodeKey.union.inj fields.2.1)
      exact .union _ _ _ _ (equal ▸ guarded)

/-- Every source union branch preserves the input constructor guards,
including singleton collapse and canonical cache hits. -/
theorem makeUnion_guarded [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (cached : Cached state)
    (available : ∀ value ∈ values, Available state value)
    (guarded : ∀ value ∈ values, GuardedValue name value) : GuardedValue name (run (makeUnion values) state).1 := by
  have allAvailable : ∀ value ∈ distinctNodes (values.flatMap unionMembers), Available state value := by
    intro value member
    obtain ⟨original, included, selected⟩ := List.mem_flatMap.mp (distinctNodes_member _ value member)
    exact unionMembers_available original (available original included) value selected
  have allGuarded : ∀ value ∈ distinctNodes (values.flatMap unionMembers), GuardedValue name value := by
    intro value member
    obtain ⟨original, included, selected⟩ := List.mem_flatMap.mp (distinctNodes_member _ value member)
    exact guarded_flatten (guarded original included) value selected
  cases normalized : distinctNodes (values.flatMap unionMembers) with
  | nil => simpa [makeUnion, normalized, run] using (GuardedValue.empty : GuardedValue name (.empty : Value Symbol Guard))
  | cons first rest =>
      cases rest with
      | nil => simpa [makeUnion, normalized, run] using allGuarded first (by simp [normalized])
      | cons second tail =>
          have membersAvailable : ∀ value ∈ first :: second :: tail, Available state value := by simpa [normalized] using allAvailable
          have membersGuarded : ∀ value ∈ first :: second :: tail, GuardedValue name value := by simpa [normalized] using allGuarded
          cases ordinary : ordinaryEdges (first :: second :: tail) with
          | some edges => simpa only [makeUnion, normalized, ordinary] using makeNode_guarded name edges state coherent
          | none =>
              let members := first :: second :: tail
              let key := NodeKey.union (members.map Value.referenceOf)
              let identify := fun entry => Value.union entry members (maximumDepth members) (childFree members)
              let after := (nodeStep key identify state).2
              let result := (nodeStep key identify state).1
              have built := makeUnion_available values state coherent cached available
              have output : Available after result := by simpa only [makeUnion, normalized, ordinary, run] using built.2.2
              have later : Coherent after := by simpa only [makeUnion, normalized, ordinary, run] using built.1
              have inputs : ∀ value ∈ members, Available after value := by
                intro value member
                simpa only [makeUnion, normalized, ordinary, run] using
                  available_after_run (makeUnion values) state coherent.valid (membersAvailable value member)
              obtain ⟨actual, fields⟩ := requested_fields key identify state coherent (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩)
              simpa only [makeUnion, normalized, ordinary, run] using
                union_readback_guarded name after later members actual result fields output inputs membersGuarded

/-- A nonunion depth-zero operand can fail the guard only at the selected bare reference. -/
theorem atomic_guarded (name : Reference) (value : Value Symbol Guard) (atomic : Atomic value)
    (zero : value.depth = 0) (different : value ≠ .reference name) : GuardedValue name value := by
  cases value with
  | empty => exact .empty
  | reference other => exact .reference other (fun same => different (congrArg Value.reference same))
  | node entry edges depth free => exact .node entry edges depth free
  | union => contradiction
  | mu => simp [Value.depth] at zero

/-- Source normalized shallow bodies derive the guard after the actual self filter. -/
theorem filter_guarded [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (body : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (cached : Cached state) (flat : Flat state)
    (available : Available state body) (zero : body.depth = 0) (different : body ≠ .reference name) :
    GuardedValue name (run (withoutSelfReference name body) state).1 := by
  cases body with
  | empty => exact .empty
  | reference other => exact .reference other (fun same => different (congrArg Value.reference same))
  | node entry edges depth free => exact .node entry edges depth free
  | mu => simp [Value.depth] at zero
  | union entry members depth free =>
      have membersAtomic := resident_flat state flat (.union entry members depth free) available.resident
      have membersZero : ∀ value ∈ members, value.depth = 0 := by
        intro value member
        exact Nat.eq_zero_of_le_zero (zero ▸ InternedUnionSeparation.child_depth state coherent _ value available member)
      simp only [withoutSelfReference]
      split
      · apply makeUnion_guarded name _ state coherent cached
          (fun value member => available.children value (List.mem_filter.mp member).1)
        intro value member
        have original := (withoutSelfReference_members name members value).mp member
        exact atomic_guarded name value (membersAtomic value original.1) (membersZero value original.1) original.2
      · rename_i absent
        apply GuardedValue.union
        intro value member
        apply atomic_guarded name value (membersAtomic value member) (membersZero value member)
        intro same
        have present : members.any (fun member => member.referenceOf == .ref name) = true :=
          List.any_eq_true.mpr ⟨value, member, by simp [same, Value.referenceOf]⟩
        exact absent present

/-- A successful source filter on a shallow open body derives preparation
success and strict head-rank decrease. The source union shape is derived
from the current tables, rather than supplied as an output guard. -/
theorem normalized_unfold_decreases [DecidableEq (EdgeKey Symbol Guard)]
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (cached : Cached state) (linked : InternedEdgeResidency.Linked state)
    (flat : Flat state) (available : Available state body) (zero : body.depth = 0)
    (opened : (Value.mu entry body depth ordinary).free ≠ [])
    (replacement : Value Symbol Guard)
    (replacementAvailable : Available (run (withoutSelfReference (.interned entry.identity) body) state).2 replacement) :
    let filtered := run (withoutSelfReference (.interned entry.identity) body) state
    ∃ template, prepare (.interned entry.identity) filtered.1 = some template ∧
      headRank (run (compile template replacement) filtered.2).1 <
        headRank (.mu entry filtered.1 depth ordinary) := by
  have different : body ≠ .reference (.interned entry.identity) := by
    intro same
    simp [same, Value.free] at opened
  have checked := withoutSelfReference_available (.interned entry.identity) body state coherent cached available
  have outputZero := Nat.eq_zero_of_le_zero (zero ▸ filter_depth_le (.interned entry.identity) body state coherent cached linked available)
  have guarded := filter_guarded (.interned entry.identity) body state coherent cached flat available zero different
  obtain ⟨template, prepared⟩ := prepare_zero (.interned entry.identity) _ _ checked.1 checked.2.2 outputZero
  refine ⟨template, prepared, ?_⟩
  rw [prepared_rank (.interned entry.identity) _ replacement template _ checked.1 checked.2.1
    checked.2.2 replacementAvailable prepared guarded]
  simp [headRank]

end MicroCFTA.InternedShallowGate
