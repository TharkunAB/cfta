import MicroCFTA.InternedUnionNormalForm

/-!
# Cached Mu-depth bounds through actual source normalization

Ordinary edge deletion cannot increase cached depth. Union flattening,
deduplication, merging, and canonical readback preserve an input depth
bound. These are normalization bounds, not an unfolding termination rank.
-/
namespace MicroCFTA.InternedNormalizationDepth
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedEdgeResidency InternedUnionSeparation InternedUnionDescendants
open InternedNormalizationFree InternedGateRank
open InternedBinderProtocol (NodeKey Reference)

/-- An actual source ordinary result inherits the bound of its surviving ordered children. -/
theorem makeNode_depth_le [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (linked : Linked state)
    (resident : ∀ edge ∈ edges, EdgeResident state edge) (bound : Nat)
    (depth : ∀ child ∈ edges.flatMap EdgeValue.children, child.depth ≤ bound) :
    (run (makeNode edges) state).1.depth ≤ bound := by
  have selected : ∀ edge ∈ canonicalEdges (surviving edges), EdgeResident state edge :=
    fun edge member => resident edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  have selectedDepth : ∀ child ∈ (canonicalEdges (surviving edges)).flatMap EdgeValue.children, child.depth ≤ bound := by
    intro child member
    obtain ⟨edge, included, found⟩ := List.mem_flatMap.mp member
    exact depth child (List.mem_flatMap.mpr ⟨edge, (List.mem_filter.mp (canonicalEdges_member _ edge included)).1, found⟩)
  unfold makeNode
  dsimp only
  split
  · exact Nat.zero_le bound
  · rename_i first rest same
    obtain ⟨entry, exactResult⟩ := identifyNode_readback (first :: rest) state coherent linked
      (by simpa [same] using selected)
    simp only [run, exactResult, identifyNode, Value.depth]
    exact (maximumDepth_exact _ bound).mpr (by simpa [same] using selectedDepth)

/-- Complete canonical union readback uses the depths of its exact immutable input members. -/
theorem union_readback_depth_le (state : State Symbol Guard) (coherent : Coherent state)
    (members : List (Value Symbol Guard)) (entry : Interned NodeKey) (value : Value Symbol Guard)
    (fields : NodeFields (.union (members.map Value.referenceOf)) entry value)
    (output : Available state value) (inputs : ∀ member ∈ members, Available state member)
    (bound : Nat) (depth : ∀ member ∈ members, member.depth ≤ bound) : value.depth ≤ bound := by
  cases value with
  | empty | reference | node | mu => simp [NodeFields, muKey] at fields
  | union actual actualMembers level free =>
      have equal := value_lists_equal state coherent members actualMembers
        (fun value member => (inputs value member).resident)
        (fun value member => (output.children value member).resident)
        (NodeKey.union.inj fields.2.1)
      simp only [Value.depth, fields.2.2.1, ← equal]
      exact (maximumDepth_exact _ bound).mpr depth

/-- Every source union branch preserves a common bound on the actual cached Mu depths. -/
theorem makeUnion_depth_le [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (cached : Cached state) (linked : Linked state)
    (available : ∀ value ∈ values, Available state value) (bound : Nat)
    (depth : ∀ value ∈ values, value.depth ≤ bound) : (run (makeUnion values) state).1.depth ≤ bound := by
  have allAvailable : ∀ value ∈ distinctNodes (values.flatMap unionMembers), Available state value := by
    intro value member
    obtain ⟨original, included, selected⟩ := List.mem_flatMap.mp (distinctNodes_member _ value member)
    exact unionMembers_available original (available original included) value selected
  have allDepth : ∀ value ∈ distinctNodes (values.flatMap unionMembers), value.depth ≤ bound := by
    intro value member
    obtain ⟨original, included, selected⟩ := List.mem_flatMap.mp (distinctNodes_member _ value member)
    cases original with
    | empty => simp [unionMembers] at selected
    | union entry members level free =>
        exact Nat.le_trans (child_depth state coherent _ value (available _ included) selected) (depth _ included)
    | reference | node | mu =>
        simp only [unionMembers, List.mem_singleton] at selected
        subst value
        exact depth _ included
  cases normalized : distinctNodes (values.flatMap unionMembers) with
  | nil => simp [makeUnion, normalized, run, Value.depth]
  | cons first rest =>
      cases rest with
      | nil => simpa [makeUnion, normalized, run] using allDepth first (by simp [normalized])
      | cons second tail =>
          have membersAvailable : ∀ value ∈ first :: second :: tail, Available state value := by simpa [normalized] using allAvailable
          have membersDepth : ∀ value ∈ first :: second :: tail, value.depth ≤ bound := by simpa [normalized] using allDepth
          cases ordinary : ordinaryEdges (first :: second :: tail) with
          | some edges =>
              have resident := ordinaryEdges_resident _ edges state linked
                (fun value member => (membersAvailable value member).resident) ordinary
              have childrenDepth : ∀ child ∈ edges.flatMap EdgeValue.children, child.depth ≤ bound := by
                have edgeSource : ∀ (members : List (Value Symbol Guard)) edges,
                    ordinaryEdges members = some edges → ∀ edge ∈ edges,
                    ∃ value ∈ members, edge ∈ InternedEdgeResidency.nodeEdges value := by
                  intro members
                  induction members with
                  | nil => intro edges found; cases found; simp
                  | cons value members ih =>
                      intro edges found edge member
                      cases value <;> simp only [ordinaryEdges] at found <;> try contradiction
                      case node entry own level free =>
                        cases remaining : ordinaryEdges members with
                        | none => simp [remaining] at found
                        | some later =>
                            have same : own ++ later = edges := by simpa [remaining] using found
                            subst edges
                            rcases List.mem_append.mp member with left | right
                            · exact ⟨.node entry own level free, by simp, left⟩
                            · obtain ⟨source, included, selected⟩ := ih later remaining edge right
                              exact ⟨source, by simp [included], selected⟩
                intro child member
                obtain ⟨edge, included, selected⟩ := List.mem_flatMap.mp member
                obtain ⟨source, sourceMember, edgeMember⟩ := edgeSource _ edges ordinary edge included
                have semantic : child ∈ semanticChildren source := by
                  cases source <;> simp only [nodeEdges] at edgeMember <;> try contradiction
                  exact List.mem_flatMap.mpr ⟨edge, edgeMember, selected⟩
                exact Nat.le_trans (child_depth state coherent source child (membersAvailable source sourceMember) semantic)
                  (membersDepth source sourceMember)
              simpa only [makeUnion, normalized, ordinary] using makeNode_depth_le edges state coherent linked resident bound childrenDepth
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
                union_readback_depth_le after later members actual result fields output inputs bound membersDepth

/-- Actual root self-reference removal never increases cached maximum Mu depth. -/
theorem filter_depth_le [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (value : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (cached : Cached state) (linked : Linked state)
    (available : Available state value) : (run (withoutSelfReference name value) state).1.depth ≤ value.depth := by
  cases value <;> simp only [withoutSelfReference, run] <;> try exact Nat.le_refl _
  case union entry members level free =>
    split
    · exact makeUnion_depth_le _ state coherent cached linked
        (fun value member => available.children value (List.mem_filter.mp member).1) _
        (fun value member => child_depth state coherent _ value available (List.mem_filter.mp member).1)
    · exact Nat.le_refl _

end MicroCFTA.InternedNormalizationDepth
