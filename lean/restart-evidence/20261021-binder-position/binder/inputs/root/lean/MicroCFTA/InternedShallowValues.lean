import MicroCFTA.InternedShallowGateRank
import MicroCFTA.InternedErasedEdgeReplay

/-!
# Shallow reachable values in arbitrary coherent source caches

The property belongs to the actual queried value, rather than every record
in the global cache. Coherent canonical readback preserves exact children.
Unrelated deeper Mu records therefore do not affect the shallow fragment.
-/
namespace MicroCFTA.InternedShallowValues
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedEdgeResidency InternedNormalizationFree InternedGateRank
open InternedBinderProtocol (NodeKey)

/-- Every Mu reached through ordinary children or union members has a depth-zero body. -/
inductive ShallowValue {Symbol Guard : Type} : Value Symbol Guard → Prop where
  | empty : ShallowValue .empty
  | reference (name) : ShallowValue (.reference name)
  | node (entry) (edges : List (EdgeValue Symbol Guard)) (depth free) (children : ∀ child ∈ edges.flatMap EdgeValue.children, ShallowValue child) :
      ShallowValue (.node entry edges depth free)
  | union (entry) (members : List (Value Symbol Guard)) (depth free) (children : ∀ child ∈ members, ShallowValue child) :
      ShallowValue (.union entry members depth free)
  | mu (entry) (body depth ordinary : Value Symbol Guard) (zero : body.depth = 0) : ShallowValue (.mu entry body depth ordinary)

/-- A current Mu exposes its actual cached body bound directly. -/
theorem mu_zero (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (shallow : ShallowValue (.mu entry body depth ordinary)) : body.depth = 0 := by cases shallow; assumption

/-- A coherent depth-zero record cannot hide a deeper Mu in its actual children. -/
theorem depth_zero (value : Value Symbol Guard) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Available state value) (zero : value.depth = 0) : ShallowValue value := by
  cases value with
  | empty => exact .empty
  | reference name => exact .reference name
  | mu => simp [Value.depth] at zero
  | node entry edges depth free =>
      apply ShallowValue.node
      intro child member
      apply depth_zero child state coherent (available.children child member)
      exact Nat.eq_zero_of_le_zero (zero ▸ InternedUnionSeparation.child_depth state coherent _ child available member)
  | union entry members depth free =>
      apply ShallowValue.union
      intro child member
      apply depth_zero child state coherent (available.children child member)
      exact Nat.eq_zero_of_le_zero (zero ▸ InternedUnionSeparation.child_depth state coherent _ child available member)
termination_by sizeOf value
decreasing_by
  · obtain ⟨edge, included, inner⟩ := List.mem_flatMap.mp member
    have outerSize := List.sizeOf_lt_of_mem included
    have innerSize := List.sizeOf_lt_of_mem inner
    cases edge
    simp_all only [EdgeValue.children]
    simp_wf
    simp_all only [EdgeValue.mk.sizeOf_spec]
    omega
  · have smaller := List.sizeOf_lt_of_mem member
    simp_wf
    simp_all only [Value.union.sizeOf_spec]
    omega

/-- Source union flattening preserves the reachable-value restriction. -/
theorem flatten {value : Value Symbol Guard} (shallow : ShallowValue value) :
    ∀ member ∈ unionMembers value, ShallowValue member := by
  cases shallow with
  | empty => simp [unionMembers]
  | reference name => simpa [unionMembers] using ShallowValue.reference (Symbol := Symbol) (Guard := Guard) name
  | node entry edges depth free children => simpa [unionMembers] using ShallowValue.node entry edges depth free children
  | mu entry body depth ordinary zero => simpa [unionMembers] using ShallowValue.mu entry body depth ordinary zero
  | union entry members depth free children => exact children

/-- Actual canonical edge readback retains the complete requested child list. -/
theorem makeEdge_children [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (constraint : Guard)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard) (coherent : Coherent state) (cached : Cached state)
    (available : ∀ value ∈ values, Available state value) : (run (makeEdge symbol constraint values) state).1.children = values := by
  have built := makeEdge_available symbol constraint values state coherent cached available
  apply value_lists_equal (run (makeEdge symbol constraint values) state).2 built.1 _ values
    (fun value member => (built.2.2 value member).resident)
    (fun value member => (available_after_run (makeEdge symbol constraint values) state coherent.valid (available value member)).resident)
  exact InternedErasedEdgeReplay.makeEdge_references symbol constraint values state coherent

/-- Actual ordinary node normalization retains only the supplied shallow children. -/
theorem makeNode_shallow [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (linked : Linked state)
    (resident : ∀ edge ∈ edges, EdgeResident state edge)
    (shallow : ∀ child ∈ edges.flatMap EdgeValue.children, ShallowValue child) :
    ShallowValue (run (makeNode edges) state).1 := by
  have selected : ∀ edge ∈ canonicalEdges (surviving edges), EdgeResident state edge :=
    fun edge member => resident edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  have selectedShallow : ∀ child ∈ (canonicalEdges (surviving edges)).flatMap EdgeValue.children, ShallowValue child := by
    intro child member
    obtain ⟨edge, included, inner⟩ := List.mem_flatMap.mp member
    exact shallow child (List.mem_flatMap.mpr ⟨edge, (List.mem_filter.mp (canonicalEdges_member _ edge included)).1, inner⟩)
  unfold makeNode
  dsimp only
  split
  · exact .empty
  · rename_i first rest same
    obtain ⟨entry, exactResult⟩ := identifyNode_readback (first :: rest) state coherent linked (by simpa [same] using selected)
    simp only [run, exactResult, identifyNode]
    exact .node _ _ _ _ (by simpa [same] using selectedShallow)

/-- An all-ordinary source merge preserves the input reachable-value restriction. -/
theorem ordinaryEdges_shallow (values : List (Value Symbol Guard)) (edges : List (EdgeValue Symbol Guard))
    (shallow : ∀ value ∈ values, ShallowValue value) (found : ordinaryEdges values = some edges) :
    ∀ child ∈ edges.flatMap EdgeValue.children, ShallowValue child := by
  induction values generalizing edges with
  | nil => cases found; simp
  | cons first rest ih =>
      cases first <;> simp only [ordinaryEdges] at found <;> try contradiction
      case node entry own depth free =>
        cases tail : ordinaryEdges rest with
        | none => simp [tail] at found
        | some later =>
            have same : own ++ later = edges := by simpa [tail] using found
            subst edges
            have head : ∀ child ∈ own.flatMap EdgeValue.children, ShallowValue child := by
              have selected := shallow (.node entry own depth free) (by simp)
              cases selected
              assumption
            have restShallow := ih later (fun value member => shallow value (by simp [member])) tail
            intro child member
            simp only [List.flatMap_append, List.mem_append] at member
            exact member.elim (head child) (restShallow child)

/-- Source union reconstruction preserves reachable shallowness through every branch and cache hit. -/
theorem makeUnion_shallow [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (cached : Cached state) (linked : Linked state)
    (available : ∀ value ∈ values, Available state value) (shallow : ∀ value ∈ values, ShallowValue value) :
    ShallowValue (run (makeUnion values) state).1 := by
  have allAvailable : ∀ value ∈ distinctNodes (values.flatMap unionMembers), Available state value := by
    intro value member
    obtain ⟨original, included, selected⟩ := List.mem_flatMap.mp (distinctNodes_member _ value member)
    exact unionMembers_available original (available original included) value selected
  have allShallow : ∀ value ∈ distinctNodes (values.flatMap unionMembers), ShallowValue value := by
    intro value member
    obtain ⟨original, included, selected⟩ := List.mem_flatMap.mp (distinctNodes_member _ value member)
    exact flatten (shallow original included) value selected
  cases normalized : distinctNodes (values.flatMap unionMembers) with
  | nil => simpa [makeUnion, normalized, run] using ShallowValue.empty (Symbol := Symbol) (Guard := Guard)
  | cons first rest =>
      cases rest with
      | nil => simpa [makeUnion, normalized, run] using allShallow first (by simp [normalized])
      | cons second tail =>
          have inputs : ∀ value ∈ first :: second :: tail, Available state value := by simpa [normalized] using allAvailable
          have safe : ∀ value ∈ first :: second :: tail, ShallowValue value := by simpa [normalized] using allShallow
          cases ordinary : ordinaryEdges (first :: second :: tail) with
          | some edges =>
              have resident := ordinaryEdges_resident _ edges state linked (fun value member => (inputs value member).resident) ordinary
              simpa only [makeUnion, normalized, ordinary] using makeNode_shallow edges state coherent linked resident
                (ordinaryEdges_shallow _ edges safe ordinary)
          | none =>
              let members := first :: second :: tail
              let key := NodeKey.union (members.map Value.referenceOf)
              let identify := fun entry => Value.union entry members (maximumDepth members) (childFree members)
              let after := (nodeStep key identify state).2
              let result := (nodeStep key identify state).1
              have built := makeUnion_available values state coherent cached available
              have output : Available after result := by simpa only [makeUnion, normalized, ordinary, run] using built.2.2
              have later : Coherent after := by simpa only [makeUnion, normalized, ordinary, run] using built.1
              have laterInputs : ∀ value ∈ members, Available after value := by
                intro value member
                simpa only [makeUnion, normalized, ordinary, run] using
                  available_after_run (makeUnion values) state coherent.valid (inputs value member)
              obtain ⟨actual, fields⟩ := requested_fields key identify state coherent (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩)
              have resultShallow : ShallowValue result := by
                change NodeFields key actual result at fields
                generalize resultEq : result = value at fields output ⊢
                cases value with
                | empty | reference | node | mu => simp [NodeFields, muKey, key] at fields
                | union entry actualMembers level free =>
                    have equal := value_lists_equal after later members actualMembers
                      (fun value member => (laterInputs value member).resident)
                      (fun value member => (output.children value member).resident)
                      (NodeKey.union.inj fields.2.1)
                    exact .union _ _ _ _ (equal ▸ safe)
              simpa only [makeUnion, normalized, ordinary, run] using resultShallow

end MicroCFTA.InternedShallowValues
