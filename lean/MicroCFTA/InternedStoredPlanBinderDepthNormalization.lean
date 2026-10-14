import MicroCFTA.InternedStoredPlanBinderDepthBounds

/-!
# Open stored-plan depth through actual ordinary normalization

Closed records have depth zero. Coherent ordinary nodes and unions have
the maximum open depth of their actual children. Source normalization
preserves an upper bound on this measure, including canonical cache hits.
This module does not assert progress at a recursive constructor.
-/
namespace MicroCFTA.InternedStoredPlanBinderDepth
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNormalizationFree InternedEdgeResidency InternedLiveEdges
open InternedUnionSeparation InternedUnionDescendants InternedGateRank
open InternedFreshProbeKeys
open InternedBinderProtocol (NodeKey Reference)

/-- The ordered maximum is bounded exactly when every actual member is bounded. -/
theorem many_le_iff (values : List (Value Symbol Guard)) (bound : Nat) :
    manyDepth values ≤ bound ↔ ∀ value ∈ values, valueDepth value ≤ bound := by
  induction values with
  | nil => simp [manyDepth]
  | cons first rest ih => simp [manyDepth, Nat.max_le, ih]

/-- Edge depth is the ordered maximum of the original edge children. -/
theorem edges_eq_many (edges : List (EdgeValue Symbol Guard)) :
    edgesDepth edges = manyDepth (edges.flatMap EdgeValue.children) := by
  have append (first second : List (Value Symbol Guard)) :
      manyDepth (first ++ second) = max (manyDepth first) (manyDepth second) := by
    induction first with
    | nil => simp [manyDepth]
    | cons first rest ih => simp [manyDepth, ih, Nat.max_assoc]
  induction edges with
  | nil => simp [edgesDepth, manyDepth]
  | cons first rest ih => cases first; simp [edgesDepth, List.flatMap_cons, ih, append, EdgeValue.children]

/-- A closed child-free list has no open plan depth. -/
theorem many_zero_of_free (values : List (Value Symbol Guard)) (closed : childFree values = []) :
    manyDepth values = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply (many_le_iff values 0).mpr
  intro value member
  have free : value.free = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro name included
    have present := (childFree_member values name).mpr ⟨value, member, included⟩
    simp [closed] at present
  rw [closed_zero value free]
  exact Nat.le_refl _

/-- A coherent ordinary record has exactly its maximum child open depth. -/
theorem node_depth (entry : Interned NodeKey) (edges : List (EdgeValue Symbol Guard))
    (depth : Nat) (free : List Reference) (state : State Symbol Guard)
    (coherent : Coherent state) (resident : Resident state (.node entry edges depth free)) :
    valueDepth (.node entry edges depth free) = edgesDepth edges := by
  rw [valueDepth.eq_def]
  split
  · rename_i closed
    have exactFree := node_free state coherent entry edges depth free resident
    rw [edges_eq_many, many_zero_of_free _ (exactFree.symm.trans (List.isEmpty_iff.mp closed))]
  · rfl

/-- A coherent union has exactly its maximum member open depth. -/
theorem union_depth (entry : Interned NodeKey) (members : List (Value Symbol Guard))
    (depth : Nat) (free : List Reference) (state : State Symbol Guard)
    (coherent : Coherent state) (resident : Resident state (.union entry members depth free)) :
    valueDepth (.union entry members depth free) = manyDepth members := by
  rw [valueDepth.eq_def]
  split
  · rename_i closed
    have exactFree := union_free state coherent entry members depth free resident
    rw [many_zero_of_free _ (exactFree.symm.trans (List.isEmpty_iff.mp closed))]
  · rfl

/-- Actual ordinary and union children inherit the parent's open-depth bound. -/
theorem ordinary_child_le (value child : Value Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (available : Available state value)
    (ordinary : ∀ entry body depth probe, value ≠ .mu entry body depth probe)
    (member : child ∈ semanticChildren value) : valueDepth child ≤ valueDepth value := by
  cases value with
  | empty | reference => simp [semanticChildren] at member
  | mu entry body depth probe => exact False.elim (ordinary entry body depth probe rfl)
  | node entry edges depth free =>
      rw [node_depth entry edges depth free state coherent available.resident, edges_eq_many]
      exact (many_le_iff _ _).mp (Nat.le_refl _) child member
  | union entry members depth free =>
      rw [union_depth entry members depth free state coherent available.resident]
      exact (many_le_iff _ _).mp (Nat.le_refl _) child member

/-- Actual ordinary construction preserves the open-depth bound of its original children. -/
theorem makeNode_le [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (linked : Linked state)
    (resident : ∀ edge ∈ edges, EdgeResident state edge) (bound : Nat)
    (bounded : ∀ child ∈ edges.flatMap EdgeValue.children, valueDepth child ≤ bound) :
    valueDepth (run (makeNode edges) state).1 ≤ bound := by
  have selected : ∀ edge ∈ canonicalEdges (surviving edges), EdgeResident state edge :=
    fun edge member => resident edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  have selectedDepth : ∀ child ∈ (canonicalEdges (surviving edges)).flatMap EdgeValue.children,
      valueDepth child ≤ bound := by
    intro child member
    obtain ⟨edge, included, found⟩ := List.mem_flatMap.mp member
    exact bounded child (List.mem_flatMap.mpr
      ⟨edge, (List.mem_filter.mp (canonicalEdges_member _ edge included)).1, found⟩)
  unfold makeNode
  dsimp only
  split
  · simp [run, valueDepth, Value.free]
  · rename_i first rest same
    obtain ⟨entry, readback⟩ := identifyNode_readback (first :: rest) state coherent linked
      (by simpa [same] using selected)
    simp only [run, readback, identifyNode]
    rw [valueDepth.eq_def]
    split
    · exact Nat.zero_le _
    · change edgesDepth (first :: rest) ≤ bound
      rw [edges_eq_many]
      exact (many_le_iff _ _).mpr (by simpa [same] using selectedDepth)

/-- Complete canonical union readback preserves a bound on the exact requested members. -/
theorem union_readback_le (state : State Symbol Guard) (coherent : Coherent state)
    (members : List (Value Symbol Guard)) (entry : Interned NodeKey) (value : Value Symbol Guard)
    (fields : NodeFields (.union (members.map Value.referenceOf)) entry value)
    (output : Available state value) (inputs : ∀ member ∈ members, Available state member)
    (bound : Nat) (bounded : ∀ member ∈ members, valueDepth member ≤ bound) : valueDepth value ≤ bound := by
  cases value with
  | empty | reference | node | mu => simp [NodeFields, muKey] at fields
  | union actual actualMembers level free =>
      have same := value_lists_equal state coherent members actualMembers
        (fun value member => (inputs value member).resident)
        (fun value member => (output.children value member).resident)
        (NodeKey.union.inj fields.2.1)
      rw [union_depth actual actualMembers level free state coherent output.resident, ← same]
      exact (many_le_iff _ _).mpr bounded

/-- Every actual union branch preserves a common open stored-plan depth bound. -/
theorem makeUnion_le [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (cached : Cached state) (linked : Linked state)
    (available : ∀ value ∈ values, Available state value) (bound : Nat)
    (bounded : ∀ value ∈ values, valueDepth value ≤ bound) : valueDepth (run (makeUnion values) state).1 ≤ bound := by
  have allAvailable : ∀ value ∈ distinctNodes (values.flatMap unionMembers), Available state value := by
    intro value member
    obtain ⟨original, included, selected⟩ := List.mem_flatMap.mp (distinctNodes_member _ value member)
    exact unionMembers_available original (available original included) value selected
  have allDepth : ∀ value ∈ distinctNodes (values.flatMap unionMembers), valueDepth value ≤ bound := by
    intro value member
    obtain ⟨original, included, selected⟩ := List.mem_flatMap.mp (distinctNodes_member _ value member)
    cases original with
    | empty => simp [unionMembers] at selected
    | union entry members level free =>
        exact Nat.le_trans (ordinary_child_le _ value state coherent (available _ included)
          (by intros; intro impossible; cases impossible) selected) (bounded _ included)
    | reference | node | mu =>
        simp only [unionMembers, List.mem_singleton] at selected
        subst value
        exact bounded _ included
  cases normalized : distinctNodes (values.flatMap unionMembers) with
  | nil => simp [makeUnion, normalized, run, valueDepth]
  | cons first rest =>
      cases rest with
      | nil => simpa [makeUnion, normalized, run] using allDepth first (by simp [normalized])
      | cons second tail =>
          have membersAvailable : ∀ value ∈ first :: second :: tail, Available state value := by simpa [normalized] using allAvailable
          have membersDepth : ∀ value ∈ first :: second :: tail, valueDepth value ≤ bound := by simpa [normalized] using allDepth
          cases ordinary : ordinaryEdges (first :: second :: tail) with
          | some edges =>
              have resident := ordinaryEdges_resident _ edges state linked
                (fun value member => (membersAvailable value member).resident) ordinary
              have childrenDepth : ∀ child ∈ edges.flatMap EdgeValue.children, valueDepth child ≤ bound := by
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
                have sourceOrdinary : ∀ entry body depth probe, source ≠ .mu entry body depth probe := by
                  intros entry body depth probe impossible
                  subst source
                  simp [InternedEdgeResidency.nodeEdges] at edgeMember
                have semantic : child ∈ semanticChildren source := by
                  cases source <;> simp only [nodeEdges] at edgeMember <;> try contradiction
                  exact List.mem_flatMap.mpr ⟨edge, edgeMember, selected⟩
                exact Nat.le_trans (ordinary_child_le source child state coherent
                  (membersAvailable source sourceMember) sourceOrdinary semantic) (membersDepth source sourceMember)
              simpa only [makeUnion, normalized, ordinary] using makeNode_le edges state coherent linked resident bound childrenDepth
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
                union_readback_le after later members actual result fields output inputs bound membersDepth

/-- Root self-reference removal cannot increase the open stored-plan depth. -/
theorem filter_le [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (value : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (cached : Cached state) (linked : Linked state)
    (available : Available state value) : valueDepth (run (withoutSelfReference name value) state).1 ≤ valueDepth value := by
  cases value <;> simp only [withoutSelfReference, run] <;> try exact Nat.le_refl _
  case union entry members depth free =>
    split
    · exact makeUnion_le _ state coherent cached linked
        (fun value member => available.children value (List.mem_filter.mp member).1) _
        (fun value member => ordinary_child_le _ value state coherent available
          (by intros; intro impossible; cases impossible) (List.mem_filter.mp member).1)
    · exact Nat.le_refl _

end MicroCFTA.InternedStoredPlanBinderDepth
