import MicroCFTA.InternedStoredPlanBinderDepthNormalization

/-!
# Exact open binder depth through source normalization

Union construction preserves the maximum open depth of its operands.
Root self-reference filtering preserves the same measure. Canonical
readback and ordinary edge merging retain the actual child records.
-/
namespace MicroCFTA.InternedStoredPlanBinderDepth
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNormalizationFree InternedEdgeResidency InternedLiveEdges
open InternedUnionSeparation InternedUnionDescendants InternedFreshProbeKeys InternedGateRank
open InternedBinderProtocol (NodeKey Reference)

/-- Concatenation takes the maximum of the two open-depth bounds. -/
theorem many_append (first second : List (Value Symbol Guard)) :
    manyDepth (first ++ second) = max (manyDepth first) (manyDepth second) := by
  induction first with
  | nil => simp [manyDepth]
  | cons first rest ih => simp [manyDepth, ih, Nat.max_assoc]

/-- Concatenating edge lists takes the maximum of their two open depths. -/
theorem edges_append (first second : List (EdgeValue Symbol Guard)) :
    edgesDepth (first ++ second) = max (edgesDepth first) (edgesDepth second) := by
  simp only [edges_eq_many, List.flatMap_append, many_append]

/-- An ordinary candidate has exactly the open depth of its original children. -/
theorem identifyNode_depth (edges : List (EdgeValue Symbol Guard)) (entry : Interned NodeKey) :
    valueDepth (identifyNode edges entry) = edgesDepth edges := by
  rw [valueDepth.eq_def]
  split
  · rename_i closed
    change 0 = edgesDepth edges
    rw [edges_eq_many, many_zero_of_free _ (List.isEmpty_iff.mp closed)]
  · rfl

/-- Canonical edge sorting and deduplication preserve the exact maximum open depth. -/
theorem canonicalEdges_depth (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (resident : ∀ edge ∈ edges, EdgeResident state edge) :
    edgesDepth (canonicalEdges edges) = edgesDepth edges := by
  simp only [edges_eq_many]
  apply Nat.le_antisymm
  · apply (many_le_iff _ _).mpr
    intro child member
    obtain ⟨edge, included, selected⟩ := List.mem_flatMap.mp member
    exact (many_le_iff _ _).mp (Nat.le_refl _) child
      (List.mem_flatMap.mpr ⟨edge, canonicalEdges_member _ edge included, selected⟩)
  · apply (many_le_iff _ _).mpr
    intro child member
    obtain ⟨edge, included, selected⟩ := List.mem_flatMap.mp member
    exact (many_le_iff _ _).mp (Nat.le_refl _) child
      (List.mem_flatMap.mpr ⟨edge, canonicalEdges_retains state coherent edges edge resident included, selected⟩)

/-- Actual ordinary construction retains exactly the open depth of its surviving edges. -/
theorem makeNode_depth [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (linked : Linked state)
    (resident : ∀ edge ∈ edges, EdgeResident state edge) :
    valueDepth (run (makeNode edges) state).1 = edgesDepth (surviving edges) := by
  have selected : ∀ edge ∈ canonicalEdges (surviving edges), EdgeResident state edge :=
    fun edge member => resident edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  have canonical := canonicalEdges_depth (surviving edges) state coherent
    (fun edge member => resident edge (List.mem_filter.mp member).1)
  unfold makeNode
  dsimp only
  split
  · rename_i same
    have zero : edgesDepth (surviving edges) = 0 := by
      rw [← canonical, same, edgesDepth]
    simp [run, valueDepth, Value.free, zero]
  · rename_i first rest same
    obtain ⟨entry, readback⟩ := identifyNode_readback (first :: rest) state coherent linked
      (by simpa [same] using selected)
    simp only [run, readback, identifyNode_depth]
    rw [← same]
    exact canonical

/-- Root union flattening preserves the complete maximum of available operands. -/
theorem flatten_depth (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (available : ∀ value ∈ values, Available state value) :
    manyDepth (values.flatMap unionMembers) = manyDepth values := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
      rw [List.flatMap_cons, many_append, manyDepth, ih (fun value member => available value (List.mem_cons_of_mem _ member))]
      congr 1
      cases first with
      | empty => simp [unionMembers, manyDepth, valueDepth, Value.free]
      | reference | node | mu => simp [unionMembers, manyDepth]
      | union entry members depth free =>
          exact (union_depth entry members depth free state coherent (available _ List.mem_cons_self).resident).symm

/-- Physical identity deduplication preserves the exact open-depth maximum. -/
theorem distinctNodes_depth (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (available : ∀ value ∈ values, Available state value) :
    manyDepth (distinctNodes values) = manyDepth values := by
  apply Nat.le_antisymm
  · apply (many_le_iff _ _).mpr
    intro value member
    exact (many_le_iff _ _).mp (Nat.le_refl _) value (distinctNodes_member _ value member)
  · apply (many_le_iff _ _).mpr
    intro value member
    exact (many_le_iff _ _).mp (Nat.le_refl _) value
      (InternedUnionRetention.distinctNodes_retains state coherent values
        (fun value member => (available value member).resident) value member)

/-- Merging ordinary operands takes exactly their maximum open binder depth. -/
theorem ordinaryEdges_depth (values : List (Value Symbol Guard)) (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state)
    (available : ∀ value ∈ values, Available state value) (found : ordinaryEdges values = some edges) :
    edgesDepth edges = manyDepth values := by
  induction values generalizing edges with
  | nil => cases found; simp [edgesDepth, manyDepth]
  | cons first rest ih =>
      cases first <;> simp only [ordinaryEdges] at found <;> try contradiction
      case node entry own depth free =>
        cases tail : ordinaryEdges rest with
        | none => simp [tail] at found
        | some later =>
            have same : own ++ later = edges := by simpa [tail] using found
            rw [← same, edges_append, manyDepth,
              ih later (fun value member => available value (List.mem_cons_of_mem _ member)) tail,
              node_depth entry own depth free state coherent (available _ List.mem_cons_self).resident]

/-- An ordinary union merge removes no previously live stored edge. -/
theorem ordinaryEdges_surviving (values : List (Value Symbol Guard)) (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (live : Live state)
    (available : ∀ value ∈ values, Available state value) (found : ordinaryEdges values = some edges) :
    surviving edges = edges := by
  induction values generalizing edges with
  | nil => cases found; rfl
  | cons first rest ih =>
      cases first <;> simp only [ordinaryEdges] at found <;> try contradiction
      case node entry own depth free =>
        cases tail : ordinaryEdges rest with
        | none => simp [tail] at found
        | some later =>
            have same : own ++ later = edges := by simpa [tail] using found
            have retained : surviving own = own := by
              apply List.filter_eq_self.mpr
              intro edge member
              have alive := resident_live state live _ (available _ List.mem_cons_self).resident edge member
              simp [alive]
            rw [← same]
            have append : surviving (own ++ later) = surviving own ++ surviving later := by
              simp only [surviving, List.filter_append]
            rw [append, retained, ih later (fun value member => available value (List.mem_cons_of_mem _ member)) tail]

/-- Canonical union readback retains the exact open-depth maximum of its named members. -/
theorem union_readback_depth (state : State Symbol Guard) (coherent : Coherent state)
    (members : List (Value Symbol Guard)) (entry : Interned NodeKey) (value : Value Symbol Guard)
    (fields : NodeFields (.union (members.map Value.referenceOf)) entry value)
    (output : Available state value) (inputs : ∀ member ∈ members, Available state member) :
    valueDepth value = manyDepth members := by
  cases value with
  | empty | reference | node | mu => simp [NodeFields, muKey] at fields
  | union actual originals depth free =>
      have same := value_lists_equal state coherent members originals
        (fun value member => (inputs value member).resident)
        (fun value member => (output.children value member).resident) (NodeKey.union.inj fields.2.1)
      rw [union_depth actual originals depth free state coherent output.resident, ← same]

/-- Every actual union branch preserves the exact maximum open depth of its input records. -/
theorem makeUnion_depth [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (cached : Cached state)
    (linked : Linked state) (live : Live state) (available : ∀ value ∈ values, Available state value) :
    valueDepth (run (makeUnion values) state).1 = manyDepth values := by
  have allAvailable : ∀ value ∈ values.flatMap unionMembers, Available state value := by
    intro value member
    obtain ⟨source, included, selected⟩ := List.mem_flatMap.mp member
    exact unionMembers_available source (available source included) value selected
  have exactDepth := (distinctNodes_depth (values.flatMap unionMembers) state coherent allAvailable).trans
    (flatten_depth values state coherent available)
  have normalizedAvailable : ∀ value ∈ distinctNodes (values.flatMap unionMembers), Available state value :=
    fun value member => allAvailable value (distinctNodes_member _ value member)
  cases normalized : distinctNodes (values.flatMap unionMembers) with
  | nil => simpa only [normalized, manyDepth, makeUnion, run, valueDepth, Value.free, List.isEmpty_nil, ↓reduceIte] using exactDepth
  | cons first rest =>
      cases rest with
      | nil => simpa only [makeUnion, normalized, run, manyDepth, Nat.max_zero] using exactDepth
      | cons second tail =>
          have membersAvailable : ∀ value ∈ first :: second :: tail, Available state value := by
            simpa only [normalized] using normalizedAvailable
          have membersDepth : manyDepth (first :: second :: tail) = manyDepth values := by
            simpa only [normalized] using exactDepth
          cases ordinary : ordinaryEdges (first :: second :: tail) with
          | some edges =>
              have resident := ordinaryEdges_resident _ edges state linked
                (fun value member => (membersAvailable value member).resident) ordinary
              simpa only [makeUnion, normalized, ordinary] using
                (makeNode_depth edges state coherent linked resident).trans
                  ((congrArg edgesDepth (ordinaryEdges_surviving _ edges state live membersAvailable ordinary)).trans
                    ((ordinaryEdges_depth _ edges state coherent membersAvailable ordinary).trans membersDepth))
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
              have exactResult := union_readback_depth after later members actual result fields output inputs
              simpa only [makeUnion, normalized, ordinary, run] using exactResult.trans membersDepth

/-- A root union member removed by the self filter has open depth zero. -/
theorem self_member_zero (value : Value Symbol Guard) (name : Reference)
    (same : value.referenceOf = .ref name) : valueDepth value = 0 := by
  cases value <;> simp only [Value.referenceOf] at same <;> try contradiction
  simp [valueDepth, Value.free]

/-- Filtering only bare self references preserves the complete maximum open depth. -/
theorem many_filter_self (values : List (Value Symbol Guard)) (name : Reference) :
    manyDepth (values.filter (fun value => value.referenceOf != .ref name)) = manyDepth values := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
      by_cases same : first.referenceOf = .ref name
      · simp [same, self_member_zero first name same, manyDepth, ih]
      · simp [same, manyDepth, ih]

/-- Actual root self-reference removal preserves exact open binder depth. -/
theorem filter_depth [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (value : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (cached : Cached state)
    (linked : Linked state) (live : Live state) (available : Available state value) :
    valueDepth (run (withoutSelfReference name value) state).1 = valueDepth value := by
  cases value <;> simp only [withoutSelfReference, run] <;> try rfl
  case union entry members depth free =>
    split
    · exact (makeUnion_depth _ state coherent cached linked live
        (fun value member => available.children value (List.mem_filter.mp member).1)).trans
          ((many_filter_self members name).trans (union_depth entry members depth free state coherent available.resident).symm)
    · rfl

end MicroCFTA.InternedStoredPlanBinderDepth
