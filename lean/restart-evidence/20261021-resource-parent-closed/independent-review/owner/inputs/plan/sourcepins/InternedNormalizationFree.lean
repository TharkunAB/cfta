import MicroCFTA.InternedUnionDescendants

/-!
# Free-name metadata through actual source normalization

The source stores complete child records and computes union free names from
them. Coherent readback, resident edges, and live-edge normalization make
those equations hold through deduplication and ordinary edge merging.
-/
namespace MicroCFTA.InternedNormalizationFree
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedEdgeResidency InternedLiveEdges
open InternedUnionRetention InternedUnionDescendants
open InternedBinderProtocol (Reference NodeKey)

/-- An ordinary resident node has exactly the free names of its actual ordered children. -/
theorem node_free (state : State Symbol Guard) (coherent : Coherent state)
    (entry : Interned NodeKey) (edges : List (EdgeValue Symbol Guard)) (depth : Nat) (free : List Reference)
    (resident : Resident state (.node entry edges depth free)) :
    free = childFree (edges.flatMap EdgeValue.children) := by
  obtain ⟨actual, _, fields⟩ := coherent.nodes entry.key _ (resident entry rfl)
  exact fields.2.2.2

/-- A resident union has exactly the free names of its actual member records. -/
theorem union_free (state : State Symbol Guard) (coherent : Coherent state)
    (entry : Interned NodeKey) (members : List (Value Symbol Guard)) (depth : Nat) (free : List Reference)
    (resident : Resident state (.union entry members depth free)) : free = childFree members := by
  obtain ⟨actual, _, fields⟩ := coherent.nodes entry.key _ (resident entry rfl)
  exact fields.2.2.2

/-- The source flattening operation retains exactly each operand's free names. -/
theorem unionMembers_free (state : State Symbol Guard) (coherent : Coherent state)
    (value : Value Symbol Guard) (available : Available state value) (name : Reference) :
    name ∈ value.free ↔ ∃ member ∈ unionMembers value, name ∈ member.free := by
  cases value with
  | empty => simp [Value.free, unionMembers]
  | reference | node | mu => simp [unionMembers]
  | union entry members depth free =>
      simp only [Value.free, unionMembers, union_free state coherent entry members depth free available.resident]
      exact childFree_member members name

/-- Resident source identity lists determine complete immutable value lists. -/
theorem value_lists_equal (state : State Symbol Guard) (coherent : Coherent state)
    (left right : List (Value Symbol Guard))
    (leftResident : ∀ value ∈ left, Resident state value)
    (rightResident : ∀ value ∈ right, Resident state value)
    (same : left.map Value.referenceOf = right.map Value.referenceOf) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp_all
  | cons first rest ih =>
      cases right with
      | nil => simp at same
      | cons second tail =>
          have parts := List.cons.inj same
          have equal := resident_reference_injective state coherent first second
            (leftResident first (by simp)) (rightResident second (by simp)) parts.1
          have tails := ih tail (fun value member => leftResident value (by simp [member]))
            (fun value member => rightResident value (by simp [member])) parts.2
          simp [equal, tails]

/-- Actual node readback stores the free names of the exact surviving edge children. -/
theorem makeNode_free [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (linked : Linked state)
    (resident : ∀ edge ∈ edges, EdgeResident state edge) :
    (run (makeNode edges) state).1.free = childFree ((canonicalEdges (surviving edges)).flatMap EdgeValue.children) := by
  have selected : ∀ edge ∈ canonicalEdges (surviving edges), EdgeResident state edge := by
    intro edge member
    exact resident edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  unfold makeNode
  dsimp only
  split
  · rename_i same
    simp [run, Value.free, same, childFree, canonicalFree]
  · rename_i first rest same
    obtain ⟨entry, exactResult⟩ := identifyNode_readback (first :: rest) state coherent linked
      (by simpa [same] using selected)
    simp only [run, exactResult, identifyNode, Value.free, same]

/-- When all input edges are live, source node normalization preserves every
free-name occurrence from their actual child payloads. -/
theorem makeNode_live_free [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (linked : Linked state)
    (resident : ∀ edge ∈ edges, EdgeResident state edge)
    (live : ∀ edge ∈ edges, edge.children.any (fun child => child.referenceOf == .empty) = false)
    (name : Reference) :
    name ∈ (run (makeNode edges) state).1.free ↔
      ∃ edge ∈ edges, ∃ child ∈ edge.children, name ∈ child.free := by
  rw [makeNode_free edges state coherent linked resident, childFree_member]
  have same : surviving edges = edges := by
    apply List.filter_eq_self.mpr
    intro edge member
    simp [live edge member]
  rw [same]
  constructor
  · rintro ⟨child, present, free⟩
    obtain ⟨edge, included, inEdge⟩ := List.mem_flatMap.mp present
    exact ⟨edge, canonicalEdges_member edges edge included, child, inEdge, free⟩
  · rintro ⟨edge, included, child, inEdge, free⟩
    exact ⟨child, List.mem_flatMap.mpr ⟨edge, canonicalEdges_retains state coherent edges edge resident included, inEdge⟩, free⟩

/-- All-ordinary union extraction retains precisely the free names of each resident operand. -/
theorem ordinaryEdges_free (state : State Symbol Guard) (coherent : Coherent state)
    (values : List (Value Symbol Guard)) (edges : List (EdgeValue Symbol Guard))
    (resident : ∀ value ∈ values, Resident state value) (found : ordinaryEdges values = some edges)
    (name : Reference) :
    (∃ edge ∈ edges, ∃ child ∈ edge.children, name ∈ child.free) ↔
      ∃ value ∈ values, name ∈ value.free := by
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
            have current := node_free state coherent entry own depth free (resident _ (by simp))
            have others := ih later (fun value member => resident value (by simp [member])) tail
            constructor
            · rintro ⟨edge, member, child, included, named⟩
              rcases List.mem_append.mp member with first | rest
              · refine ⟨.node entry own depth free, by simp, ?_⟩
                simp only [Value.free, current]
                exact (childFree_member _ name).mpr ⟨child, List.mem_flatMap.mpr ⟨edge, first, included⟩, named⟩
              · obtain ⟨value, present, free⟩ := others.mp ⟨edge, rest, child, included, named⟩
                exact ⟨value, by simp [present], free⟩
            · rintro ⟨value, member, named⟩
              rcases List.mem_cons.mp member with rfl | member
              · have original : name ∈ childFree (own.flatMap EdgeValue.children) := by
                  simpa only [Value.free, current] using named
                obtain ⟨child, children, free⟩ := (childFree_member _ name).mp original
                obtain ⟨edge, present, included⟩ := List.mem_flatMap.mp children
                exact ⟨edge, List.mem_append_left later present, child, included, free⟩
              · obtain ⟨edge, present, child, included, free⟩ := others.mpr ⟨value, member, named⟩
                exact ⟨edge, List.mem_append_right own present, child, included, free⟩

/-- Flattening and identity deduplication preserve all free names of available operands. -/
theorem normalized_free (state : State Symbol Guard) (coherent : Coherent state)
    (values : List (Value Symbol Guard)) (available : ∀ value ∈ values, Available state value) (name : Reference) :
    (∃ value ∈ distinctNodes (values.flatMap unionMembers), name ∈ value.free) ↔
      ∃ value ∈ values, name ∈ value.free := by
  have allAvailable : ∀ value ∈ values.flatMap unionMembers, Available state value := by
    intro value member
    obtain ⟨outer, included, inner⟩ := List.mem_flatMap.mp member
    exact unionMembers_available outer (available outer included) value inner
  constructor
  · rintro ⟨value, member, free⟩
    obtain ⟨outer, included, inner⟩ := List.mem_flatMap.mp (distinctNodes_member _ value member)
    exact ⟨outer, included, (unionMembers_free state coherent outer (available outer included) name).mpr ⟨value, inner, free⟩⟩
  · rintro ⟨outer, included, free⟩
    obtain ⟨value, inner, named⟩ := (unionMembers_free state coherent outer (available outer included) name).mp free
    have flat := List.mem_flatMap.mpr ⟨outer, included, inner⟩
    exact ⟨value, distinctNodes_retains state coherent _
      (fun value member => (allAvailable value member).resident) value flat, named⟩

/-- Complete union-cache readback preserves each free-name occurrence from
the requested resident operand list. -/
theorem union_readback_free (state : State Symbol Guard) (coherent : Coherent state)
    (members : List (Value Symbol Guard)) (entry : Interned NodeKey) (result : Value Symbol Guard)
    (fields : NodeFields (.union (members.map Value.referenceOf)) entry result)
    (available : Available state result) (inputs : ∀ value ∈ members, Available state value)
    (name : Reference) : name ∈ result.free ↔ ∃ value ∈ members, name ∈ value.free := by
  cases result with
  | empty | reference | node | mu => simp [NodeFields, muKey] at fields
  | union actual original depth free =>
      have ids : members.map Value.referenceOf = original.map Value.referenceOf := NodeKey.union.inj fields.2.1
      have equal := value_lists_equal state coherent members original
        (fun value member => (inputs value member).resident)
        (fun value member => (available.children value member).resident) ids
      simp only [Value.free, fields.2.2.2, ← equal]
      exact childFree_member members name

/-- Every source union branch preserves exactly the free names of its
available operands. Live ordinary edges are derived by the full executor. -/
theorem makeUnion_free [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (cached : Cached state)
    (linked : Linked state) (live : Live state)
    (available : ∀ value ∈ values, Available state value) (name : Reference) :
    name ∈ (run (makeUnion values) state).1.free ↔ ∃ value ∈ values, name ∈ value.free := by
  have allAvailable : ∀ value ∈ distinctNodes (values.flatMap unionMembers), Available state value := by
    intro value member
    obtain ⟨outer, included, inner⟩ := List.mem_flatMap.mp (distinctNodes_member _ value member)
    exact unionMembers_available outer (available outer included) value inner
  have built := makeUnion_available values state coherent cached available
  rw [← normalized_free state coherent values available name]
  cases normalized : distinctNodes (values.flatMap unionMembers) with
  | nil => simp [makeUnion, normalized, run, Value.free]
  | cons first rest =>
      cases rest with
      | nil => simp [makeUnion, normalized, run]
      | cons second tail =>
          have memberAvailable : ∀ value ∈ first :: second :: tail, Available state value := by
            simpa [normalized] using allAvailable
          cases ordinaryResult : ordinaryEdges (first :: second :: tail) with
          | some edges =>
              have resident := ordinaryEdges_resident _ edges state linked
                (fun value member => (memberAvailable value member).resident) ordinaryResult
              have edgesLive : ∀ edge ∈ edges, edge.children.any (fun child => child.referenceOf == .empty) = false := by
                have fromOrdinary : ∀ (inputs : List (Value Symbol Guard)) output,
                    (∀ value ∈ inputs, ValueLive value) → ordinaryEdges inputs = some output →
                    ∀ edge ∈ output, edge.children.any (fun child => child.referenceOf == .empty) = false := by
                  intro inputs
                  induction inputs with
                  | nil => intro output _ found; cases found; simp
                  | cons value inputs ih =>
                      intro output allLive found
                      cases value <;> simp only [ordinaryEdges] at found <;> try contradiction
                      case node actual own depth free =>
                        cases later : ordinaryEdges inputs with
                        | none => simp [later] at found
                        | some tail =>
                            have equal : own ++ tail = output := by simpa [later] using found
                            subst output
                            intro edge present
                            rcases List.mem_append.mp present with left | right
                            · exact allLive (.node actual own depth free) (by simp) edge left
                            · exact ih tail (fun value member => allLive value (by simp [member])) later edge right
                exact fromOrdinary _ edges
                  (fun value member => resident_live state live value (memberAvailable value member).resident) ordinaryResult
              have free := (makeNode_live_free edges state coherent linked resident edgesLive name).trans
                (ordinaryEdges_free state coherent _ edges
                  (fun value member => (memberAvailable value member).resident) ordinaryResult name)
              simpa only [makeUnion, normalized, ordinaryResult] using free
          | none =>
              let members := first :: second :: tail
              let key := NodeKey.union (members.map Value.referenceOf)
              let identify := fun entry => Value.union entry members (maximumDepth members) (childFree members)
              let after := (nodeStep key identify state).2
              let result := (nodeStep key identify state).1
              have outputAvailable : Available after result := by simpa only [makeUnion, normalized, ordinaryResult, run] using built.2.2
              have afterCoherent : Coherent after := by simpa only [makeUnion, normalized, ordinaryResult, run] using built.1
              have inputs : ∀ value ∈ members, Available after value := by
                intro value present
                simpa only [makeUnion, normalized, ordinaryResult, run] using
                  available_after_run (makeUnion values) state coherent.valid (memberAvailable value present)
              obtain ⟨actual, fields⟩ := InternedGateRank.requested_fields key identify state coherent
                (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩)
              have free := union_readback_free after afterCoherent members actual result fields outputAvailable inputs name
              simpa only [makeUnion, normalized, ordinaryResult, run] using free

/-- Current root self-reference filtering preserves every other free name
through source union normalization and cache readback. -/
theorem filter_free_other [DecidableEq (EdgeKey Symbol Guard)] (binder name : Reference)
    (value : Value Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (cached : Cached state) (linked : Linked state) (live : Live state)
    (available : Available state value) (different : name ≠ binder) :
    name ∈ (run (withoutSelfReference binder value) state).1.free ↔ name ∈ value.free := by
  cases value <;> simp only [withoutSelfReference, run] <;> try rfl
  case union entry members depth free =>
    split
    · rw [makeUnion_free (members.filter (fun member => member.referenceOf != .ref binder)) state coherent cached linked live
        (fun value member => available.children value (List.mem_filter.mp member).1) name]
      have original := union_free state coherent entry members depth free available.resident
      simp only [Value.free, original, childFree_member]
      constructor
      · rintro ⟨value, present, named⟩
        exact ⟨value, (List.mem_filter.mp present).1, named⟩
      · rintro ⟨value, present, named⟩
        have notSelf : value ≠ .reference binder := by
          intro same
          simp [same, Value.free, different] at named
        exact ⟨value, (withoutSelfReference_members binder members value).mpr ⟨present, notSelf⟩, named⟩
    · rfl

/-- Unused-binder and bare-self cleanup preserve the exact stored free-name list. -/
theorem cleanup_free (value : Value Symbol Guard) : (cleanup value).free = value.free := by
  cases value <;> simp only [cleanup] <;> try rfl
  case mu entry body depth ordinary =>
    split
    · rename_i unused
      simp only [Value.free]
      symm
      apply List.filter_eq_self.mpr
      intro name present
      have different : name ≠ .interned entry.identity := fun same => unused (same ▸ present)
      simpa using different
    · split
      · rename_i self
        have same := (referenceOf_self_iff (.interned entry.identity) body).mp self
        simp [Value.free, same]
      · rfl

/-- Filtering the body's root self alternative preserves every external
free name of the completed binder. -/
theorem binder_filter_free [DecidableEq (EdgeKey Symbol Guard)]
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (cached : Cached state)
    (linked : Linked state) (live : Live state) (available : Available state body)
    (name : Reference) :
    name ∈ (Value.mu entry (run (withoutSelfReference (.interned entry.identity) body) state).1 depth ordinary).free ↔
      name ∈ (Value.mu entry body depth ordinary).free := by
  by_cases same : name = .interned entry.identity
  · simp [Value.free, same]
  · simp only [Value.free, List.mem_filter, bne_iff_ne, ne_eq, same, not_false_eq_true, and_true]
    exact filter_free_other _ name body state coherent cached linked live available same

/-- The actual filter followed by smart cleanup preserves binder free-name membership. -/
theorem smart_binder_free [DecidableEq (EdgeKey Symbol Guard)]
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (cached : Cached state)
    (linked : Linked state) (live : Live state) (available : Available state body)
    (name : Reference) :
    name ∈ (cleanup (Value.mu entry
      (run (withoutSelfReference (.interned entry.identity) body) state).1 depth ordinary)).free ↔
      name ∈ (Value.mu entry body depth ordinary).free := by
  rw [cleanup_free]
  exact binder_filter_free entry body depth ordinary state coherent cached linked live available name

/-- A preserved free name excludes source EmptyNode, independently of semantic inhabitation. -/
theorem free_nonempty (value : Value Symbol Guard) (name : Reference) (present : name ∈ value.free) :
    value.referenceOf ≠ .empty := by
  cases value <;> simp_all [Value.free, Value.referenceOf]

end MicroCFTA.InternedNormalizationFree
