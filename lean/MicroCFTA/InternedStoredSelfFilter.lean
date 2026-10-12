import MicroCFTA.InternedShallowGate

/-!
# Derived self-union normalization in stored Mu bodies

Both source probes and the allocated callback body run the actual root
self-reference filter. Every completed Mu record therefore stores a body
without its own bare reference as a root union alternative. Pending
outcomes preserve the same invariant for all records already completed.
-/
namespace MicroCFTA.InternedStoredSelfFilter
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedTemplateProvenance InternedConstructionProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedRequestFacts InternedNestedProvenance
open InternedUnionNormalForm InternedNormalizationFree InternedGateRank
open InternedBinderProtocol (NodeKey Reference)

/-- A root union has no bare occurrence of the selected reference. -/
def NoSelf (name : Reference) : Value Symbol Guard → Prop
  | .union _ members _ _ => .reference name ∉ members
  | _ => True

/-- A complete Mu has passed its actual root self-reference filter. -/
def CleanValue : Value Symbol Guard → Prop
  | .mu entry body _ _ => NoSelf (.interned entry.identity) body
  | _ => True

/-- Every completed Mu payload satisfies the source body normalization. -/
def Clean (state : State Symbol Guard) : Prop :=
  ∀ key value, state.nodeRecords key = some value → CleanValue value

/-- Empty tables contain no unnormalized binder record. -/
theorem empty_clean : Clean (empty (Symbol := Symbol) (Guard := Guard)) := by
  intro key value impossible
  cases impossible

/-- Available Mu records inherit the actual stored-body filter invariant. -/
theorem resident_clean (state : State Symbol Guard) (clean : Clean state)
    (value : Value Symbol Guard) (resident : Resident state value) : CleanValue value := by
  cases value with
  | mu entry body depth ordinary => exact clean entry.key _ (resident entry rfl)
  | empty | reference | node | union => trivial

/-- Ordinary node reconstruction cannot return a root union. -/
theorem makeNode_noSelf [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) : NoSelf name (run (makeNode edges) state).1 := by
  unfold makeNode
  dsimp only
  split
  · trivial
  · rename_i first rest _
    simp only [run]
    obtain ⟨entry, fields⟩ := requested_fields
      (.node ((first :: rest).map (fun edge => edge.entry.identity)))
      (identifyNode (first :: rest)) state coherent (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩)
    generalize found : (nodeStep _ _ state).1 = value at fields ⊢
    cases value <;> simp [NodeFields, muKey] at fields <;> trivial

/-- Normalized nonself operands produce a union without the removed reference. -/
theorem makeUnion_noSelf [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (cached : Cached state)
    (available : Values state values) (atomic : ∀ value ∈ values, Atomic value)
    (different : ∀ value ∈ values, value ≠ .reference name) : NoSelf name (run (makeUnion values) state).1 := by
  have flatMember : ∀ value ∈ values.flatMap unionMembers, value ∈ values := by
    intro value member
    obtain ⟨source, present, inner⟩ := List.mem_flatMap.mp member
    have sourceAtomic := atomic source present
    cases source <;> simp only [unionMembers, List.mem_singleton] at inner
    · contradiction
    · exact inner ▸ present
    · exact inner ▸ present
    · contradiction
    · exact inner ▸ present
  have normalizedMember : ∀ value ∈ distinctNodes (values.flatMap unionMembers), value ∈ values :=
    fun value member => flatMember value (distinctNodes_member _ value member)
  cases normalized : distinctNodes (values.flatMap unionMembers) with
  | nil => simp [makeUnion, normalized, run, NoSelf]
  | cons first rest =>
      cases rest with
      | nil =>
          have firstAtomic := atomic first (normalizedMember first (by simp [normalized]))
          cases first <;> simp_all [makeUnion, run, Atomic, NoSelf]
      | cons second tail =>
          have memberAvailable : ∀ value ∈ first :: second :: tail, Available state value :=
            fun value member => available value (normalizedMember value (by simpa [normalized] using member))
          have memberDifferent : ∀ value ∈ first :: second :: tail, value ≠ .reference name :=
            fun value member => different value (normalizedMember value (by simpa [normalized] using member))
          cases ordinary : ordinaryEdges (first :: second :: tail) with
          | some edges => simpa only [makeUnion, normalized, ordinary] using makeNode_noSelf name edges state coherent
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
                  available_after_run (makeUnion values) state coherent.valid (memberAvailable value member)
              obtain ⟨actual, fields⟩ := requested_fields key identify state coherent (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩)
              have noSelf : NoSelf name result := by
                change NodeFields key actual result at fields
                generalize resultEq : result = value at fields output ⊢
                cases value with
                | empty | reference | node | mu => trivial
                | union entry actualMembers level free =>
                    have equal := value_lists_equal after later members actualMembers
                      (fun value member => (inputs value member).resident)
                      (fun value member => (output.children value member).resident)
                      (NodeKey.union.inj fields.2.1)
                    change .reference name ∉ actualMembers
                    rw [← equal]
                    exact fun member => memberDifferent _ member rfl
              simpa only [makeUnion, normalized, ordinary, run] using noSelf

/-- The actual source filter establishes the body property from derived flat union records. -/
theorem filter_noSelf [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (value : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (cached : Cached state) (flat : Flat state)
    (available : Available state value) : NoSelf name (run (withoutSelfReference name value) state).1 := by
  cases value <;> simp only [withoutSelfReference, run] <;> try trivial
  case union entry members depth free =>
    split
    · exact makeUnion_noSelf name _ state coherent cached
        (fun value member => available.children value (List.mem_filter.mp member).1)
        (fun value member => resident_flat state flat _ available.resident value (List.mem_filter.mp member).1)
        (fun value member => ((withoutSelfReference_members name members value).mp member).2)
    · rename_i absent
      intro member
      exact absent (List.any_eq_true.mpr ⟨.reference name, member, by simp [Value.referenceOf]⟩)

/-- A source node request retains earlier normalized Mu bodies. -/
theorem nodeStep_clean (key : NodeKey) (identify : Interned NodeKey → Value Symbol Guard)
    (state : State Symbol Guard) (clean : Clean state) (candidate : ∀ entry, CleanValue (identify entry)) :
    Clean (nodeStep key identify state).2 := by
  intro other value present
  rcases record_cases _ key other _ value present with old | ⟨same, equal⟩
  · exact clean other value old
  · subst other value
    exact candidate _

/-- Ordinary source node construction installs no new Mu payload. -/
theorem makeNode_clean [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (clean : Clean state) : Clean (run (makeNode edges) state).2 := by
  unfold makeNode
  dsimp only
  split
  · exact clean
  · exact nodeStep_clean _ _ state clean (fun _ => trivial)

/-- Source union normalization installs no new Mu payload. -/
theorem makeUnion_clean [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (clean : Clean state) : Clean (run (makeUnion values) state).2 := by
  unfold makeUnion
  split
  · exact clean
  · exact clean
  · split
    · exact makeNode_clean _ state clean
    · simp only [run]
      exact nodeStep_clean _ _ state clean (fun _ => trivial)

/-- Filtering one body preserves all earlier Mu payloads. -/
theorem filter_clean [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (value : Value Symbol Guard)
    (state : State Symbol Guard) (clean : Clean state) : Clean (run (withoutSelfReference name value) state).2 := by
  cases value <;> simp only [withoutSelfReference] <;> try exact clean
  case union => split <;> first | exact makeUnion_clean _ state clean | exact clean

/-- Completing the filtered callback installs a normalized Mu body. -/
theorem complete_clean (smart : Bool) (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard) (clean : Clean state)
    (filtered : NoSelf (.interned entry.identity) body) : Clean (complete smart entry body depth ordinary state).state := by
  intro key value present
  rcases record_cases state.nodeRecords (muKey depth ordinary) key (.mu entry body depth ordinary) value present with old | ⟨same, equal⟩
  · exact clean key value old
  · subst key value
    exact filtered

/-- Sequencing retains completed binder normalization at every intermediate state. -/
theorem bind_clean (state : State Symbol Guard) (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result)
    (property : State Symbol Guard → First → Prop) (verified : Verified state outcome property)
    (clean : Clean outcome.state)
    (later : ∀ value after, outcome = .done value after → Facts after → property after value → Clean after → Clean (next value after).state) :
    Clean (outcome.bind next).state := by
  cases outcome with
  | pending => exact clean
  | done value after => exact later value after rfl verified.facts (verified.result value after rfl) clean

/-- Mu lookup and reservation use the filtered callback's derived body property. -/
theorem request_clean [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (depth ordinary : Value Symbol Guard)
    (callback : Reference → State Symbol Guard → Outcome Symbol Guard (Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (flat : Flat state) (clean : Clean state)
    (checked : ∀ name current, Grows state current → Extends state.nodes.issued current.nodes.issued →
      Facts current → Available current (.reference name) → Flat current → Clean current →
      Verified current (callback name current) (fun state value => Available state value ∧ NoSelf name value) ∧ Clean (callback name current).state) :
    Clean (request smart depth ordinary callback state).state := by
  unfold request
  dsimp only
  split
  · split <;> exact clean
  · let key := muKey depth ordinary
    let entry := Cache.intern state.nodes key
    let allocated := {state with nodes := entry.2}
    have growth : Grows state allocated :=
      ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
    have body := checked (.interned entry.1.identity) allocated growth
      (intern_issued_extends state.nodes key facts.coherent.valid.2) (reserve_facts key state facts)
      (reserve_available key state facts.coherent facts.cached).2 flat clean
    exact bind_clean allocated _ _ _ body.1 body.2
      (fun value after _ _ property afterClean => complete_clean smart entry.1 value depth ordinary after afterClean property.2)

end MicroCFTA.InternedStoredSelfFilter
