import MicroCFTA.SourceCurrentConstrainedCapNonplainRank
import MicroCFTA.InternedDeepFreeNormalization

/-!
# Ranked free occurrences through actual constructor normalization

Each positive request bound permits equal-weight references only at the root.
An ordinary constructor needs strictly smaller free occurrences in its children.
Union construction preserves this classification through actual cache readback.
Root filtering and smart cleanup then remove a maximal local reference.
These local producer laws do not certify native calls or earlier Mu bodies.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapPairOccurrences
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedEdgeResidency InternedNestedFacts InternedStoredMuOrigins
open InternedDeepFreeDepth InternedNormalizationFree
open InternedBinderProtocol (Reference NodeKey)
variable {Symbol Guard : Type}

/-- An immutable source payload supplies each numeric identity's nonhereditary weight. -/
noncomputable def sourceWeight (annotation : Guard → Prop) (source : State Symbol Guard) : Reference → Nat
  | .intersection left right =>
      ((SourcePreparedSharedRows.read source left).map (SourceCurrentConstrainedCapNonplainRank.rank annotation)).getD 0 +
      ((SourcePreparedSharedRows.read source right).map (SourceCurrentConstrainedCapNonplainRank.rank annotation)).getD 0
  | _ => 0

/-- Every actual free reference has weight at most the current request bound. -/
def FreeLE (weight : Reference → Nat) (bound : Nat) (value : Value Symbol Guard) : Prop :=
  ∀ name ∈ value.free, weight name ≤ bound

/-- At a positive bound, every actual free reference is strictly smaller. -/
def FreeBelow (weight : Reference → Nat) (bound : Nat) (value : Value Symbol Guard) : Prop :=
  ∀ name ∈ value.free, weight name < bound ∨ bound = 0

/-- Equal positive weights can occur only outside ordinary and Mu boundaries. -/
structure Classified (weight : Reference → Nat) (bound : Nat) (value : Value Symbol Guard) : Prop where
  free : FreeLE weight bound value
  deep : ∀ name ∈ deepNames value, weight name < bound ∨ bound = 0

/-- Empty has no free or deep occurrence. -/
theorem empty (weight : Reference → Nat) (bound : Nat) :
    Classified weight bound (Value.empty (Symbol := Symbol) (Guard := Guard)) := by
  constructor <;> simp [FreeLE, Value.free, deepNames]

/-- A literal repeated reference has only a root occurrence. -/
theorem reference (weight : Reference → Nat) (bound : Nat) (name : Reference) (within : weight name ≤ bound) :
    Classified weight bound (Value.reference (Symbol := Symbol) (Guard := Guard) name) := by
  refine ⟨?_, ?_⟩
  · intro actual member
    exact List.mem_singleton.mp member ▸ within
  · simp [deepNames]

/-- A smaller request's free bound is sufficient below one ordinary boundary. -/
theorem FreeLE.below {weight : Reference → Nat} {smaller bound : Nat} {value : Value Symbol Guard}
    (free : FreeLE weight smaller value) (decrease : smaller < bound) : FreeBelow weight bound value := by
  intro name member
  exact .inl (Nat.lt_of_le_of_lt (free name member) decrease)

/-- A coherent record with a strictly smaller free set has the full local classification. -/
theorem of_below (weight : Reference → Nat) (bound : Nat) (value : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (available : Available state value)
    (free : FreeLE weight bound value) (below : FreeBelow weight bound value) : Classified weight bound value :=
  ⟨free, fun name member => below name (InternedDeepFreeNormalization.deep_free value state coherent available name member)⟩

/-- A maximal reference cannot occur below an ordinary or Mu boundary. -/
theorem Classified.not_deep {weight : Reference → Nat} {bound : Nat} {value : Value Symbol Guard}
    (classified : Classified weight bound value) (positive : 0 < bound) (name : Reference)
    (maximal : bound ≤ weight name) : name ∉ deepNames value := by
  intro member
  rcases classified.deep name member with lower | zero <;> omega

section Constructors
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Actual ordinary readback places only smaller child occurrences below its new boundary. -/
theorem makeNode (weight : Reference → Nat) (bound : Nat) (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (resident : ∀ edge ∈ edges, EdgeResident state edge)
    (children : ∀ edge ∈ edges, ∀ value ∈ edge.children, FreeLE weight bound value ∧ FreeBelow weight bound value) :
    Classified weight bound (run (InternedConstructorTemplates.makeNode edges) state).1 := by
  have selected : ∀ name ∈ (run (InternedConstructorTemplates.makeNode edges) state).1.free,
      weight name ≤ bound ∧ (weight name < bound ∨ bound = 0) := by
    intro name member
    rw [InternedNormalizationFree.makeNode_free edges state facts.coherent facts.linked resident] at member
    obtain ⟨value, member, named⟩ := (childFree_member _ name).mp member
    obtain ⟨edge, member, inside⟩ := List.mem_flatMap.mp member
    have original := (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
    exact ⟨(children edge original value inside).1 name named, (children edge original value inside).2 name named⟩
  refine ⟨fun name member => (selected name member).1, ?_⟩
  intro name member
  rw [InternedDeepFreeNormalization.makeNode_deep edges state facts.coherent facts.linked resident] at member
  exact (selected name member).2

/-- Every actual union branch keeps the free and deep bounds of its literal operands. -/
theorem makeUnion (weight : Reference → Nat) (bound : Nat) (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (normal : Normal state) (available : ∀ value ∈ values, Available state value)
    (classified : ∀ value ∈ values, Classified weight bound value) :
    Classified weight bound (run (InternedConstructorTemplates.makeUnion values) state).1 := by
  constructor
  · intro name member
    obtain ⟨value, member, named⟩ := (InternedNormalizationFree.makeUnion_free values state normal.facts.coherent
      normal.facts.cached normal.facts.linked normal.live available name).mp member
    exact (classified value member).free name named
  · intro name member
    obtain ⟨value, member, named⟩ := (InternedDeepFreeNormalization.makeUnion_deep values state normal.facts.coherent
      normal.facts.cached normal.facts.linked normal.live available name).mp member
    exact (classified value member).deep name named

private theorem filter_free_subset (localName : Reference) (value : Value Symbol Guard)
    (state : State Symbol Guard) (normal : Normal state) (available : Available state value)
    (name : Reference) (member : name ∈ (run (withoutSelfReference localName value) state).1.free) : name ∈ value.free := by
  by_cases same : name = localName
  · subst name
    by_cases bare : value = .reference localName
    · simpa [bare, withoutSelfReference, run, Value.free] using member
    · exact InternedDeepFreeNormalization.deep_free value state normal.facts.coherent available localName
        ((InternedDeepFreeDepth.filter_free localName value state normal available bare).mp member)
  · exact (InternedNormalizationFree.filter_free_other localName name value state normal.facts.coherent
      normal.facts.cached normal.facts.linked normal.live available same).mp member

/-- Actual root filtering retains the same ranked classification. -/
theorem filter (weight : Reference → Nat) (bound : Nat) (localName : Reference) (value : Value Symbol Guard)
    (state : State Symbol Guard) (normal : Normal state) (available : Available state value)
    (classified : Classified weight bound value) :
    Classified weight bound (run (withoutSelfReference localName value) state).1 := by
  refine ⟨fun name member => classified.free name (filter_free_subset localName value state normal available name member), ?_⟩
  intro name member
  exact classified.deep name ((InternedDeepFreeNormalization.filter_deep localName name value state normal available).mp member)

/-- Actual root filtering retains the input's finite constraint depth. -/
theorem filter_cap (annotation : Guard → Prop) (depth : Nat) (localName : Reference) (value : Value Symbol Guard)
    (state : State Symbol Guard) (normal : Normal state) (available : Available state value)
    (bounded : SourceCurrentConstrainedCap.Cap annotation depth value) :
    SourceCurrentConstrainedCap.Cap annotation depth (run (withoutSelfReference localName value) state).1 := by
  cases value with
  | empty | reference | node | mu => exact bounded
  | union entry members level free =>
      unfold withoutSelfReference
      split
      · apply SourceCurrentConstrainedCap.makeUnion annotation depth _ state normal.facts
        · intro value member
          exact available.children value (List.mem_filter.mp member).1
        · intro value member
          exact SourceCurrentConstrainedCap.union_member bounded value (List.mem_filter.mp member).1
      · exact bounded

/-- A maximal local yields the filtered body or empty; smart cleanup retains no new Mu. -/
theorem finish_filtered (weight : Reference → Nat) (bound : Nat) (annotation : Guard → Prop) (depth : Nat)
    (entry : Interned NodeKey) (value probe ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (normal : Normal state) (available : Available state value) (classified : Classified weight bound value)
    (positive : 0 < bound) (maximal : bound ≤ weight (.interned entry.identity))
    (bounded : SourceCurrentConstrainedCap.Cap annotation depth value) :
    let filtered := (run (withoutSelfReference (.interned entry.identity) value) state).1
    let result := InternedNestedConstruction.finish true (.mu entry filtered probe ordinary)
    (result = filtered ∨ result = .empty) ∧
      Classified weight bound result ∧ SourceCurrentConstrainedCap.Cap annotation depth result := by
  dsimp only
  by_cases bare : value = .reference (.interned entry.identity)
  · subst value
    simp only [withoutSelfReference, run, InternedNestedConstruction.finish, Bool.true_eq, ↓reduceIte, cleanup,
      Value.free, List.mem_singleton, Value.referenceOf, beq_self_eq_true]
    exact ⟨.inr rfl, empty weight bound, .plain depth .empty⟩
  · have absent : .interned entry.identity ∉ (run (withoutSelfReference (.interned entry.identity) value) state).1.free := by
      intro member
      exact classified.not_deep positive (.interned entry.identity) maximal
        ((InternedDeepFreeDepth.filter_free _ value state normal available bare).mp member)
    have same : InternedNestedConstruction.finish true
        (.mu entry (run (withoutSelfReference (.interned entry.identity) value) state).1 probe ordinary) =
        (run (withoutSelfReference (.interned entry.identity) value) state).1 := by
      simp [InternedNestedConstruction.finish, cleanup, absent]
    rw [same]
    exact ⟨.inl rfl, filter weight bound _ value state normal available classified,
      filter_cap annotation depth _ value state normal available bounded⟩

end Constructors
end MicroCFTA.SourceCurrentConstrainedCapPairOccurrences
