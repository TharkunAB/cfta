import MicroCFTA.SourceRecursiveIntersectionInputIdentity
import MicroCFTA.SourceRecursiveIntersectionInputCopy
import MicroCFTA.SourcePhysicalSharedRowsLanguage

/-!
# Original physical syntax and independent input languages

Physical syntax retains ordered children, complete guards, and least recursive
binders. Independent input derivations use the actual tagged physical view.
-/
namespace MicroCFTA.SourceRecursiveIntersectionInputView
open Cache Binding BinderLanguage InternedConstructorTemplates InternedProbeProvenance
open InternedFreshProbeKeys InternedBinderProtocol InternedNestedFacts IntersectSchedule Language

/-- Copied member lists retain their exact order and multiplicity. -/
theorem shapeValues_map (holds : Guard → Term Symbol → Bool) (values : List (Value Symbol Guard)) :
    shapeValues holds values = values.map (shape holds) := by
  induction values with
  | nil => simp [shapeValues]
  | cons first rest ih => simp [shapeValues, ih]

/-- Copied row lists retain their exact order and multiplicity. -/
theorem shapeEdges_map (holds : Guard → Term Symbol → Bool) (edges : List (EdgeValue Symbol Guard)) :
    shapeEdges holds edges = edges.map (shapeEdge holds) := by
  induction edges with
  | nil => simp [shapeEdges]
  | cons first rest ih => simp [shapeEdges, ih]

/-- Copied physical forests have exactly the corresponding ordered child meanings. -/
theorem shapeValues_meaning (holds : Guard → Term Symbol → Bool) (environment : Env Symbol)
    (values : List (Value Symbol Guard)) (terms : List (Term Symbol)) :
    forest environment (shapeValues holds values) terms ↔
      All₂ (fun value term => meaning environment (shape holds value) term) values terms := by
  induction values generalizing terms with
  | nil =>
      cases terms with
      | nil => simp only [shapeValues, forest]; exact ⟨fun _ => .nil, fun _ => trivial⟩
      | cons term terms => simp only [shapeValues, forest]; constructor <;> intro impossible <;> cases impossible
  | cons first rest ih =>
      cases terms with
      | nil => simp only [shapeValues, forest]; constructor <;> intro impossible <;> cases impossible
      | cons term terms =>
          simp only [shapeValues, forest, ih]
          constructor
          · rintro ⟨head, tail⟩; exact .cons head tail
          · intro accepted; cases accepted with | cons head tail => exact ⟨head, tail⟩

/-- Copied physical nodes have exactly their original guarded row and child meanings. -/
theorem shape_node_meaning (holds : Guard → Term Symbol → Bool) (environment : Env Symbol)
    (entry : Interned NodeKey) (edges : List (EdgeValue Symbol Guard)) (depth : Nat) (free : List Reference) (term : Term Symbol) :
    meaning environment (shape holds (.node entry edges depth free)) term ↔
      ∃ edge ∈ edges, ∃ terms, term = .node edge.entry.key.symbol terms ∧
        All₂ (fun child term => meaning environment (shape holds child) term) edge.children terms ∧
        holds edge.entry.key.constraint term = true := by
  simp only [shape, meaning, shapeEdges_map]
  constructor
  · rintro ⟨⟨selected, present⟩, accepted⟩
    obtain ⟨edge, inEdges, rfl⟩ := List.mem_map.mp present
    change meaning environment (shapeEdge holds edge) term at accepted
    simp only [shapeEdge, meaning] at accepted
    obtain ⟨terms, same, children, guard⟩ := accepted
    exact ⟨edge, inEdges, terms, same, (shapeValues_meaning holds environment edge.children terms).mp children, guard⟩
  · rintro ⟨edge, present, terms, same, children, guard⟩
    refine ⟨⟨shapeEdge holds edge, List.mem_map.mpr ⟨edge, present, rfl⟩⟩, ?_⟩
    change meaning environment (shapeEdge holds edge) term
    simp only [shapeEdge, meaning]
    exact ⟨terms, same, (shapeValues_meaning holds environment edge.children terms).mpr children, guard⟩

/-- Copied physical unions have exactly their original member meanings. -/
theorem shape_union_meaning (holds : Guard → Term Symbol → Bool) (environment : Env Symbol)
    (entry : Interned NodeKey) (members : List (Value Symbol Guard)) (depth : Nat) (free : List Reference) (term : Term Symbol) :
    meaning environment (shape holds (.union entry members depth free)) term ↔
      ∃ member ∈ members, meaning environment (shape holds member) term := by
  simp only [shape, meaning, shapeValues_map]
  constructor
  · rintro ⟨⟨selected, present⟩, accepted⟩
    obtain ⟨member, inMembers, rfl⟩ := List.mem_map.mp present
    exact ⟨member, inMembers, accepted⟩
  · rintro ⟨member, present, accepted⟩
    exact ⟨⟨shape holds member, List.mem_map.mpr ⟨member, present, rfl⟩⟩, accepted⟩

/-- Original physical Mu readback selects its actual stored body. -/
theorem body_readback (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Term Symbol → Bool) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (available : Available state (.mu entry body depth ordinary)) :
    (view state holds).body entry.identity = inputOf body := by
  simp only [view, payload_readback state facts _ available (.mu entry.identity) rfl]

/-- Original physical node readback selects its actual ordered rows. -/
theorem rows_readback (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Term Symbol → Bool) (entry : Interned NodeKey) (edges : List (EdgeValue Symbol Guard))
    (depth : Nat) (free : List Reference) (available : Available state (.node entry edges depth free)) :
    (view state holds).rows entry.identity = edges.map (row holds) := by
  simp only [view, payload_readback state facts _ available (.node entry.identity) rfl]

/-- Original physical union readback selects its actual ordered members. -/
theorem members_readback (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Term Symbol → Bool) (entry : Interned NodeKey) (members : List (Value Symbol Guard))
    (depth : Nat) (free : List Reference) (available : Available state (.union entry members depth free)) :
    (view state holds).members entry.identity = members.map inputOf := by
  simp only [view, payload_readback state facts _ available (.union entry.identity) rfl]

/-- Erase the finite unfolding bound from independent actual input derivations. -/
def InputLanguage (state : InternedConstructorTemplates.State Symbol Guard) (holds : Guard → Term Symbol → Bool)
    (input : Input) : Lang Symbol := fun term => ∃ rank, InputDerivation (view state holds) input rank term

/-- Sound free environments contain only terms with independent finite reference derivations. -/
def SoundEnvironment (state : InternedConstructorTemplates.State Symbol Guard) (holds : Guard → Term Symbol → Bool)
    (value : Value Symbol Guard) (environment : Env Symbol) : Prop :=
  ∀ name ∈ freeNames value, Included (environment name) (InputLanguage state holds (.ref name))

/-- Complete free environments contain every reference derivation through the stated finite rank. -/
def CompleteEnvironment (state : InternedConstructorTemplates.State Symbol Guard) (holds : Guard → Term Symbol → Bool)
    (value : Value Symbol Guard) (rank : Nat) (environment : Env Symbol) : Prop :=
  ∀ name ∈ freeNames value, ∀ smaller, smaller ≤ rank → ∀ term,
    InputDerivation (view state holds) (.ref name) smaller term → environment name term

/-- Every actual node child's free name is free in its coherent cached parent. -/
theorem node_free_child (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (entry : Interned NodeKey) (edges : List (EdgeValue Symbol Guard)) (depth : Nat) (free : List Reference)
    (available : Available state (.node entry edges depth free)) (edge : EdgeValue Symbol Guard) (present : edge ∈ edges)
    (child : Value Symbol Guard) (member : child ∈ edge.children) (name : Nat) (named : name ∈ freeNames child) :
    name ∈ freeNames (.node entry edges depth free) :=
  (node_free_member state facts entry edges depth free available name).mpr ⟨edge, present, child, member, named⟩

/-- Every actual union member's free name is free in its coherent cached parent. -/
theorem union_free_child (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (entry : Interned NodeKey) (members : List (Value Symbol Guard)) (depth : Nat) (free : List Reference)
    (available : Available state (.union entry members depth free)) (child : Value Symbol Guard) (member : child ∈ members)
    (name : Nat) (named : name ∈ freeNames child) : name ∈ freeNames (.union entry members depth free) := by
  rw [freeNames_member]
  simp only [Value.free, InternedNormalizationFree.union_free state facts.coherent entry members depth free available.resident,
    childFree_member]
  exact ⟨child, member, (freeNames_member child name).mp named⟩

/-- Original Mu cached free names remove exactly their own interned recursion name. -/
theorem mu_free_member (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) (name : Nat) :
    name ∈ freeNames (.mu entry body depth ordinary) ↔ name ∈ freeNames body ∧ name ≠ entry.identity := by
  rw [freeNames_member, freeNames_member]
  simp [Value.free]

end MicroCFTA.SourceRecursiveIntersectionInputView
