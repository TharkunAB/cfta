import MicroCFTA.EqualityLeafProjectionSetChildren

/-!
# Closed metadata for actual ordinary occurrence records

Coherent available ordinary records have zero stored Mu depth and no free
references. These are the exact source fast-path fields used by recursive
constraint detection and the closed self-intersection shortcut.
-/
namespace MicroCFTA.EqualityLeafProjectionOrdinaryMetadata
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys
open EqualityLeafProjectionWorkers
open EqualityLeafProjectionCompileAvailability EqualityLeafProjectionRepresentation

/-- Structural ordinary child lists expose the predicate at every actual position. -/
theorem ordinary_child (children : List (Value Symbol Guard)) (ordinary : OrdinaryChildren children)
    (child : Value Symbol Guard) (member : child ∈ children) : Ordinary child := by
  induction children with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | present
      · exact ordinary.1
      · exact ih ordinary.2 present

/-- Structural ordinary rows expose every complete stored child. -/
theorem ordinary_edge_child (edges : List (EdgeValue Symbol Guard)) (ordinary : OrdinaryEdges edges)
    (edge : EdgeValue Symbol Guard) (member : edge ∈ edges) (child : Value Symbol Guard) (present : child ∈ edge.children) : Ordinary child := by
  induction edges with
  | nil => cases member
  | cons first rest ih =>
      cases first with
      | mk entry children =>
          rcases List.mem_cons.mp member with rfl | later
          · exact ordinary_child children ordinary.1 child present
          · exact ih ordinary.2 later

/-- Zero-depth closed children give zero-depth closed parent metadata. -/
theorem children_metadata (children : List (Value Symbol Guard))
    (closed : ∀ child ∈ children, child.depth = 0 ∧ child.free = []) :
    maximumDepth children = 0 ∧ childFree children = [] := by
  constructor
  · induction children with
    | nil => rfl
    | cons first rest ih =>
        have head := (closed first (by simp)).1
        have tail := ih (fun child member => closed child (by simp [member]))
        simpa only [maximumDepth, List.map_cons, List.foldl_cons, head, Nat.max_self] using tail
  · have noFree : children.flatMap Value.free = [] := by
      apply List.flatMap_eq_nil_iff.mpr
      intro child member
      exact (closed child member).2
    simp [childFree, noFree, canonicalFree]

/-- Coherent available ordinary records have exactly the source closed fast-path metadata. -/
theorem ordinary_metadata (value : Value Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (available : Available state value) (ordinary : Ordinary value) :
    value.depth = 0 ∧ value.free = [] := by
  cases value with
  | empty => exact ⟨rfl, rfl⟩
  | reference | union | mu => cases ordinary
  | node entry edges depth free =>
      have stored := available.resident entry rfl
      obtain ⟨actual, present, fields⟩ := facts.coherent.nodes entry.key _ stored
      have children : ∀ child ∈ edges.flatMap EdgeValue.children, child.depth = 0 ∧ child.free = [] := by
        intro child member
        obtain ⟨edge, included, selected⟩ := List.mem_flatMap.mp member
        exact ordinary_metadata child state facts
          (available.children child (List.mem_flatMap.mpr ⟨edge, included, selected⟩))
          (ordinary_edge_child edges ordinary edge included child selected)
      have metadata := children_metadata _ children
      exact ⟨fields.2.2.1.trans metadata.1, fields.2.2.2.trans metadata.2⟩
termination_by sizeOf value
decreasing_by
  have edgeSmall := List.sizeOf_lt_of_mem included
  cases edge with
  | mk stored children =>
      have childSmall := List.sizeOf_lt_of_mem selected
      simp only [EdgeValue.children] at childSmall
      simp_wf
      simp only [EdgeValue.mk.sizeOf_spec] at edgeSmall
      subst value
      simp only [Value.node.sizeOf_spec]
      omega

noncomputable local instance : DecidableEq EqualityLeafProjectionLeafCache.ConstraintKey := by classical exact inferInstance

/-- Every represented finite raw occurrence satisfies the source closed fast-path metadata test. -/
theorem represented_metadata
    (tree : EqualityLeafProjectionSyntax.Tree
      (EqualityLeafProjectionCompile.Tag (Fin symbols) EqualityLeafProjectionLeafCache.ConstraintKey)
      (EqualityRawLeafInventory.Leaf initial symbols))
    (state : State (Fin symbols) EqualityLeafProjectionLeafCache.ConstraintKey) (facts : Facts state)
    (value : Value (Fin symbols) EqualityLeafProjectionLeafCache.ConstraintKey)
    (represented : Represents EqualityRawLeafCompiler.build tree state value) : value.depth = 0 ∧ value.free = [] := by
  have ordinary := EqualityLeafProjectionCompileOrdinary.compile_ordinary EqualityRawLeafCompiler.build
    EqualityRawLeafCompiler.leaves_available EqualityRawLeafCompiler.leaves_ordinary tree state facts
  rw [represented] at ordinary
  exact ordinary_metadata value state facts
    (EqualityLeafProjectionRepresentation.available EqualityRawLeafCompiler.build EqualityRawLeafCompiler.leaves_available tree state facts value represented)
    ordinary

/-- The source checks reference and union constructors before its closed metadata fast path. -/
def clearFastPath (value : Value Symbol Guard) : Bool :=
  match value with
  | .reference _ | .union _ _ _ _ => false
  | _ => value.depth == 0 && value.free.isEmpty

/-- Actual ordinary records always reach the source's immediate unconstrained-recursion result. -/
theorem ordinary_fast_path (value : Value Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (available : Available state value) (ordinary : Ordinary value) : clearFastPath value = true := by
  have metadata := ordinary_metadata value state facts available ordinary
  cases value with
  | reference | union | mu => cases ordinary
  | empty => rfl
  | node => simp only [clearFastPath, metadata.1, metadata.2, List.isEmpty_nil, Bool.and_true, beq_self_eq_true]

/-- Every root in a represented finite raw forest supplies the source recursion-filter fast path. -/
theorem represented_forest_fast_path
    (forest : List (EqualityLeafProjectionSyntax.Tree
      (EqualityLeafProjectionCompile.Tag (Fin symbols) EqualityLeafProjectionLeafCache.ConstraintKey)
      (EqualityRawLeafInventory.Leaf initial symbols)))
    (state : State (Fin symbols) EqualityLeafProjectionLeafCache.ConstraintKey) (facts : Facts state)
    (values : List (Value (Fin symbols) EqualityLeafProjectionLeafCache.ConstraintKey))
    (represented : RepresentsForest EqualityRawLeafCompiler.build forest state values) :
    ∀ value ∈ values, clearFastPath value = true := by
  have ordinary := EqualityLeafProjectionCompileOrdinary.compileForest_ordinary EqualityRawLeafCompiler.build
    EqualityRawLeafCompiler.leaves_available EqualityRawLeafCompiler.leaves_ordinary forest state facts
  rw [represented] at ordinary
  have available := forest_available EqualityRawLeafCompiler.build EqualityRawLeafCompiler.leaves_available forest state facts values represented
  intro value member
  exact ordinary_fast_path value state facts (available value member) (ordinary value member)

end MicroCFTA.EqualityLeafProjectionOrdinaryMetadata
