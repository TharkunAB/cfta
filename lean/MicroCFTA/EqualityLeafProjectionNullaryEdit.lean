import MicroCFTA.EqualityLeafProjectionRequireExact
import MicroCFTA.EqualityRawLeafUnion

/-!
# Exact edits below a nullary source leaf

A descendant-only edit has no child position to change. Actual resident
edge requests and normal parent reconstruction therefore replay the same
complete leaf record without allocation.
-/
namespace MicroCFTA.EqualityLeafProjectionNullaryEdit
open Cache InternedConstructorTemplates InternedRecordCoherence InternedEdgeResidency InternedProbeProvenance
open EqualityLeafProjectionSyntax (Path atRoot)
open EqualityLeafProjectionWorkers EqualityLeafProjectionPhysical EqualityOrdinaryReadback
open EqualityLeafProjectionCompileAvailability EqualityLeafProjectionRepresentation

/-- Rebuilding a resident edge with its complete current fields is an exact cache hit. -/
theorem resident_edge_replay [DecidableEq (EdgeKey Symbol Guard)]
    (edge : EdgeValue Symbol Guard) (state : State Symbol Guard) (coherent : Coherent state) (resident : EdgeResident state edge) :
    run (makeEdge edge.entry.key.symbol edge.entry.key.constraint edge.children) state = (edge, state) := by
  have checked := coherent.edges edge.entry.key edge resident
  have key : (⟨edge.entry.key.symbol, edge.children.map Value.referenceOf, edge.entry.key.constraint⟩ : EdgeKey Symbol Guard) = edge.entry.key := by
    have children := checked.2.2
    cases source : edge.entry.key with
    | mk symbol values guard =>
        simp only [source] at children ⊢
        rw [children]
  have recorded : state.edgeRecords edge.entry.key = some edge := resident
  simp only [makeEdge, run, edgeStep, key, Cache.intern, checked.1, keepFirst, recorded, Option.getD_some]

/-- Actual nullary edge editing returns the identical ordered records without allocation. -/
theorem editEdges_nullary [DecidableEq (EdgeKey Symbol Guard)]
    (meet : Target → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard)) (edits : List (Path × Target))
    (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard) (coherent : Coherent state)
    (resident : ∀ edge ∈ edges, EdgeResident state edge) (nullary : ∀ edge ∈ edges, edge.children = []) :
    run (editEdges meet edits edges) state = (some edges, state) := by
  induction edges with
  | nil => rfl
  | cons edge rest ih =>
      cases edge with
      | mk entry children =>
          have empty : children = [] := nullary (.mk entry children) (by simp)
          subst children
          have head := resident_edge_replay (.mk entry []) state coherent (resident _ (by simp))
          change run (makeEdge entry.key.symbol entry.key.constraint []) state = (.mk entry [], state) at head
          have tail := ih (fun edge member => resident edge (by simp [member])) (fun edge member => nullary edge (by simp [member]))
          simp only [editEdges, editChildren, bindOptional, run_bind, run, head, tail]

/-- Descendant-only edits leave every normalized nullary source node exactly unchanged. -/
theorem below_leaf [DecidableEq (EdgeKey Symbol Guard)]
    (meet : Target → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard)) (edits : List (Path × Target))
    (noRoot : atRoot edits = none) (value : Value Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (ordinary : EqualityLeafProjectionUnion.OrdinaryRoot value)
    (normal : Normal state value) (resident : ∀ edge ∈ nodeEdges value, EdgeResident state edge)
    (nullary : ∀ edge ∈ nodeEdges value, edge.children = []) :
    run (edit meet edits value) state = (some value, state) := by
  cases edits with
  | nil => simp only [edit_unselected, run]
  | cons first rest =>
      cases value with
      | empty => simp only [edit_empty, run]
      | reference | union | mu => simp only [EqualityLeafProjectionUnion.OrdinaryRoot] at ordinary
      | node entry edges depth free =>
          have rows := editEdges_nullary meet (first :: rest) edges state coherent resident nullary
          have parent : run (makeNode edges) state = (.node entry edges depth free, state) := normal
          simp only [edit, noRoot, bindOptional, run_bind, rows, parent, run]

noncomputable local instance : DecidableEq EqualityLeafProjectionLeafCache.ConstraintKey := by classical exact inferInstance

/-- The represented finite raw leaf discharges every physical nullary edit premise. -/
theorem represented_raw_below
    (leaf : EqualityRawLeafInventory.Leaf initial symbols)
    (meet : Target → Value (Fin symbols) EqualityLeafProjectionLeafCache.ConstraintKey →
      Work (Fin symbols) EqualityLeafProjectionLeafCache.ConstraintKey (Value (Fin symbols) EqualityLeafProjectionLeafCache.ConstraintKey))
    (edits : List (Path × Target)) (noRoot : atRoot edits = none)
    (value : Value (Fin symbols) EqualityLeafProjectionLeafCache.ConstraintKey)
    (state : State (Fin symbols) EqualityLeafProjectionLeafCache.ConstraintKey) (facts : Facts state)
    (represented : Represents EqualityRawLeafCompiler.build (.leaf leaf) state value) :
    run (edit meet edits value) state = (some value, state) := by
  have fields := EqualityRawLeafUnion.represented_fields leaf value state facts represented
  have closed : run (EqualityRawLeafCompiler.build leaf) state = (value, state) := represented
  have nullary := EqualityRawLeafAvailability.built_nullary (EqualityRawLeafInventory.rawChoices leaf) state facts
  change ∀ edge ∈ nodeEdges (run (EqualityRawLeafCompiler.build leaf) state).1, edge.children = [] at nullary
  rw [closed] at nullary
  exact below_leaf meet edits noRoot value state facts.coherent fields.2.2.1 fields.2.1
    (resident_edges state facts.linked value fields.1) nullary

end MicroCFTA.EqualityLeafProjectionNullaryEdit
