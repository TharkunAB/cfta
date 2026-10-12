import MicroCFTA.EqualityRawLeafCompiler
import MicroCFTA.EqualityOrdinaryReadback

/-!
# Exact finite raw projection unions

Each physical operand represents an original finite raw leaf. Actual source
union removes empty operands and duplicate identities. Complete outgoing
keys and reconstructed records give exact finite-carrier correspondence.
-/
namespace MicroCFTA.EqualityRawLeafUnion
open InternedConstructorTemplates InternedRecordCoherence InternedEdgeResidency
open InternedFreshProbeKeys InternedProbeProvenance EqualityLeafProjectionPhysical
open EqualityLeafProjectionCompileAvailability EqualityLeafProjectionRepresentation
open EqualityRawLeafInventory (Leaf)
open EqualityRawLeafConstruction (ConstraintKey)
open EqualityRawLeafCompiler (build)
open EqualityOrdinaryReadback

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- Projection union retains each complete alternative from any selected input. -/
def union (leaves : List (Leaf initial symbols)) : Leaf initial symbols :=
  fun symbol row => ∃ leaf ∈ leaves, leaf symbol row

/-- Actual raw leaf construction reconstructs exactly from its outgoing records. -/
theorem build_normal (leaf : Leaf initial symbols) (state : State (Fin symbols) ConstraintKey) (facts : Facts state) :
    Normal (run (build leaf) state).2 (run (build leaf) state).1 := by
  let declarations := EqualityRawLeafConstruction.declarations (EqualityRawLeafInventory.rawChoices leaf)
  let rows := run (EqualityLeafProjectionWorkers.sequence (EqualityRawLeafConstruction.requests declarations)) state
  have rowFacts := EqualityRawLeafAvailability.rows_available declarations state facts
  have builtFacts := EqualityRawLeafCompiler.leaves_available leaf state facts
  simp only [build, EqualityRawLeafConstruction.build, run_bind] at builtFacts ⊢
  change Normal (run (makeNode rows.1) rows.2).2 (run (makeNode rows.1) rows.2).1
  exact makeNode_normal rows.1 rows.2 _ rowFacts.1.coherent rowFacts.1.linked builtFacts.1.coherent
    (fun edge member => (rowFacts.2 edge member).1) (grows_refl _)

/-- A represented raw leaf derives all physical ordinary-union premises. -/
theorem represented_fields (leaf : Leaf initial symbols) (value : Value (Fin symbols) ConstraintKey)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (represented : Represents build (.leaf leaf) state value) :
    Resident state value ∧ Normal state value ∧ EqualityLeafProjectionUnion.OrdinaryRoot value ∧
      ∀ edge ∈ nodeEdges value, dead edge = false := by
  have exactInput : run (build leaf) state = (value, state) := represented
  have available := EqualityRawLeafCompiler.leaves_available leaf state facts
  have normal := build_normal leaf state facts
  have root := EqualityRawLeafAvailability.built_root
    (EqualityRawLeafConstruction.declarations (EqualityRawLeafInventory.rawChoices leaf)) state facts
  change EqualityLeafProjectionUnion.OrdinaryRoot (run (build leaf) state).1 at root
  have nullary := EqualityRawLeafAvailability.built_nullary (EqualityRawLeafInventory.rawChoices leaf) state facts
  change ∀ edge ∈ nodeEdges (run (build leaf) state).1, edge.children = [] at nullary
  rw [exactInput] at available normal root nullary
  exact ⟨available.2.resident, normal, root, fun edge member => by simp only [dead, nullary edge member, List.any_nil]⟩

/-- Every represented raw input has the exact finite-carrier outgoing-key set. -/
theorem represented_keys (leaf : Leaf initial symbols) (value : Value (Fin symbols) ConstraintKey)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (represented : Represents build (.leaf leaf) state value) (key : EdgeKey (Fin symbols) ConstraintKey) :
    (∃ edge ∈ nodeEdges value, edge.entry.key = key) ↔
      ∃ symbol row, leaf symbol row ∧ EqualityRawLeafConstruction.key (symbol, row.val.val) = key := by
  have checked := EqualityRawLeafCompiler.build_keys leaf state facts key
  have exactInput : run (build leaf) state = (value, state) := represented
  simpa only [exactInput] using checked

/-- Operand representations derive ordinary-union facts for the actual ordered value list. -/
theorem operand_fields (inputs : List (Leaf initial symbols × Value (Fin symbols) ConstraintKey))
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (represented : ∀ pair ∈ inputs, Represents build (.leaf pair.1) state pair.2) :
    ∀ value ∈ inputs.map Prod.snd, Resident state value ∧ Normal state value ∧
      EqualityLeafProjectionUnion.OrdinaryRoot value ∧ ∀ edge ∈ nodeEdges value, dead edge = false := by
  intro value member
  obtain ⟨pair, present, rfl⟩ := List.mem_map.mp member
  exact represented_fields pair.1 pair.2 state facts (represented pair present)

/-- Source projection union has exactly the full keys of the finite predicate union. -/
theorem union_keys (inputs : List (Leaf initial symbols × Value (Fin symbols) ConstraintKey))
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (represented : ∀ pair ∈ inputs, Represents build (.leaf pair.1) state pair.2)
    (key : EdgeKey (Fin symbols) ConstraintKey) :
    (∃ edge ∈ nodeEdges (run (makeUnion (inputs.map Prod.snd)) state).1, edge.entry.key = key) ↔
      ∃ symbol row, union (inputs.map Prod.fst) symbol row ∧ EqualityRawLeafConstruction.key (symbol, row.val.val) = key := by
  have checked := operand_fields inputs state facts represented
  rw [EqualityLeafProjectionUnion.union_keys _ state facts.coherent facts.linked
    (fun value member => (checked value member).1) (fun value member => (checked value member).2.2.1)
    (fun value member => (checked value member).2.2.2)]
  constructor
  · rintro ⟨value, member, selected⟩
    obtain ⟨pair, present, rfl⟩ := List.mem_map.mp member
    obtain ⟨symbol, row, member, same⟩ := (represented_keys pair.1 pair.2 state facts (represented pair present) key).mp selected
    exact ⟨symbol, row, ⟨pair.1, List.mem_map.mpr ⟨pair, present, rfl⟩, member⟩, same⟩
  · rintro ⟨symbol, row, ⟨leaf, member, selected⟩, same⟩
    obtain ⟨pair, present, rfl⟩ := List.mem_map.mp member
    exact ⟨pair.2, List.mem_map.mpr ⟨pair, present, rfl⟩,
      (represented_keys pair.1 pair.2 state facts (represented pair present) key).mpr ⟨symbol, row, selected, same⟩⟩

/-- Actual physical projection union and compiled finite union return the same complete record. -/
theorem union_record (inputs : List (Leaf initial symbols × Value (Fin symbols) ConstraintKey))
    (state resultState after : State (Fin symbols) ConstraintKey)
    (facts : Facts state) (resultFacts : Facts resultState) (afterFacts : Facts after)
    (represented : ∀ pair ∈ inputs, Represents build (.leaf pair.1) state pair.2)
    (unionGrowth : Grows (run (makeUnion (inputs.map Prod.snd)) state).2 after)
    (resultGrowth : Grows (run (build (union (inputs.map Prod.fst))) resultState).2 after) :
    (run (makeUnion (inputs.map Prod.snd)) state).1 = (run (build (union (inputs.map Prod.fst))) resultState).1 := by
  have checked := operand_fields inputs state facts represented
  have available : ∀ value ∈ inputs.map Prod.snd, Available state value := by
    intro value member
    obtain ⟨pair, present, rfl⟩ := List.mem_map.mp member
    exact EqualityLeafProjectionRepresentation.available build EqualityRawLeafCompiler.leaves_available
      (.leaf pair.1) state facts pair.2 (represented pair present)
  have joined := makeUnion_available (inputs.map Prod.snd) state facts.coherent facts.cached available
  have built := EqualityRawLeafCompiler.leaves_available (union (inputs.map Prod.fst)) resultState resultFacts
  have leftNormal := makeUnion_normal _ state facts.coherent facts.linked
    (fun value member => (checked value member).1) (fun value member => (checked value member).2.2.1)
    (fun value member => (checked value member).2.1)
  have rightNormal := build_normal (union (inputs.map Prod.fst)) resultState resultFacts
  apply keys_ext after afterFacts.coherent _ _
    (normal_grows _ after joined.1.valid unionGrowth _ leftNormal)
    (normal_grows _ after built.1.coherent.valid resultGrowth _ rightNormal)
    (resident_edges after afterFacts.linked _ (resident_grows _ after unionGrowth _ joined.2.2.resident))
    (resident_edges after afterFacts.linked _ (resident_grows _ after resultGrowth _ built.2.resident))
  intro key
  rw [union_keys inputs state facts represented key,
    EqualityRawLeafCompiler.build_keys (union (inputs.map Prod.fst)) resultState resultFacts key]

/-- Actual union execution constructs a finite later cache for the exact projected leaf representation. -/
theorem union_completed (inputs : List (Leaf initial symbols × Value (Fin symbols) ConstraintKey))
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (represented : ∀ pair ∈ inputs, Represents build (.leaf pair.1) state pair.2) :
    let actual := run (makeUnion (inputs.map Prod.snd)) state
    let prepared := run (build (union (inputs.map Prod.fst))) actual.2
    Facts prepared.2 ∧ Grows actual.2 prepared.2 ∧
      Represents build (.leaf (union (inputs.map Prod.fst))) prepared.2 actual.1 := by
  let actual := run (makeUnion (inputs.map Prod.snd)) state
  let prepared := run (build (union (inputs.map Prod.fst))) actual.2
  have available : ∀ value ∈ inputs.map Prod.snd, Available state value := by
    intro value member
    obtain ⟨pair, present, rfl⟩ := List.mem_map.mp member
    exact EqualityLeafProjectionRepresentation.available build EqualityRawLeafCompiler.leaves_available
      (.leaf pair.1) state facts pair.2 (represented pair present)
  have actualAvailable := makeUnion_available _ state facts.coherent facts.cached available
  have actualFacts : Facts actual.2 := ⟨actualAvailable.1, actualAvailable.2.1,
    makeUnion_linked _ state facts.linked available⟩
  have preparedFacts := EqualityRawLeafCompiler.leaves_available (union (inputs.map Prod.fst)) actual.2 actualFacts
  have growth : Grows actual.2 prepared.2 := (InternedConstructorTemplates.run_correct _ actual.2 actualFacts.coherent.valid).2
  have same := union_record inputs state actual.2 prepared.2 facts actualFacts preparedFacts.1 represented growth (grows_refl _)
  change actual.1 = prepared.1 at same
  refine ⟨preparedFacts.1, growth, ?_⟩
  change run (build (union (inputs.map Prod.fst))) prepared.2 = (actual.1, prepared.2)
  rw [same]
  exact replay (build (union (inputs.map Prod.fst))) actual.2 prepared.2 actualFacts.coherent.valid (grows_refl _)

end MicroCFTA.EqualityRawLeafUnion
