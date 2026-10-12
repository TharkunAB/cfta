import MicroCFTA.EqualityLeafProjectionAdmission
import MicroCFTA.EqualityLeafProjectionReplay

/-!
# Physical nullary rows for admitted source leaf domains

Every row request keeps its constructor symbol, empty equality field, and
canonical residual guard. Actual cache readback and duplicate normalization
recover exactly the selected finite leaf alternatives.
-/
namespace MicroCFTA.EqualityLeafProjectionLeafCache
open SourceGuards FullSyntax InternedConstructorTemplates InternedRecordCoherence InternedEdgeResidency
open InternedFreshProbeKeys EqualityLeafProjectionPhysical
open EqualityLeafProjectionWorkers (sequence sequence_safe sequence_completed)

abbrev Row := EqualityLeafProjectionAdmission.Row
abbrev ConstraintKey := Option (List (List (List Nat))) × Guard Formula

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance
abbrev Leaf (initial : List (Guard Formula)) (symbols : Nat) := FiniteLeafSymbolsProgress.Node (Row initial) symbols

/-- Full leaf constraints retain the normalized empty equality field. -/
def constraint (row : Row initial) : ConstraintKey := (some [], row.val.val.val)

/-- Nullary source edge identity includes both the symbol and complete constraint. -/
def key (symbol : Fin symbols) (row : Row initial) : EdgeKey (Fin symbols) ConstraintKey :=
  ⟨symbol, [], constraint row⟩

/-- Different admitted residuals cannot share the same complete nullary edge key. -/
theorem key_injective (firstSymbol secondSymbol : Fin symbols) (first second : Row initial)
    (same : key firstSymbol first = key secondSymbol second) : firstSymbol = secondSymbol ∧ first = second := by
  refine ⟨congrArg EdgeKey.symbol same, ?_⟩
  have constraints := congrArg EdgeKey.constraint same
  have guards := congrArg Prod.snd constraints
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact guards

/-- Enumerate selected rows from the complete finite admitted inventory. -/
noncomputable def choices (leaf : Leaf initial symbols) : List (Fin symbols × Row initial) := by
  classical
  exact (List.ofFn id).flatMap fun symbol =>
    ((EqualityLeafProjectionAdmission.inventory initial).filter (fun row => decide (leaf symbol row))).map (symbol, ·)

/-- The finite occurrence list represents exactly the original row predicate. -/
theorem choices_member (leaf : Leaf initial symbols) (symbol : Fin symbols) (row : Row initial) :
    (symbol, row) ∈ choices leaf ↔ leaf symbol row := by
  classical
  simp only [choices, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨actual, _, original, ⟨_, member⟩, same⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
    exact member
  · intro member
    exact ⟨symbol, by simp, row, ⟨EqualityLeafProjectionAdmission.inventory_complete initial row, member⟩, rfl⟩

/-- The physical source constructor receives one actual nullary edge request per row occurrence. -/
noncomputable def requests (leaf : Leaf initial symbols) : List (Work (Fin symbols) ConstraintKey (EdgeValue (Fin symbols) ConstraintKey)) :=
  (choices leaf).map fun (symbol, row) => makeEdge symbol (constraint row) []

/-- Construct the admitted leaf using the actual separate edge and node caches. -/
noncomputable def build (leaf : Leaf initial symbols) : Work (Fin symbols) ConstraintKey (Value (Fin symbols) ConstraintKey) :=
  (sequence (requests leaf)).bind makeNode

/-- Read a physical leaf alternative by its exact complete nullary source key. -/
def read (value : Value (Fin symbols) ConstraintKey) : Leaf initial symbols :=
  fun symbol row => ∃ edge ∈ nodeEdges value, edge.entry.key = key symbol row

/-- A nullary request returns its literal source key and no child payloads. -/
theorem nullary_fields (symbol : Fin symbols) (row : Row initial)
    (state : State (Fin symbols) ConstraintKey) (coherent : Coherent state) :
    (run (makeEdge symbol (constraint row) []) state).1.entry.key = key symbol row ∧
      (run (makeEdge symbol (constraint row) []) state).1.children = [] := by
  let identify := fun entry => EdgeValue.mk entry ([] : List (Value (Fin symbols) ConstraintKey))
  have correct := edgeStep_correct (key symbol row) identify state coherent.valid
  have after := edgeStep_coherent (key symbol row) identify state coherent (fun _ same => ⟨rfl, same, rfl⟩)
  have fields := (after.edges _ _ correct.2.2).2
  refine ⟨fields.1, ?_⟩
  have noChildren := fields.2
  exact List.map_eq_nil_iff.mp noChildren

/-- Every generated nullary request uses the actual source constructor fields. -/
theorem requests_safe (leaf : Leaf initial symbols) : ∀ request ∈ requests leaf, Safe request := by
  intro request member
  obtain ⟨⟨symbol, row⟩, _, rfl⟩ := List.mem_map.mp member
  exact makeEdge_safe symbol (constraint row) []

/-- Nullary requests preserve physical node-edge links because they do not change any node payload. -/
theorem requests_linked (leaf : Leaf initial symbols) (state : State (Fin symbols) ConstraintKey) (coherent : Coherent state) (linked : Linked state) :
    Linked (run (sequence (requests leaf)) state).2 := by
  generalize found : requests leaf = operations
  have edgeOnly : ∀ request ∈ operations, ∃ symbol row, request = makeEdge symbol (constraint (initial := initial) row) [] := by
    intro request member
    rw [← found] at member
    obtain ⟨⟨symbol, row⟩, _, rfl⟩ := List.mem_map.mp member
    exact ⟨symbol, row, rfl⟩
  clear found
  induction operations generalizing state with
  | nil => exact linked
  | cons first rest ih =>
      obtain ⟨symbol, row, rfl⟩ := edgeOnly first (by simp)
      simp only [sequence, run_bind, run]
      exact ih _ (InternedErasedEdgeReplay.run_coherent _ state (makeEdge_safe _ _ _) coherent)
        (makeEdge_linked symbol (constraint row) [] state coherent linked).1
        (fun request member => edgeOnly request (by simp [member]))

/-- Completed generated rows are resident nullary records and retain their exact selected keys. -/
theorem completed_rows (leaf : Leaf initial symbols) (state : State (Fin symbols) ConstraintKey) (coherent : Coherent state) :
    let result := run (sequence (requests leaf)) state
    Coherent result.2 ∧ (∀ edge ∈ result.1, EdgeResident result.2 edge ∧ edge.children = []) ∧
      ∀ symbol row, (∃ edge ∈ result.1, edge.entry.key = key symbol row) ↔ leaf symbol row := by
  let result := run (sequence (requests leaf)) state
  have after : Coherent result.2 := InternedErasedEdgeReplay.run_coherent _ state (sequence_safe _ (requests_safe leaf)) coherent
  have completed := sequence_completed (requests leaf) state coherent.valid
  have resultEq : result.1 = (choices leaf).map (fun (symbol, row) => (run (makeEdge symbol (constraint row) []) result.2).1) := by
    have base : result.1 = (requests leaf).map (fun request => (run request result.2).1) := completed.1
    rw [requests, List.map_map] at base
    exact base
  refine ⟨after, ?_, ?_⟩
  · intro edge member
    rw [resultEq] at member
    obtain ⟨⟨symbol, row⟩, present, rfl⟩ := List.mem_map.mp member
    have requestMember : makeEdge symbol (constraint row) [] ∈ requests leaf := List.mem_map.mpr ⟨(symbol, row), present, rfl⟩
    have replayed := completed.2 _ requestMember
    have resident := makeEdge_resident symbol (constraint row) [] result.2 after
    rw [replayed] at resident
    exact ⟨resident, (nullary_fields symbol row result.2 after).2⟩
  · intro symbol row
    constructor
    · rintro ⟨edge, member, same⟩
      rw [resultEq] at member
      obtain ⟨⟨actual, original⟩, present, rfl⟩ := List.mem_map.mp member
      have requested := (nullary_fields actual original result.2 after).1
      obtain ⟨rfl, rfl⟩ := key_injective actual symbol original row (requested.symm.trans same)
      exact (choices_member leaf _ _).mp present
    · intro present
      refine ⟨(run (makeEdge symbol (constraint row) []) result.2).1, ?_, (nullary_fields symbol row result.2 after).1⟩
      rw [resultEq]
      exact List.mem_map.mpr ⟨(symbol, row), (choices_member leaf symbol row).mpr present, rfl⟩

/-- Canonical physical node construction decodes to exactly the selected admitted leaf rows. -/
theorem build_read (leaf : Leaf initial symbols) (state : State (Fin symbols) ConstraintKey)
    (coherent : Coherent state) (linked : Linked state) : read (run (build leaf) state).1 = leaf := by
  let rows := run (sequence (requests leaf)) state
  have checked := completed_rows leaf state coherent
  have rowsLinked := requests_linked leaf state coherent linked
  have survives : surviving rows.1 = rows.1 := by
    apply List.filter_eq_self.mpr
    intro edge member
    simp only [(checked.2.1 edge member).2, List.any_nil, Bool.not_false]
  funext symbol row
  apply propext
  change (∃ edge ∈ nodeEdges (run (build leaf) state).1, edge.entry.key = key symbol row) ↔ leaf symbol row
  rw [build, run_bind, makeNode_edges rows.1 rows.2 checked.1 rowsLinked (fun edge member => (checked.2.1 edge member).1), survives]
  rw [← checked.2.2 symbol row]
  constructor
  · rintro ⟨edge, member, same⟩
    exact ⟨edge, InternedProbeProvenance.canonicalEdges_member rows.1 edge member, same⟩
  · rintro ⟨edge, member, same⟩
    exact ⟨edge, canonicalEdges_retains rows.2 checked.1 rows.1 edge (fun edge member => (checked.2.1 edge member).1) member, same⟩

/-- Actual ordinary-node construction returns its complete resident payload. -/
theorem makeNode_resident (edges : List (EdgeValue (Fin symbols) ConstraintKey))
    (state : State (Fin symbols) ConstraintKey) (coherent : Coherent state) :
    Resident (run (makeNode edges) state).2 (run (makeNode edges) state).1 := by
  unfold makeNode
  dsimp only
  split
  · intro entry impossible
    cases impossible
  · rename_i first rest same
    let key := InternedBinderProtocol.NodeKey.node ((first :: rest).map (fun edge => edge.entry.identity))
    let identify := identifyNode (first :: rest)
    have correct := nodeStep_correct key identify state coherent.valid
    have after := nodeStep_coherent key identify state coherent (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩)
    exact stored_resident _ after key _ correct.2.2

/-- The constructed admitted leaf has a canonical resident record. -/
theorem build_resident (leaf : Leaf initial symbols) (state : State (Fin symbols) ConstraintKey)
    (coherent : Coherent state) : Resident (run (build leaf) state).2 (run (build leaf) state).1 := by
  have rowsCoherent := InternedErasedEdgeReplay.run_coherent _ state (sequence_safe _ (requests_safe leaf)) coherent
  simp only [build, run_bind]
  exact makeNode_resident _ _ rowsCoherent

/-- In a common cache, the physical whole-node identity test equals equality
of the complete admitted leaf row predicates. It is not a per-symbol test. -/
theorem identity_iff (first second : Leaf initial symbols)
    (leftState rightState after : State (Fin symbols) ConstraintKey)
    (leftCoherent : Coherent leftState) (rightCoherent : Coherent rightState) (afterCoherent : Coherent after)
    (leftLinked : Linked leftState) (rightLinked : Linked rightState)
    (leftGrowth : Grows (run (build first) leftState).2 after)
    (rightGrowth : Grows (run (build second) rightState).2 after) :
    (run (build first) leftState).1.referenceOf = (run (build second) rightState).1.referenceOf ↔ first = second := by
  constructor
  · intro identities
    have values := resident_reference_injective after afterCoherent _ _
      (resident_grows _ after leftGrowth _ (build_resident first leftState leftCoherent))
      (resident_grows _ after rightGrowth _ (build_resident second rightState rightCoherent)) identities
    have rows := congrArg (read (initial := initial)) values
    simpa only [build_read first leftState leftCoherent leftLinked,
      build_read second rightState rightCoherent rightLinked] using rows
  · intro rows
    subst second
    have left := replay (build first) leftState after leftCoherent.valid leftGrowth
    have right := replay (build first) rightState after rightCoherent.valid rightGrowth
    have values := congrArg (fun result : Value (Fin symbols) ConstraintKey × State (Fin symbols) ConstraintKey => result.1)
      (left.symm.trans right)
    exact congrArg Value.referenceOf values

end MicroCFTA.EqualityLeafProjectionLeafCache
