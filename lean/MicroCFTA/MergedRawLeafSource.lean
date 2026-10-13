import MicroCFTA.MergedRawLeaves
import MicroCFTA.MergedRowGroups
import MicroCFTA.EqualityRawLeafUnion
import MicroCFTA.EqualityRawLeafPullback

/-!
# Physical raw-leaf merge worker

Read the actual outgoing records, group their distinct raw guards by symbol,
then issue the source nullary makeEdge and makeNode requests. Symbol order is
an explicit input because HashMap iteration order is not fixed by this model.
-/
namespace MicroCFTA.MergedRawLeafSource
open SourceGuards FullSyntax InternedConstructorTemplates InternedRecordCoherence
open InternedEdgeResidency InternedFreshProbeKeys InternedProbeProvenance
open EqualityLeafProjectionCompileAvailability EqualityLeafProjectionRepresentation
open EqualityRawLeafInventory (Leaf Row)
open EqualityRawLeafConstruction (ConstraintKey)
open EqualityRawLeafCompiler (build)

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance
noncomputable local instance : DecidableEq (Guard Formula) := by classical exact inferInstance

/-- Read the complete residual spelling of every actual outgoing nullary record. -/
def rows (value : Value (Fin symbols) ConstraintKey) : List (Fin symbols × Guard Formula) :=
  (nodeEdges value).map fun edge => (edge.entry.key.symbol, edge.entry.key.constraint.2)

/-- A represented leaf exposes exactly its selected raw rows through its actual records. -/
theorem represented_rows (leaf : Leaf initial symbols) (value : Value (Fin symbols) ConstraintKey)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (represented : Represents build (.leaf leaf) state value) (symbol : Fin symbols) (guard : Guard Formula) :
    (symbol, guard) ∈ rows value ↔ ∃ row, leaf symbol row ∧ row.val.val = guard := by
  constructor
  · intro member
    obtain ⟨edge, member, same⟩ := List.mem_map.mp member
    obtain ⟨actual, row, present, key⟩ :=
      (EqualityRawLeafUnion.represented_keys leaf value state facts represented edge.entry.key).mp ⟨edge, member, rfl⟩
    have label : actual = symbol := (congrArg EdgeKey.symbol key).trans (congrArg Prod.fst same)
    have residual : row.val.val = guard :=
      (congrArg (fun key => key.constraint.2) key).trans (congrArg Prod.snd same)
    subst actual
    exact ⟨row, present, residual⟩
  · rintro ⟨row, present, rfl⟩
    obtain ⟨edge, member, key⟩ :=
      (EqualityRawLeafUnion.represented_keys leaf value state facts represented
        (EqualityRawLeafConstruction.key (symbol, row.val.val))).mpr ⟨symbol, row, present, rfl⟩
    exact List.mem_map.mpr ⟨edge, member,
      Prod.ext (congrArg EdgeKey.symbol key) (congrArg (fun key => key.constraint.2) key)⟩

/-- Canonical input records already contain no repeated complete raw row. -/
theorem represented_rows_distinct (leaf : Leaf initial symbols) (value : Value (Fin symbols) ConstraintKey)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (represented : Represents build (.leaf leaf) state value) : (rows value).Nodup := by
  have fields := EqualityRawLeafUnion.represented_fields leaf value state facts represented
  have resident := resident_edges state facts.linked value fields.1
  have normal := fields.2.1
  have readback := EqualityLeafProjectionPhysical.makeNode_edges (nodeEdges value) state facts.coherent facts.linked resident
  rw [normal] at readback
  have ids : ((nodeEdges value).map (fun edge => edge.entry.identity)).Nodup := by
    rw [readback, canonicalEdges_ids]
    exact EnumerationBuilderCaches.canonicalIds_nodup _
  have shape (edge : EdgeValue (Fin symbols) ConstraintKey) (member : edge ∈ nodeEdges value) :
      edge.entry.key = ⟨edge.entry.key.symbol, [], (some [], edge.entry.key.constraint.2)⟩ := by
    obtain ⟨symbol, row, _, key⟩ :=
      (EqualityRawLeafUnion.represented_keys leaf value state facts represented edge.entry.key).mp ⟨edge, member, rfl⟩
    rw [← key]
    rfl
  simp only [rows, List.Nodup, List.pairwise_map] at ids ⊢
  apply ids.imp_of_mem
  intro first second firstMember secondMember different same
  have keys : first.entry.key = second.entry.key := by
    rw [shape first firstMember, shape second secondMember]
    exact congrArg (fun pair : Fin symbols × Guard Formula =>
      EdgeKey.mk pair.1 [] (some [], pair.2)) same
  have left := resident first firstMember
  have right := resident second secondMember
  unfold EdgeResident at left right
  rw [keys] at left
  exact different (congrArg (fun edge : EdgeValue (Fin symbols) ConstraintKey => edge.entry.identity)
    (Option.some.inj (left.symm.trans right)))

/-- Group actual outgoing records in the supplied source symbol order. -/
noncomputable def declarations (order : List (Fin symbols)) (value : Value (Fin symbols) ConstraintKey) :
    List (Fin symbols × Guard Formula) :=
  MergedRowGroups.grouped .top order (rows value)

/-- The supplied order includes every physical source symbol. -/
def Complete (order : List (Fin symbols)) (value : Value (Fin symbols) ConstraintKey) : Prop :=
  ∀ symbol guard, (symbol, guard) ∈ rows value → symbol ∈ order

/-- Complete raw guard spelling determines its finite proof-carrying row. -/
theorem row_injective (first second : Row initial) (same : first.val.val = second.val.val) : first = second :=
  Subtype.ext (Subtype.ext same)

/-- The physical group and finite carrier enumerate the same distinct complete rows. -/
theorem rowsAt_perm (leaf : Leaf initial symbols) (value : Value (Fin symbols) ConstraintKey)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (represented : Represents build (.leaf leaf) state value) (symbol : Fin symbols) :
    (MergedRowGroups.rowsAt (rows value) symbol).Perm
      ((MergedRawLeaves.selected leaf symbol).map (fun row => row.val.val)) := by
  have distinct : ((MergedRawLeaves.selected leaf symbol).map (fun row => row.val.val)).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    exact (MergedRawLeaves.selected_distinct leaf symbol).imp
      (fun different same => different (row_injective _ _ same))
  apply (List.perm_ext_iff_of_nodup (MergedRowGroups.rowsAt_nodup _ _) distinct).mpr
  intro guard
  rw [MergedRowGroups.rowsAt_member, represented_rows leaf value state facts represented]
  simp only [List.mem_map, MergedRawLeaves.selected_member]

/-- Physical grouping selects exactly the merged finite raw predicate. -/
theorem declarations_member (leaf : Leaf initial symbols) (value : Value (Fin symbols) ConstraintKey)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (represented : Represents build (.leaf leaf) state value)
    (order : List (Fin symbols)) (complete : Complete order value)
    (symbol : Fin symbols) (guard : Guard Formula) :
    (symbol, guard) ∈ declarations order value ↔
      ∃ row, MergedRawLeaves.merge leaf symbol row ∧ row.val.val = guard := by
  rw [declarations, MergedRowGroups.grouped_member _ _ _ complete]
  have lengths := (rowsAt_perm leaf value state facts represented symbol).length_eq
  simp only [List.length_map] at lengths
  rw [lengths, represented_rows leaf value state facts represented]
  constructor
  · rintro (⟨⟨row, present, same⟩, small⟩ | ⟨rfl, large⟩)
    · exact ⟨row, (MergedRawLeaves.merge_cases leaf symbol row).mpr (Or.inl ⟨present, small⟩), same⟩
    · exact ⟨MergedRawLeaves.top initial,
        (MergedRawLeaves.merge_cases leaf symbol _).mpr (Or.inr ⟨rfl, large⟩), rfl⟩
  · rintro ⟨row, member, rfl⟩
    rcases (MergedRawLeaves.merge_cases leaf symbol row).mp member with ⟨present, small⟩ | ⟨rfl, large⟩
    · exact Or.inl ⟨⟨row, present, rfl⟩, small⟩
    · exact Or.inr ⟨rfl, large⟩

/-- Every output declaration already satisfies the raw nullary constructor checks. -/
theorem declarations_admitted (leaf : Leaf initial symbols) (value : Value (Fin symbols) ConstraintKey)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (represented : Represents build (.leaf leaf) state value)
    (order : List (Fin symbols)) (complete : Complete order value)
    (declaration : Fin symbols × Guard Formula) (member : declaration ∈ declarations order value) :
    EqualityRawLeafConstruction.accepted declaration.2 = true := by
  obtain ⟨row, _, same⟩ := (declarations_member leaf value state facts represented order complete declaration.1 declaration.2).mp member
  rw [← same]
  exact row.property.2

/-- Execute the source's direct nullary edge and node requests on the physical groups. -/
noncomputable def worker (order : List (Fin symbols)) (value : Value (Fin symbols) ConstraintKey) :
    Work (Fin symbols) ConstraintKey (Value (Fin symbols) ConstraintKey) :=
  EqualityLeafProjectionNullary.build
    ((declarations order value).map fun row => (row.1, (some [], row.2)))

/-- The direct source requests equal the checked raw builder when all rows are already admitted. -/
theorem admitted_build (declarations : List (Fin symbols × Guard Formula))
    (admitted : ∀ row ∈ declarations, EqualityRawLeafConstruction.accepted row.2 = true) :
    EqualityLeafProjectionNullary.build (declarations.map fun row => (row.1, (some [], row.2))) =
      EqualityRawLeafConstruction.build declarations := by
  unfold EqualityLeafProjectionNullary.build EqualityRawLeafConstruction.build
  congr 1
  unfold EqualityLeafProjectionNullary.requests EqualityRawLeafConstruction.requests
  rw [List.map_map]
  apply congrArg EqualityLeafProjectionWorkers.sequence
  apply List.map_congr_left
  intro row member
  simp only [Function.comp_apply, EqualityRawLeafConstruction.request, admitted row member,
    ↓reduceIte]

/-- No sentinel request or extra rejection branch occurs in the represented physical merge. -/
theorem worker_eq_raw (leaf : Leaf initial symbols) (value : Value (Fin symbols) ConstraintKey)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (represented : Represents build (.leaf leaf) state value)
    (order : List (Fin symbols)) (complete : Complete order value) :
    worker order value = EqualityRawLeafConstruction.build (declarations order value) :=
  admitted_build _ (declarations_admitted leaf value state facts represented order complete)

/-- The actual merge preserves all finite-cache payload and availability invariants. -/
theorem worker_available (leaf : Leaf initial symbols) (value : Value (Fin symbols) ConstraintKey)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (represented : Represents build (.leaf leaf) state value)
    (order : List (Fin symbols)) (complete : Complete order value) :
    Facts (run (worker order value) state).2 ∧
      Available (run (worker order value) state).2 (run (worker order value) state).1 := by
  rw [worker_eq_raw leaf value state facts represented order complete]
  exact EqualityRawLeafAvailability.build_available _ state facts

/-- The physical merge has exactly the complete keys selected by the finite merged predicate. -/
theorem worker_keys (leaf : Leaf initial symbols) (value : Value (Fin symbols) ConstraintKey)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (represented : Represents build (.leaf leaf) state value)
    (order : List (Fin symbols)) (complete : Complete order value)
    (key : EdgeKey (Fin symbols) ConstraintKey) :
    (∃ edge ∈ nodeEdges (run (worker order value) state).1, edge.entry.key = key) ↔
      ∃ symbol row, MergedRawLeaves.merge leaf symbol row ∧
        EqualityRawLeafConstruction.key (symbol, row.val.val) = key := by
  rw [worker_eq_raw leaf value state facts represented order complete,
    EqualityRawLeafConstruction.build_keys _ state facts.coherent facts.linked]
  constructor
  · rintro ⟨⟨symbol, guard⟩, member, _, same⟩
    obtain ⟨row, present, rfl⟩ := (declarations_member leaf value state facts represented order complete symbol guard).mp member
    exact ⟨symbol, row, present, same⟩
  · rintro ⟨symbol, row, present, same⟩
    exact ⟨(symbol, row.val.val),
      (declarations_member leaf value state facts represented order complete symbol row.val.val).mpr ⟨row, present, rfl⟩,
      row.property.2, same⟩

/-- Compiler declaration membership forgets only the row's proof fields. -/
theorem compiler_declarations (leaf : Leaf initial symbols) (symbol : Fin symbols) (guard : Guard Formula) :
    (symbol, guard) ∈ EqualityRawLeafConstruction.declarations (EqualityRawLeafInventory.rawChoices leaf) ↔
      ∃ row, leaf symbol row ∧ row.val.val = guard := by
  simp only [EqualityRawLeafConstruction.declarations, EqualityRawLeafInventory.rawChoices,
    List.map_map, List.mem_map, Function.comp_def]
  constructor
  · rintro ⟨⟨actual, row⟩, member, same⟩
    have symbols : actual = symbol := (Prod.mk.inj same).1
    subst actual
    exact ⟨row, (EqualityRawLeafInventory.choices_member leaf symbol row).mp member, (Prod.mk.inj same).2⟩
  · rintro ⟨row, member, same⟩
    exact ⟨(symbol, row), (EqualityRawLeafInventory.choices_member leaf symbol row).mpr member, Prod.ext rfl same⟩

/-- The actual merge and compiled finite merged leaf have the same complete record in a later common cache. -/
theorem worker_record (leaf : Leaf initial symbols) (value : Value (Fin symbols) ConstraintKey)
    (state built after : State (Fin symbols) ConstraintKey)
    (facts : Facts state) (builtFacts : Facts built) (afterCoherent : Coherent after)
    (represented : Represents build (.leaf leaf) state value)
    (order : List (Fin symbols)) (complete : Complete order value)
    (workerGrowth : Grows (run (worker order value) state).2 after)
    (buildGrowth : Grows (run (build (MergedRawLeaves.merge leaf)) built).2 after) :
    (run (worker order value) state).1 = (run (build (MergedRawLeaves.merge leaf)) built).1 := by
  rw [worker_eq_raw leaf value state facts represented order complete] at workerGrowth ⊢
  apply EqualityRawLeafIdentity.same_records _ _ state built after facts.coherent.valid builtFacts.coherent.valid
    afterCoherent workerGrowth buildGrowth
  intro declaration
  rw [declarations_member leaf value state facts represented order complete declaration.1 declaration.2,
    compiler_declarations]

/-- The physical merge constructs a finite later cache containing its exact merged-leaf representation. -/
theorem worker_completed (leaf : Leaf initial symbols) (value : Value (Fin symbols) ConstraintKey)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (represented : Represents build (.leaf leaf) state value)
    (order : List (Fin symbols)) (complete : Complete order value) :
    let actual := run (worker order value) state
    let prepared := run (build (MergedRawLeaves.merge leaf)) actual.2
    Facts prepared.2 ∧ Grows actual.2 prepared.2 ∧
      Represents build (.leaf (MergedRawLeaves.merge leaf)) prepared.2 actual.1 := by
  let actual := run (worker order value) state
  let prepared := run (build (MergedRawLeaves.merge leaf)) actual.2
  have actualFacts := worker_available leaf value state facts represented order complete
  have preparedFacts := EqualityRawLeafCompiler.leaves_available (MergedRawLeaves.merge leaf) actual.2 actualFacts.1
  have growth : Grows actual.2 prepared.2 :=
    (InternedConstructorTemplates.run_correct _ actual.2 actualFacts.1.coherent.valid).2
  have same := worker_record leaf value state actual.2 prepared.2 facts actualFacts.1 preparedFacts.1.coherent
    represented order complete growth (grows_refl prepared.2)
  change actual.1 = prepared.1 at same
  refine ⟨preparedFacts.1, growth, ?_⟩
  change run (build (MergedRawLeaves.merge leaf)) prepared.2 = (actual.1, prepared.2)
  rw [same]
  exact replay (build (MergedRawLeaves.merge leaf)) actual.2 prepared.2 actualFacts.1.coherent.valid (grows_refl prepared.2)

/-- The exact merged representation already holds in the actual runtime output cache. -/
theorem worker_actual (leaf : Leaf initial symbols) (value : Value (Fin symbols) ConstraintKey)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (represented : Represents build (.leaf leaf) state value)
    (order : List (Fin symbols)) (complete : Complete order value) :
    let actual := run (worker order value) state
    Facts actual.2 ∧ Represents build (.leaf (MergedRawLeaves.merge leaf)) actual.2 actual.1 := by
  let actual := run (worker order value) state
  have available := worker_available leaf value state facts represented order complete
  have completed := worker_completed leaf value state facts represented order complete
  exact ⟨available.1, EqualityRawLeafPullback.represented_pullback (MergedRawLeaves.merge leaf)
    actual.2 _ available.1 completed.1 actual.1 available.2.resident completed.2.2⟩

/-- The physical merged result has at most four distinct complete rows at each symbol. -/
theorem worker_group_bound (leaf : Leaf initial symbols) (value : Value (Fin symbols) ConstraintKey)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (represented : Represents build (.leaf leaf) state value)
    (order : List (Fin symbols)) (complete : Complete order value) (symbol : Fin symbols) :
    (MergedRowGroups.rowsAt (rows (run (worker order value) state).1) symbol).length ≤ 4 := by
  have actual := worker_actual leaf value state facts represented order complete
  have lengths := (rowsAt_perm (MergedRawLeaves.merge leaf) (run (worker order value) state).1
    (run (worker order value) state).2 actual.1 actual.2 symbol).length_eq
  rw [lengths, List.length_map]
  exact MergedRawLeaves.merged_bound leaf symbol

/-- If all nullary groups have at most four rows, the worker retains the complete original node. -/
theorem worker_small_record (leaf : Leaf initial symbols) (value : Value (Fin symbols) ConstraintKey)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (represented : Represents build (.leaf leaf) state value)
    (order : List (Fin symbols)) (complete : Complete order value)
    (small : ∀ symbol, (MergedRowGroups.rowsAt (rows value) symbol).length ≤ 4) :
    (run (worker order value) state).1 = value := by
  have unchanged : MergedRawLeaves.merge leaf = leaf := by
    apply MergedRawLeaves.unchanged
    intro symbol
    have lengths := (rowsAt_perm leaf value state facts represented symbol).length_eq
    simpa only [lengths, List.length_map] using small symbol
  have actual := worker_actual leaf value state facts represented order complete
  rw [unchanged] at actual
  have growth := (InternedConstructorTemplates.run_correct (worker order value) state facts.coherent.valid).2
  have old := EqualityLeafProjectionRepresentation.grows build (.leaf leaf) state _
    facts.coherent.valid growth value represented
  exact congrArg Prod.fst (actual.2.symm.trans old)

end MicroCFTA.MergedRawLeafSource
