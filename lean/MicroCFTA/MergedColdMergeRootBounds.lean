import MicroCFTA.MergedColdMergeMapFacts
import MicroCFTA.MergedGroupPartitionBound
import MicroCFTA.MergedNodeRowBounds
import MicroCFTA.EqualityOrdinaryReadback

/-!
# Structural keys of completed cold groups

Actual child calls preserve list positions. Rebuilding therefore keeps the
source symbol and arity of each group. The literal group threshold bounds
the number of rows that can have that full key.
-/
namespace MicroCFTA.MergedColdMergeRootBounds
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedNestedProvenance
open InternedRecordCoherence InternedEdgeResidency InternedShallowHeap
open MergedPhysicalWarmup MergedSourceComparison MergedColdMerge MergedColdMergeMapFacts
open MergedPhysicalGroupCalls MergedPhysicalGroupEdges MergedPhysicalGroupColumns MergedSourceGrouping Language
open MergedOrdinaryHeight

/-- A completed finite constructor retains its exact returned-state certificate. -/
theorem work_valid [DecidableEq (EdgeKey Symbol Guard)] (computation : Work Symbol Guard Output)
    (before : State Symbol Guard) (prepared : Prepared before) (post : State Symbol Guard → Output → Prop)
    (verified : InternedNestedFacts.Verified before (InternedNestedConstruction.work computation before) post)
    (unchanged : NoNewMu before (run computation before).2) :
    Extension before (run computation before).2 ∧ post (run computation before).2 (run computation before).1 :=
  ⟨⟨verified.facts, prepared.preserve unchanged, verified.growth, verified.history⟩, verified.result _ _ rfl⟩

/-- Actual retained-column construction preserves source facts at every successful return. -/
theorem retained_valid [DecidableEq (EdgeKey Symbol Guard)]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (checked : ValueCallValid recurse)
    (inputs : List (Value Symbol Guard)) (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (available : Values before inputs) (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : retainedColumn recurse inputs before = .done result after) : Extension before after ∧ Available after result := by
  have branches (values : List (Value Symbol Guard)) (available : Values before values)
      (done : (if values.any recursiveBoundary then MergedColdMerge.work (makeUnion values)
        else MergedColdMerge.bind (MergedColdMerge.work (ordinaryUnion values)) recurse) before = .done result after) :
      Extension before after ∧ Available after result := by
    by_cases boundary : values.any recursiveBoundary = true
    · have equal : (run (makeUnion values) before).1 = result ∧ (run (makeUnion values) before).2 = after := by
        simpa [boundary, MergedColdMerge.work] using done
      rw [← equal.1, ← equal.2]
      exact work_valid _ before prepared Available (union_verified values before facts available) (makeUnion_noNewMu _ _)
    · have resident : Edges before (values.flatMap nodeEdges) := by
        intro edge member
        obtain ⟨value, included, present⟩ := List.mem_flatMap.mp member
        exact resident_edges before facts.linked value (available value included).resident edge present
      obtain ⟨extension, valid⟩ := work_valid (ordinaryUnion values) before prepared Available
        (node_verified _ before facts resident) (makeNode_noNewMu _ _)
      have called : recurse (run (ordinaryUnion values) before).1 (run (ordinaryUnion values) before).2 = .done result after := by
        simpa [boundary, MergedColdMerge.bind, MergedColdMerge.work, Result.bind] using done
      obtain ⟨later, returned⟩ := checked _ _ result after extension.facts extension.prepared valid called
      exact ⟨extension.trans later, returned⟩
  cases inputs with
  | nil => exact branches [] available done
  | cons first rest =>
      cases rest with
      | nil =>
          have equal : first = result ∧ before = after := by simpa [retainedColumn, MergedColdMerge.pure] using done
          rcases equal with ⟨rfl, rfl⟩
          exact ⟨.refl before facts prepared, available first List.mem_cons_self⟩
      | cons second tail => exact branches _ available done

/-- Ordered source filtering and retained construction preserve every successful column result. -/
theorem column_valid [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (checked : ValueCallValid recurse)
    (clear : Guard → Bool) (fuel : Nat) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before) (available : Values before inputs)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : column recurse clear fuel inputs before = .done result after) : Extension before after ∧ Available after result := by
  cases selected : MergedSourceSelection.select clear fuel inputs before with
  | failed => simp [column, MergedColdMerge.bind, selected, Result.bind] at done
  | done retained middle =>
      have effect := (MergedSourceSelection.select_verified clear fuel inputs before facts prepared available).effect selected
      have extension : Extension before middle := ⟨effect.facts, prepared.preserve effect.unchanged, effect.growth, effect.history⟩
      have subset := MergedSourceSelection.select_subset clear fuel inputs before retained middle selected
      have kept := fun value member => extension.available value (available value (subset value member))
      have called : retainedColumn recurse retained middle = .done result after := by
        simpa [column, MergedColdMerge.bind, selected, Result.bind] using done
      obtain ⟨later, returned⟩ := retained_valid recurse checked retained middle extension.facts extension.prepared kept result after called
      exact ⟨extension.trans later, returned⟩

/-- Source transpose constructs exactly one column for each original child position. -/
theorem columns_length (rows : List (List Item)) (arity : Nat) :
    (MergedAlternativesGroups.columns rows arity).length = arity := by
  induction arity generalizing rows with
  | zero => rfl
  | succ arity ih => simp [MergedAlternativesGroups.columns, ih]

/-- A successful small edge keeps its full source key and all cache invariants. -/
theorem small_valid [DecidableEq (EdgeKey Symbol Guard)]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (checked : ValueCallValid recurse)
    (edge : EdgeValue Symbol Guard) (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (resident : EdgeResident before edge) (result : EdgeValue Symbol Guard) (after : State Symbol Guard)
    (done : small recurse edge before = .done result after) :
    Extension before after ∧ EdgeResident after result ∧ groupKey result = groupKey edge := by
  cases children : MergedColdMerge.map recurse edge.children before with
  | failed => simp [small, MergedColdMerge.bind, children, Result.bind] at done
  | done values middle =>
      obtain ⟨extension, available⟩ := values_valid recurse checked edge.children before facts prepared
        (facts.cached.edges edge.entry.key edge resident) values middle children
      have equal : (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle).1 = result ∧
          (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle).2 = after := by
        simpa [small, MergedColdMerge.bind, children, Result.bind, MergedColdMerge.work] using done
      have constructed := work_valid _ middle extension.prepared EdgeResident
        (edge_verified edge.entry.key.symbol edge.entry.key.constraint values middle extension.facts available)
        (fun _ _ _ _ _ stored => stored)
      have fields := makeEdge_fields middle extension.facts edge.entry.key.symbol edge.entry.key.constraint values available
      have count := MergedColdMergeBounds.map_length recurse edge.children before values middle children
      rw [← equal.1, ← equal.2]
      exact ⟨extension.trans constructed.1, constructed.2, Prod.ext fields.1 (by dsimp only [groupKey]; rw [fields.2.2, count])⟩

/-- A successful large edge keeps the representative group's symbol and arity. -/
theorem large_valid [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (checked : ValueCallValid recurse)
    (clear : Guard → Bool) (fuel : Nat) (top : Guard) (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before) (resident : Edges before (first :: rest))
    (result : EdgeValue Symbol Guard) (after : State Symbol Guard)
    (done : large recurse clear fuel top first rest before = .done result after) :
    Extension before after ∧ EdgeResident after result ∧ groupKey result = groupKey first := by
  let requests := MergedAlternativesGroups.columns ((first :: rest).map EdgeValue.children) first.children.length
  change MergedColdMerge.bind (MergedColdMerge.map (column recurse clear fuel) requests)
    (fun values => MergedColdMerge.work (makeEdge first.entry.key.symbol top values)) before = .done result after at done
  have inputs : ∀ values ∈ requests, Values before values := by
    intro values member value included
    obtain ⟨row, present, inner⟩ := columns_member _ _ values member value included
    obtain ⟨edge, selected, rfl⟩ := List.mem_map.mp present
    exact facts.cached.edges edge.entry.key edge (resident edge selected) value inner
  cases children : MergedColdMerge.map (column recurse clear fuel) requests before with
  | failed => simp only [MergedColdMerge.bind, children, Result.bind, reduceCtorEq] at done
  | done values middle =>
      obtain ⟨extension, related⟩ := map_valid (column recurse clear fuel) Values (fun state _ value => Available state value)
        (fun _ _ extension values available value member => extension.available value (available value member))
        (fun _ _ extension _ value available => extension.available value available)
        (fun inputs before result after facts prepared available done => column_valid recurse checked clear fuel inputs before facts prepared available result after done)
        requests before facts prepared inputs values middle children
      have available : Values middle values := EnumerationSoundness.all₂_outputs _ _ _ related
      have equal : (run (makeEdge first.entry.key.symbol top values) middle).1 = result ∧
          (run (makeEdge first.entry.key.symbol top values) middle).2 = after := by
        simpa only [MergedColdMerge.bind, children, Result.bind, MergedColdMerge.work, Result.done.injEq] using done
      have constructed := work_valid _ middle extension.prepared EdgeResident
        (edge_verified first.entry.key.symbol top values middle extension.facts available) (fun _ _ _ _ _ stored => stored)
      have fields := makeEdge_fields middle extension.facts first.entry.key.symbol top values available
      have count := MergedColdMergeBounds.map_length (column recurse clear fuel) requests before values middle children
      have length : values.length = first.children.length := count.trans (columns_length _ _)
      rw [← equal.1, ← equal.2]
      exact ⟨extension.trans constructed.1, constructed.2, Prod.ext fields.1 (by dsimp only [groupKey]; rw [fields.2.2, length])⟩

/-- Every successful group retains only its original full key and at most four rows. -/
theorem group_valid [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (checked : ValueCallValid recurse)
    (clear : Guard → Bool) (fuel : Nat) (top : Guard) (edges : List (EdgeValue Symbol Guard))
    (keys : SameKey edges) (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (resident : Edges before edges) (rows : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : group recurse clear fuel top edges before = .done rows after) :
    Extension before after ∧ Edges after rows ∧ rows.length ≤ 4 ∧
      ∀ row ∈ rows, ∀ original ∈ edges, groupKey row = groupKey original := by
  have bound := MergedColdMergeBounds.group_bound recurse clear fuel top edges before rows after done
  by_cases few : edges.length ≤ 4
  · have mapped : MergedColdMerge.map (small recurse) edges before = .done rows after := by simpa [group, few] using done
    obtain ⟨extension, related⟩ := map_valid (small recurse) EdgeResident
      (fun state original result => EdgeResident state result ∧ groupKey result = groupKey original)
      (fun before after extension edge resident => edge_grows before after extension.growth edge resident)
      (fun before after extension _ edge valid => ⟨edge_grows before after extension.growth edge valid.1, valid.2⟩)
      (fun edge before result after facts prepared resident done => small_valid recurse checked edge before facts prepared resident result after done)
      edges before facts prepared resident rows after mapped
    refine ⟨extension, EnumerationSoundness.all₂_outputs _ _ _ (related.imp (fun _ _ valid => valid.1)), bound, ?_⟩
    intro row member original selected
    have paired : All₂ (fun _ row => groupKey row = groupKey original) edges rows :=
      all₂_left_imp _ _ edges rows related (fun source present result valid =>
        valid.2.trans (Prod.ext (keys source present original selected).1 (keys source present original selected).2))
    exact EnumerationSoundness.all₂_outputs _ _ _ paired row member
  · cases edges with
    | nil => simp at few
    | cons first rest =>
        cases built : large recurse clear fuel top first rest before with
        | failed => simp only [group, ite_eq_right few, MergedColdMerge.bind, built, Result.bind, reduceCtorEq] at done
        | done edge final =>
            have equal : [edge] = rows ∧ final = after := by
              simpa only [group, ite_eq_right few, MergedColdMerge.bind, built, Result.bind, MergedColdMerge.pure, Result.done.injEq] using done
            obtain ⟨extension, retained, same⟩ := large_valid recurse checked clear fuel top first rest before facts prepared resident edge final built
            rcases equal with ⟨rfl, rfl⟩
            refine ⟨extension, ?_, bound, ?_⟩
            · intro row member; simpa only [List.mem_singleton.mp member] using retained
            · intro row member original selected
              rw [List.mem_singleton.mp member]
              exact same.trans (Prod.ext (keys first List.mem_cons_self original selected).1 (keys first List.mem_cons_self original selected).2)

/-- Actual source groups retain their positional row certificates at the final group cache. -/
theorem groups_valid [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (checked : ValueCallValid recurse)
    (clear : Guard → Bool) (fuel : Nat) (top : Guard) (edges : List (EdgeValue Symbol Guard))
    (buckets : List (List (EdgeValue Symbol Guard))) (grouping : MergedPhysicalGroupRoot.Grouping edges buckets)
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before) (resident : Edges before edges)
    (outputs : List (List (EdgeValue Symbol Guard))) (middle : State Symbol Guard)
    (mapped : MergedColdMerge.map (group recurse clear fuel top) buckets before = .done outputs middle) :
    Extension before middle ∧ Edges middle outputs.flatten ∧
      All₂ (MergedGroupPartitionBound.GroupPost groupKey 4) buckets outputs := by
  have inputs : ∀ group ∈ buckets, Edges before group ∧ SameKey group := by
    intro group member
    exact ⟨fun edge present => resident edge (grouping.partition.mem_iff.mp
      (List.mem_flatten.mpr ⟨group, member, present⟩)), grouping.keys edges buckets group member⟩
  obtain ⟨extension, related⟩ := map_valid (group recurse clear fuel top)
    (fun state rows => Edges state rows ∧ SameKey rows)
    (fun state input output => Edges state output ∧ MergedGroupPartitionBound.GroupPost groupKey 4 input output)
    (fun before after extension rows valid => ⟨fun edge member => edge_grows before after extension.growth edge (valid.1 edge member), valid.2⟩)
    (fun before after extension _ rows valid => ⟨fun edge member => edge_grows before after extension.growth edge (valid.1 edge member), valid.2⟩)
    (fun input before output after facts prepared valid done =>
      group_valid recurse checked clear fuel top input valid.2 before facts prepared valid.1 output after done)
    buckets before facts prepared inputs outputs middle mapped
  refine ⟨extension, ?_, related.imp (fun _ _ valid => valid.2)⟩
  intro edge member
  obtain ⟨rows, outer, inner⟩ := List.mem_flatten.mp member
  exact EnumerationSoundness.all₂_outputs _ _ _ (related.imp (fun _ _ valid => valid.1)) rows outer edge inner

/-- The actual root ends with a node request over its complete certified row groups. -/
theorem root_trace [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (checked : ValueCallValid recurse)
    (clear : Guard → Bool) (fuel : Nat) (top : Guard) (edges : List (EdgeValue Symbol Guard))
    (buckets : List (List (EdgeValue Symbol Guard))) (grouping : MergedPhysicalGroupRoot.Grouping edges buckets)
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before) (resident : Edges before edges)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : root recurse clear fuel top buckets before = .done result after) :
    ∃ outputs middle, Extension before middle ∧ Edges middle outputs.flatten ∧
      All₂ (MergedGroupPartitionBound.GroupPost groupKey 4) buckets outputs ∧
      run (makeNode outputs.flatten) middle = (result, after) := by
  cases mapped : MergedColdMerge.map (group recurse clear fuel top) buckets before with
  | failed => simp only [root, MergedColdMerge.bind, mapped, Result.bind, reduceCtorEq] at done
  | done outputs middle =>
      obtain ⟨extension, resident, related⟩ := groups_valid recurse checked clear fuel top edges buckets grouping
        before facts prepared resident outputs middle mapped
      refine ⟨outputs, middle, extension, resident, related, ?_⟩
      have equal : (run (makeNode outputs.flatten) middle).1 = result ∧
          (run (makeNode outputs.flatten) middle).2 = after := by
        simpa only [root, MergedColdMerge.bind, mapped, Result.bind, MergedColdMerge.work, Result.done.injEq] using done
      exact Prod.ext equal.1 equal.2

/-- Arbitrary hash-table bucket order retains the complete root's full-key row bound. -/
theorem root_permutation_bound [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (checked : ValueCallValid recurse)
    (clear : Guard → Bool) (fuel : Nat) (top : Guard) (edges : List (EdgeValue Symbol Guard))
    (buckets : List (List (EdgeValue Symbol Guard))) (permutation : buckets.Perm (groups edges))
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before) (resident : Edges before edges)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : root recurse clear fuel top buckets before = .done result after) (key : Symbol × Nat) :
    ((nodeEdges result).filter (fun edge => decide (groupKey edge = key))).length ≤ 4 := by
  obtain ⟨outputs, middle, extension, resident, related, equal⟩ := root_trace recurse checked clear fuel top edges buckets
    (grouping_permutation edges buckets permutation) before facts prepared resident result after done
  have bound := MergedGroupPartitionBound.filter_bound_permutation groupKey 4 edges buckets outputs permutation related key
  have built := MergedNodeRowBounds.makeNode_key_bound outputs.flatten middle extension.facts.coherent extension.facts.linked resident key 4 bound
  simpa only [equal] using built

/-- The executable source partition returns at most four rows for each symbol and arity. -/
theorem root_bound [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (checked : ValueCallValid recurse)
    (clear : Guard → Bool) (fuel : Nat) (top : Guard) (edges : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before) (resident : Edges before edges)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : root recurse clear fuel top (groups edges) before = .done result after) (key : Symbol × Nat) :
    ((nodeEdges result).filter (fun edge => decide (groupKey edge = key))).length ≤ 4 :=
  root_permutation_bound recurse checked clear fuel top edges (groups edges) (.refl _) before facts prepared resident result after done key

/-- Every actual root result replays exactly from its own normalized outgoing rows. -/
theorem root_normal [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (checked : ValueCallValid recurse)
    (clear : Guard → Bool) (fuel : Nat) (top : Guard) (edges : List (EdgeValue Symbol Guard))
    (buckets : List (List (EdgeValue Symbol Guard))) (grouping : MergedPhysicalGroupRoot.Grouping edges buckets)
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before) (resident : Edges before edges)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : root recurse clear fuel top buckets before = .done result after) :
    EqualityOrdinaryReadback.Normal after result := by
  obtain ⟨outputs, middle, extension, resident, _, equal⟩ := root_trace recurse checked clear fuel top edges buckets grouping
    before facts prepared resident result after done
  have verified := node_verified outputs.flatten middle extension.facts resident
  have afterFacts : Facts after := by
    simpa only [InternedNestedConstruction.work, equal, InternedNestedConstruction.Outcome.state] using verified.facts
  have growth : Grows (run (makeNode outputs.flatten) middle).2 after := by rw [equal]; exact grows_refl _
  have normal := EqualityOrdinaryReadback.makeNode_normal outputs.flatten middle after extension.facts.coherent
    extension.facts.linked afterFacts.coherent resident growth
  simpa only [equal] using normal

/-- Every successful closed ordinary source worker derives the complete root bound from actual execution. -/
theorem worker_root_bound [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (top : Guard) (ordinary comparison : Nat)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Guard)) (depth : Nat)
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (available : Available before (.node entry edges depth [])) (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : worker groups clear top ordinary comparison (.node entry edges depth []) before = .done result after)
    (key : Symbol × Nat) : ((nodeEdges result).filter (fun edge => decide (groupKey edge = key))).length ≤ 4 := by
  cases ordinary with
  | zero => simp [worker] at done
  | succ remaining =>
      apply root_bound (worker groups clear top remaining comparison) (worker_valid groups groups_correct clear top remaining comparison)
        clear comparison top edges before facts prepared (resident_edges before facts.linked _ available.resident) result after _ key
      simpa only [worker, ↓reduceIte] using done

/-- Every completed closed ordinary worker derives exact reconstruction of its returned root. -/
theorem worker_root_normal [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (top : Guard) (ordinary comparison : Nat)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Guard)) (depth : Nat)
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (available : Available before (.node entry edges depth [])) (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : worker groups clear top ordinary comparison (.node entry edges depth []) before = .done result after) :
    EqualityOrdinaryReadback.Normal after result := by
  cases ordinary with
  | zero => simp [worker] at done
  | succ remaining =>
      apply root_normal (worker groups clear top remaining comparison) (worker_valid groups groups_correct clear top remaining comparison)
        clear comparison top edges (groups edges) (groups_correct edges) before facts prepared
        (resident_edges before facts.linked _ available.resident) result after
      simpa only [worker, ↓reduceIte] using done

end MicroCFTA.MergedColdMergeRootBounds
