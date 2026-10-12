import MicroCFTA.KeyedNaryInverse
import MicroCFTA.RecursiveCallbackAPI

/-!
# Public and bounded inverse queries for arbitrary-branch mutually recursive key families

The public filter retains every matching source position. Conversion to
size-major ranks agrees with the independently compiled bounded decoder.
-/
namespace MicroCFTA.KeyedNaryQuery
open Language GeneratorCombinators IntegerTermViews SizedRank
open RecursiveCallbackTermination RecursiveCallbackTables
open KeyedNaryFields KeyedNaryInverse

/-- Exact source term classes, in their independently compiled rank order. -/
def environment (code : Key → Nat) (program : Key → KeyedNaryAlignment.Recipe Key Root Symbol Root) (key : Key) : Nat → List (EngineTerm Symbol) :=
  fun size => KeyedSource.languageClass (KeyedNaryAlignment.sourceTermProgram code program) size key

/-- Class lengths equal the count supplied by the independent value index. -/
theorem root_counts (code : Key → Nat) (program : Key → KeyedNaryAlignment.Recipe Key Root Symbol Root) (key : Key) (size : Nat) :
    (environment code program key size).length = rootCounts program key size := by
  rw [rootCounts, ← (KeyedNaryAlignment.class_counts (KeyedNaryAlignment.sourceWrap code) program size key).2, KeyedSource.family_count]
  rfl

/-- The actual term decoder is exactly the class lookup. -/
theorem decode_table (code : Key → Nat) (program : Key → KeyedNaryAlignment.Recipe Key Root Symbol Root) (key : Key) (position : Position) :
    rootSelect code program key position = (environment code program key position.size)[position.rank]? := by
  simp only [rootSelect, Decoder.decode_correct, KeyedSource.family_values, environment]

/-- The actual checked-flag filter decodes only uncertified candidates. -/
def keep [DecidableEq (EngineTerm Symbol)] (code : Key → Nat) (program : Key → KeyedNaryAlignment.Recipe Key Root Symbol Root) (key : Key)
    (view : View) (wanted : List (EngineTerm Symbol)) (row : Checked) : Bool :=
  row.2 || decide ((rootSelect code program key row.1).map (project view) = some wanted)

/-- Retain source callback order and return the matching class positions. -/
def query [DecidableEq Symbol] [DecidableEq (EngineTerm Symbol)] (callbacks : LeafCallbacks Symbol)
    (code : Key → Nat) (program : Key → KeyedNaryAlignment.Recipe Key Root Symbol Root) (key : Key) (view : View) (wanted : List (EngineTerm Symbol)) :
    List Position :=
  ((positions code callbacks program key view wanted).filter (keep code program key view wanted)).map Prod.fst

/-- The optimized public filter has every inverse position and no false match. -/
theorem query_exact [DecidableEq Symbol] [DecidableEq (EngineTerm Symbol)] (callbacks : LeafCallbacks Symbol)
    (code : Key → Nat) (program : Key → KeyedNaryAlignment.Recipe Key Root Symbol Root) (key : Key)
    (keys : List Key) (complete : ∀ key, key ∈ keys) (accepted : Guarded keys complete program)
    (leaves : ∀ key, KeyedNaryFields.LeavesExact callbacks (program key))
    (view : View) (wanted : List (EngineTerm Symbol)) (position : Position) :
    position ∈ query callbacks code program key view wanted ↔
      ∃ term, rootSelect code program key position = some term ∧ project view term = wanted := by
  constructor
  · intro member
    obtain ⟨row, filtered, same⟩ := List.mem_map.mp member
    obtain ⟨present, kept⟩ := List.mem_filter.mp filtered
    rcases Bool.or_eq_true_iff.mp kept with checked | replayed
    · have rowEq : row = (position, true) := Prod.ext same checked
      exact (positions_exact keys complete code callbacks program accepted leaves key view wanted position).mp (rowEq ▸ present)
    · have replay : (rootSelect code program key position).map (project view) = some wanted := by
        rw [← same]
        exact of_decide_eq_true replayed
      exact Option.map_eq_some_iff.mp replay
  · intro found
    have present := (positions_exact keys complete code callbacks program accepted leaves key view wanted position).mpr found
    exact List.mem_map.mpr ⟨(position, true), List.mem_filter.mpr ⟨present, by simp [keep]⟩, rfl⟩

/-- Whole-term inverse queries agree directly with the independently compiled decoder. -/
theorem whole_query [DecidableEq Symbol] [DecidableEq (EngineTerm Symbol)] (callbacks : LeafCallbacks Symbol)
    (code : Key → Nat) (program : Key → KeyedNaryAlignment.Recipe Key Root Symbol Root) (key : Key)
    (keys : List Key) (complete : ∀ key, key ∈ keys) (accepted : Guarded keys complete program)
    (leaves : ∀ key, KeyedNaryFields.LeavesExact callbacks (program key)) (term : EngineTerm Symbol) (position : Position) :
    position ∈ query callbacks code program key .whole [term] ↔ rootSelect code program key position = some term := by
  rw [query_exact callbacks code program key keys complete accepted leaves]
  simp [project]

/-- Filtering cannot duplicate source positions when finite producers have distinct candidates. -/
theorem query_nodup [DecidableEq Symbol] [DecidableEq (EngineTerm Symbol)] (callbacks : LeafCallbacks Symbol)
    (code : Key → Nat) (program : Key → KeyedNaryAlignment.Recipe Key Root Symbol Root) (key : Key)
    (keys : List Key) (complete : ∀ key, key ∈ keys) (accepted : Guarded keys complete program)
    (bounded : ∀ key, KeyedNaryFields.LeavesBounded callbacks (program key))
    (distinct : ∀ key, KeyedNaryFields.LeavesDistinct callbacks (program key))
    (view : View) (wanted : List (EngineTerm Symbol)) : (query callbacks code program key view wanted).Nodup := by
  have rows := positions_distinct keys complete code callbacks program accepted bounded distinct key view wanted
  exact (RecursiveCallbackDistinct.distinct_iff _).mp (rows.sublist List.filter_sublist)

/-- Public class positions retain the source ascending size and rank order. -/
theorem query_ordered [DecidableEq Symbol] [DecidableEq (EngineTerm Symbol)] (callbacks : LeafCallbacks Symbol)
    (code : Key → Nat) (program : Key → KeyedNaryAlignment.Recipe Key Root Symbol Root) (key : Key)
    (ordered : ∀ key, KeyedNaryFields.LeavesOrdered callbacks (program key)) (view : View) (wanted : List (EngineTerm Symbol)) :
    (query callbacks code program key view wanted).Pairwise (fun p q => p.size < q.size ∨ (p.size = q.size ∧ p.rank ≤ q.rank)) := by
  have rows := positions_ordered code callbacks program ordered key view wanted
  rw [query, List.pairwise_map]
  apply (rows.sublist List.filter_sublist).imp
  intro first second before
  simp only [RecursiveCallbackTermination.before, decide_eq_true_eq] at before
  omega

/-- The public recursive rank is the count prefix followed by its class rank. -/
def globalRank (code : Key → Nat) (program : Key → KeyedNaryAlignment.Recipe Key Root Symbol Root) (key : Key) (position : Position) : Nat :=
  PlanVariants.sizedOffset (environment code program key) position.size + position.rank

theorem global_source_counts (code : Key → Nat) (program : Key → KeyedNaryAlignment.Recipe Key Root Symbol Root) (key : Key) (position : Position) :
    globalRank code program key position = ((List.range position.size).map (rootCounts program key)).sum + position.rank := by
  simp only [globalRank, PlanVariants.sizedOffset, root_counts]

/-- The bounded source decoder selects from the complete ordered class prefix. -/
def boundedDecode (code : Key → Nat) (program : Key → KeyedNaryAlignment.Recipe Key Root Symbol Root) (key : Key) (bound rank : Nat) : Option (EngineTerm Symbol) :=
  Decoder.decode (GroupedRecord.bounded (fun size => KeyedSource.family (KeyedNaryAlignment.sourceTermProgram code program) size key) bound).plan rank

theorem bounded_table (code : Key → Nat) (program : Key → KeyedNaryAlignment.Recipe Key Root Symbol Root) (key : Key) (bound rank : Nat) :
    boundedDecode code program key bound rank = ((List.range (bound + 1)).flatMap (environment code program key))[rank]? := by
  simp only [boundedDecode, Decoder.decode_correct, GroupedRecord.bounded, SamplerReplay.boundedRecord,
    SamplerReplay.manyRecord, SamplerReplay.manyPlan_values, List.flatMap_map, KeyedSource.family_values]
  rfl

/-- A valid class position keeps its global rank under every sufficient size bound. -/
theorem global_replay (code : Key → Nat) (program : Key → KeyedNaryAlignment.Recipe Key Root Symbol Root) (key : Key) (bound : Nat) (position : Position)
    (within : position.size ≤ bound) (valid : position.rank < (environment code program key position.size).length) :
    boundedDecode code program key bound (globalRank code program key position) = rootSelect code program key position := by
  rw [bounded_table, decode_table]
  exact RecursiveSize.get_class_offset (environment code program key) bound position.size position.rank within valid

/-- Every bounded decoder result has its exact original class position. -/
theorem bounded_position (code : Key → Nat) (program : Key → KeyedNaryAlignment.Recipe Key Root Symbol Root) (key : Key) (bound rank : Nat)
    (term : EngineTerm Symbol) (selected : boundedDecode code program key bound rank = some term) :
    ∃ position, position.size ≤ bound ∧ globalRank code program key position = rank ∧ rootSelect code program key position = some term := by
  let plan : PlanVariants.Plan (EngineTerm Symbol) := .sized (environment code program key) bound
  have decoded : Decoder.decode (PlanVariants.erase plan) rank = some term := by
    simpa only [bounded_table, plan, PlanVariants.erase, Decoder.decode] using selected
  have valid := SamplerReplay.decoded_bound _ _ _ decoded
  obtain ⟨position, found⟩ := PlanVariants.position_complete plan rank valid
  obtain ⟨count, member, inClass⟩ := sizeClassOf_valid (PlanVariants.sizedCounts (environment code program key) bound) rank position found
  obtain ⟨size, listed, same⟩ := List.mem_map.mp member
  have sameSize : size = position.size := congrArg Prod.fst same
  have sameCount : (environment code program key size).length = count := congrArg Prod.snd same
  have within : position.size ≤ bound := by have := List.mem_range.mp listed; omega
  have classValid : position.rank < (environment code program key position.size).length := by
    rw [← sameSize, sameCount]
    exact inClass
  have read := PlanVariants.selectClass_position plan rank position term found decoded
  rw [PlanVariants.sized_selectClass (environment code program key) bound position within classValid] at read
  obtain ⟨value, classRead, equal⟩ := Option.map_eq_some_iff.mp read
  obtain ⟨rankEq, valueEq⟩ := Prod.mk.inj equal
  exact ⟨position, within, rankEq, by simpa only [decode_table, valueEq] using classRead⟩

/-- Bound the source callback before converting its retained class positions to global ranks. -/
def boundedQuery [DecidableEq Symbol] [DecidableEq (EngineTerm Symbol)] (callbacks : LeafCallbacks Symbol)
    (code : Key → Nat) (program : Key → KeyedNaryAlignment.Recipe Key Root Symbol Root) (key : Key) (bound : Nat)
    (view : View) (wanted : List (EngineTerm Symbol)) : List Nat :=
  ((query callbacks code program key view wanted).filter (fun position => decide (position.size ≤ bound))).map (globalRank code program key)

/-- The bounded source inverse contains every matching global rank and only matching ranks. -/
theorem bounded_query_exact [DecidableEq Symbol] [DecidableEq (EngineTerm Symbol)] (callbacks : LeafCallbacks Symbol)
    (code : Key → Nat) (program : Key → KeyedNaryAlignment.Recipe Key Root Symbol Root) (key : Key)
    (keys : List Key) (complete : ∀ key, key ∈ keys) (accepted : Guarded keys complete program)
    (leaves : ∀ key, KeyedNaryFields.LeavesExact callbacks (program key)) (bound : Nat)
    (view : View) (wanted : List (EngineTerm Symbol)) (rank : Nat) :
    rank ∈ boundedQuery callbacks code program key bound view wanted ↔
      ∃ term, boundedDecode code program key bound rank = some term ∧ project view term = wanted := by
  constructor
  · intro member
    obtain ⟨position, filtered, same⟩ := List.mem_map.mp member
    obtain ⟨queried, within⟩ := List.mem_filter.mp filtered
    obtain ⟨term, selected, projected⟩ := (query_exact callbacks code program key keys complete accepted leaves view wanted position).mp queried
    have valid := (List.getElem?_eq_some_iff.mp (by simpa only [decode_table] using selected)).1
    exact ⟨term, by rw [← same, global_replay code program key bound position (of_decide_eq_true within) valid, selected], projected⟩
  · rintro ⟨term, selected, projected⟩
    obtain ⟨position, within, same, classRead⟩ := bounded_position code program key bound rank term selected
    exact List.mem_map.mpr ⟨position, List.mem_filter.mpr
      ⟨(query_exact callbacks code program key keys complete accepted leaves view wanted position).mpr ⟨term, classRead, projected⟩,
        decide_eq_true within⟩, same⟩

/-- Valid class positions cannot collapse when converted to global ranks. -/
theorem global_injective (code : Key → Nat) (program : Key → KeyedNaryAlignment.Recipe Key Root Symbol Root) (key : Key) (first second : Position)
    (firstValid : first.rank < (environment code program key first.size).length)
    (secondValid : second.rank < (environment code program key second.size).length)
    (same : globalRank code program key first = globalRank code program key second) : first = second := by
  have left := PlanVariants.position_sized_offset (environment code program key) (max first.size second.size)
    first (Nat.le_max_left _ _) firstValid
  have right := PlanVariants.position_sized_offset (environment code program key) (max first.size second.size)
    second (Nat.le_max_right _ _) secondValid
  change PlanVariants.position _ (globalRank code program key first) = some first at left
  change PlanVariants.position _ (globalRank code program key second) = some second at right
  rw [same, right] at left
  exact (Option.some.inj left).symm

/-- Source size-major order agrees with the global rank order. -/
theorem global_monotone (code : Key → Nat) (program : Key → KeyedNaryAlignment.Recipe Key Root Symbol Root) (key : Key) (first second : Position)
    (valid : first.rank < (environment code program key first.size).length)
    (ordered : first.size < second.size ∨ (first.size = second.size ∧ first.rank ≤ second.rank)) :
    globalRank code program key first ≤ globalRank code program key second := by
  rcases ordered with earlier | ⟨same, within⟩
  · have prefixBound := RecursiveCallbackAPI.prefix_monotone (fun size => (environment code program key size).length)
      (first.size + 1) second.size (by omega)
    simp only [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero] at prefixBound
    dsimp only [globalRank, PlanVariants.sizedOffset]
    omega
  · simp only [globalRank, same]
    omega


/-- Bounded inverse callbacks return each matching global rank once. -/
theorem bounded_query_nodup [DecidableEq Symbol] [DecidableEq (EngineTerm Symbol)] (callbacks : LeafCallbacks Symbol)
    (code : Key → Nat) (program : Key → KeyedNaryAlignment.Recipe Key Root Symbol Root) (key : Key)
    (keys : List Key) (complete : ∀ key, key ∈ keys) (accepted : Guarded keys complete program)
    (leaves : ∀ key, KeyedNaryFields.LeavesExact callbacks (program key)) (bounded : ∀ key, KeyedNaryFields.LeavesBounded callbacks (program key))
    (distinct : ∀ key, KeyedNaryFields.LeavesDistinct callbacks (program key))
    (bound : Nat) (view : View) (wanted : List (EngineTerm Symbol)) :
    (boundedQuery callbacks code program key bound view wanted).Nodup := by
  have unique := (query_nodup callbacks code program key keys complete accepted bounded distinct view wanted).filter
    (fun position => decide (position.size ≤ bound))
  rw [boundedQuery, List.Nodup, List.pairwise_map]
  apply unique.imp_of_mem
  intro first second firstMember secondMember different same
  obtain ⟨firstTerm, firstRead, _⟩ := (query_exact callbacks code program key keys complete accepted leaves view wanted first).mp
    (List.mem_filter.mp firstMember).1
  obtain ⟨secondTerm, secondRead, _⟩ := (query_exact callbacks code program key keys complete accepted leaves view wanted second).mp
    (List.mem_filter.mp secondMember).1
  exact different (global_injective code program key first second
    (List.getElem?_eq_some_iff.mp (by simpa only [decode_table] using firstRead)).1
    (List.getElem?_eq_some_iff.mp (by simpa only [decode_table] using secondRead)).1 same)

/-- The bounded public inverse retains ascending global rank order. -/
theorem bounded_query_ordered [DecidableEq Symbol] [DecidableEq (EngineTerm Symbol)] (callbacks : LeafCallbacks Symbol)
    (code : Key → Nat) (program : Key → KeyedNaryAlignment.Recipe Key Root Symbol Root) (key : Key)
    (keys : List Key) (complete : ∀ key, key ∈ keys) (accepted : Guarded keys complete program)
    (leaves : ∀ key, KeyedNaryFields.LeavesExact callbacks (program key)) (ordered : ∀ key, KeyedNaryFields.LeavesOrdered callbacks (program key))
    (bound : Nat) (view : View) (wanted : List (EngineTerm Symbol)) :
    (boundedQuery callbacks code program key bound view wanted).Pairwise (· ≤ ·) := by
  have sourceOrder := (query_ordered callbacks code program key ordered view wanted).sublist
    (List.filter_sublist (p := fun position : Position => decide (position.size ≤ bound)))
  rw [boundedQuery, List.pairwise_map]
  apply sourceOrder.imp_of_mem
  intro first second firstMember _ order
  obtain ⟨term, selected, _⟩ := (query_exact callbacks code program key keys complete accepted leaves view wanted first).mp
    (List.mem_filter.mp firstMember).1
  exact global_monotone code program key first second
    (List.getElem?_eq_some_iff.mp (by simpa only [decode_table] using selected)).1 order

end MicroCFTA.KeyedNaryQuery
