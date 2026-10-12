import MicroCFTA.RecursiveCallbackCompleteness
import MicroCFTA.RecursiveCallbackAlignment
import MicroCFTA.RecursiveCallbackDistinct

/-!
# Exact recursive inverse queries against the typed decoder

The checked callback and the independently compiled term index agree at
every class position. The public checked-flag filter keeps all and only
matching positions. Finite callback laws are local producer contracts.
-/
namespace MicroCFTA.RecursiveCallbackAPI
open Language GeneratorCombinators IntegerTermViews SizedRank
open RecursiveCallbackTermination RecursiveCallbackTables RecursiveCallbackAlignment

/-- The actual value index supplies the count used by recursive inverse callbacks. -/
def selfCounts (body : RecursiveTermAlignment.Recipe Root Symbol Root) (size : Nat) : Nat :=
  Decoder.count (RecursiveSource.family (RecursiveTermAlignment.valueRecipe body) size).plan

/-- The independently built term index supplies exact class decoding. -/
def decode (body : RecursiveTermAlignment.Recipe Root Symbol Root) (position : Position) : Option (EngineTerm Symbol) :=
  Decoder.decode (RecursiveSource.family (RecursiveTermAlignment.termBody body) position.size).plan position.rank

theorem root_counts (body : RecursiveTermAlignment.Recipe Root Symbol Root) (size : Nat) :
    (environment body size).length = selfCounts body size := by
  rw [selfCounts, RecursiveTermAlignment.class_counts, RecursiveSource.family_count]
  rfl

theorem decode_table (body : RecursiveTermAlignment.Recipe Root Symbol Root) (position : Position) :
    decode body position = (environment body position.size)[position.rank]? := by
  simp only [decode, Decoder.decode_correct, RecursiveSource.family_values, environment]

/-- The source count-knot equation follows from actual class construction and its guard. -/
theorem count_knot (callbacks : LeafCallbacks Symbol) (body : RecursiveTermAlignment.Recipe Root Symbol Root)
    (accepted : RecursiveSource.guarded (RecursiveTermAlignment.valueRecipe body)
      (RecursiveSource.assumption (RecursiveTermAlignment.valueRecipe body)) = true) (size : Nat) :
    selfCounts body size = counts (selfCounts body) (compile callbacks body) size := by
  rw [← root_counts body size, root_equation callbacks body accepted size, List.length_map]
  exact class_length _ _ (root_counts body) _ _

/-- True flags identify exactly the requested views of the actual recursive decoder. -/
theorem certified_query [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol)
    (body : RecursiveTermAlignment.Recipe Root Symbol Root)
    (accepted : RecursiveSource.guarded (RecursiveTermAlignment.valueRecipe body)
      (RecursiveSource.assumption (RecursiveTermAlignment.valueRecipe body)) = true)
    (leaves : LeavesExact (compile callbacks body))
    (view : View) (wanted : List (EngineTerm Symbol)) (position : Position) :
    (position, true) ∈ tied (selfCounts body) (compile callbacks body) view wanted ↔
      ∃ term, decode body position = some term ∧ project view term = wanted := by
  constructor
  · intro member
    obtain ⟨term, selected, projected⟩ :=
      (certified_exact _ _ leaves .occurrence trivial view wanted position).mp member
    have found := selects_lookup (environment body) (selfCounts body) (root_counts body)
      (compile callbacks body) (root_equation callbacks body accepted) (compiled_indexed callbacks body)
      .occurrence position term selected trivial
    exact ⟨term, by simpa only [decode_table, classTerms] using found, projected⟩
  · rintro ⟨term, selected, rfl⟩
    exact RecursiveCallbackCompleteness.table_complete (environment body) (selfCounts body) (root_counts body)
      (compile callbacks body) (root_equation callbacks body accepted) leaves (compiled_indexed callbacks body)
      .occurrence trivial trivial position term (by simpa only [decode_table, classTerms] using selected) view

/-- The actual checked-flag filter decodes only uncertified candidates. -/
def keep [DecidableEq (EngineTerm Symbol)] (body : RecursiveTermAlignment.Recipe Root Symbol Root)
    (view : View) (wanted : List (EngineTerm Symbol)) (row : Checked) : Bool :=
  row.2 || decide ((decode body row.1).map (project view) = some wanted)

/-- Retain source callback order and return the matching class positions. -/
def query [DecidableEq Symbol] [DecidableEq (EngineTerm Symbol)] (callbacks : LeafCallbacks Symbol)
    (body : RecursiveTermAlignment.Recipe Root Symbol Root) (view : View) (wanted : List (EngineTerm Symbol)) :
    List Position :=
  ((tied (selfCounts body) (compile callbacks body) view wanted).filter (keep body view wanted)).map Prod.fst

/-- The optimized public filter has every inverse position and no false match. -/
theorem query_exact [DecidableEq Symbol] [DecidableEq (EngineTerm Symbol)] (callbacks : LeafCallbacks Symbol)
    (body : RecursiveTermAlignment.Recipe Root Symbol Root)
    (accepted : RecursiveSource.guarded (RecursiveTermAlignment.valueRecipe body)
      (RecursiveSource.assumption (RecursiveTermAlignment.valueRecipe body)) = true)
    (leaves : LeavesExact (compile callbacks body))
    (view : View) (wanted : List (EngineTerm Symbol)) (position : Position) :
    position ∈ query callbacks body view wanted ↔
      ∃ term, decode body position = some term ∧ project view term = wanted := by
  constructor
  · intro member
    obtain ⟨row, filtered, same⟩ := List.mem_map.mp member
    obtain ⟨present, kept⟩ := List.mem_filter.mp filtered
    rcases Bool.or_eq_true_iff.mp kept with checked | replayed
    · have rowEq : row = (position, true) := Prod.ext same checked
      exact (certified_query callbacks body accepted leaves view wanted position).mp (rowEq ▸ present)
    · have replay : (decode body position).map (project view) = some wanted := by
        rw [← same]
        exact of_decide_eq_true replayed
      exact Option.map_eq_some_iff.mp replay
  · intro found
    have present := (certified_query callbacks body accepted leaves view wanted position).mpr found
    exact List.mem_map.mpr ⟨(position, true), List.mem_filter.mpr ⟨present, by simp [keep]⟩, rfl⟩

/-- Whole-term inverse queries agree directly with the independently compiled decoder. -/
theorem whole_query [DecidableEq Symbol] [DecidableEq (EngineTerm Symbol)] (callbacks : LeafCallbacks Symbol)
    (body : RecursiveTermAlignment.Recipe Root Symbol Root)
    (accepted : RecursiveSource.guarded (RecursiveTermAlignment.valueRecipe body)
      (RecursiveSource.assumption (RecursiveTermAlignment.valueRecipe body)) = true)
    (leaves : LeavesExact (compile callbacks body)) (term : EngineTerm Symbol) (position : Position) :
    position ∈ query callbacks body .whole [term] ↔ decode body position = some term := by
  rw [query_exact callbacks body accepted leaves]
  simp [project]

/-- Filtering cannot duplicate source positions when finite producers have distinct candidates. -/
theorem query_nodup [DecidableEq Symbol] [DecidableEq (EngineTerm Symbol)] (callbacks : LeafCallbacks Symbol)
    (body : RecursiveTermAlignment.Recipe Root Symbol Root)
    (accepted : RecursiveSource.guarded (RecursiveTermAlignment.valueRecipe body)
      (RecursiveSource.assumption (RecursiveTermAlignment.valueRecipe body)) = true)
    (bounded : LeavesBounded (compile callbacks body))
    (distinct : RecursiveCallbackDistinct.LeavesDistinct (compile callbacks body))
    (view : View) (wanted : List (EngineTerm Symbol)) : (query callbacks body view wanted).Nodup := by
  have rows := RecursiveCallbackDistinct.positions_distinct (selfCounts body) (compile callbacks body)
    (count_knot callbacks body accepted) bounded distinct .occurrence trivial trivial view wanted
  exact (RecursiveCallbackDistinct.distinct_iff _).mp (rows.sublist List.filter_sublist)

/-- Public class positions retain the source ascending size and rank order. -/
theorem query_ordered [DecidableEq Symbol] [DecidableEq (EngineTerm Symbol)] (callbacks : LeafCallbacks Symbol)
    (body : RecursiveTermAlignment.Recipe Root Symbol Root)
    (ordered : LeavesOrdered (compile callbacks body)) (view : View) (wanted : List (EngineTerm Symbol)) :
    (query callbacks body view wanted).Pairwise (fun p q => p.size < q.size ∨ (p.size = q.size ∧ p.rank ≤ q.rank)) := by
  have rows := positions_ordered (selfCounts body) (compile callbacks body) ordered .occurrence trivial view wanted
  rw [query, List.pairwise_map]
  apply (rows.sublist List.filter_sublist).imp
  intro first second before
  simp only [RecursiveCallbackTermination.before, decide_eq_true_eq] at before
  omega

/-- The public recursive rank is the count prefix followed by its class rank. -/
def globalRank (body : RecursiveTermAlignment.Recipe Root Symbol Root) (position : Position) : Nat :=
  PlanVariants.sizedOffset (environment body) position.size + position.rank

theorem global_source_counts (body : RecursiveTermAlignment.Recipe Root Symbol Root) (position : Position) :
    globalRank body position = ((List.range position.size).map (selfCounts body)).sum + position.rank := by
  simp only [globalRank, PlanVariants.sizedOffset, root_counts]

/-- The bounded source decoder selects from the complete ordered class prefix. -/
def boundedDecode (body : RecursiveTermAlignment.Recipe Root Symbol Root) (bound rank : Nat) : Option (EngineTerm Symbol) :=
  Decoder.decode (RecursiveSource.bounded (RecursiveTermAlignment.termBody body) bound).plan rank

theorem bounded_table (body : RecursiveTermAlignment.Recipe Root Symbol Root) (bound rank : Nat) :
    boundedDecode body bound rank = ((List.range (bound + 1)).flatMap (environment body))[rank]? := by
  simp only [boundedDecode, Decoder.decode_correct, RecursiveSource.bounded, SamplerReplay.boundedRecord,
    SamplerReplay.manyRecord, SamplerReplay.manyPlan_values, List.flatMap_map, RecursiveSource.family_values, environment]

/-- A valid class position keeps its global rank under every sufficient size bound. -/
theorem global_replay (body : RecursiveTermAlignment.Recipe Root Symbol Root) (bound : Nat) (position : Position)
    (within : position.size ≤ bound) (valid : position.rank < (environment body position.size).length) :
    boundedDecode body bound (globalRank body position) = decode body position := by
  rw [bounded_table, decode_table]
  exact RecursiveSize.get_class_offset (environment body) bound position.size position.rank within valid

/-- Every bounded decoder result has its exact original class position. -/
theorem bounded_position (body : RecursiveTermAlignment.Recipe Root Symbol Root) (bound rank : Nat)
    (term : EngineTerm Symbol) (selected : boundedDecode body bound rank = some term) :
    ∃ position, position.size ≤ bound ∧ globalRank body position = rank ∧ decode body position = some term := by
  let plan : PlanVariants.Plan (EngineTerm Symbol) := .sized (environment body) bound
  have decoded : Decoder.decode (PlanVariants.erase plan) rank = some term := by
    simpa only [bounded_table, plan, PlanVariants.erase, Decoder.decode] using selected
  have valid := SamplerReplay.decoded_bound _ _ _ decoded
  obtain ⟨position, found⟩ := PlanVariants.position_complete plan rank valid
  obtain ⟨count, member, inClass⟩ := sizeClassOf_valid (PlanVariants.sizedCounts (environment body) bound) rank position found
  obtain ⟨size, listed, same⟩ := List.mem_map.mp member
  have sameSize : size = position.size := congrArg Prod.fst same
  have sameCount : (environment body size).length = count := congrArg Prod.snd same
  have within : position.size ≤ bound := by have := List.mem_range.mp listed; omega
  have classValid : position.rank < (environment body position.size).length := by
    rw [← sameSize, sameCount]
    exact inClass
  have read := PlanVariants.selectClass_position plan rank position term found decoded
  rw [PlanVariants.sized_selectClass (environment body) bound position within classValid] at read
  obtain ⟨value, classRead, equal⟩ := Option.map_eq_some_iff.mp read
  obtain ⟨rankEq, valueEq⟩ := Prod.mk.inj equal
  exact ⟨position, within, rankEq, by simpa only [decode_table, valueEq] using classRead⟩

/-- Bound the source callback before converting its retained class positions to global ranks. -/
def boundedQuery [DecidableEq Symbol] [DecidableEq (EngineTerm Symbol)] (callbacks : LeafCallbacks Symbol)
    (body : RecursiveTermAlignment.Recipe Root Symbol Root) (bound : Nat)
    (view : View) (wanted : List (EngineTerm Symbol)) : List Nat :=
  ((query callbacks body view wanted).filter (fun position => decide (position.size ≤ bound))).map (globalRank body)

/-- The bounded source inverse contains every matching global rank and only matching ranks. -/
theorem bounded_query_exact [DecidableEq Symbol] [DecidableEq (EngineTerm Symbol)] (callbacks : LeafCallbacks Symbol)
    (body : RecursiveTermAlignment.Recipe Root Symbol Root)
    (accepted : RecursiveSource.guarded (RecursiveTermAlignment.valueRecipe body)
      (RecursiveSource.assumption (RecursiveTermAlignment.valueRecipe body)) = true)
    (leaves : LeavesExact (compile callbacks body)) (bound : Nat)
    (view : View) (wanted : List (EngineTerm Symbol)) (rank : Nat) :
    rank ∈ boundedQuery callbacks body bound view wanted ↔
      ∃ term, boundedDecode body bound rank = some term ∧ project view term = wanted := by
  constructor
  · intro member
    obtain ⟨position, filtered, same⟩ := List.mem_map.mp member
    obtain ⟨queried, within⟩ := List.mem_filter.mp filtered
    obtain ⟨term, selected, projected⟩ := (query_exact callbacks body accepted leaves view wanted position).mp queried
    have valid := (List.getElem?_eq_some_iff.mp (by simpa only [decode_table] using selected)).1
    exact ⟨term, by rw [← same, global_replay body bound position (of_decide_eq_true within) valid, selected], projected⟩
  · rintro ⟨term, selected, projected⟩
    obtain ⟨position, within, same, classRead⟩ := bounded_position body bound rank term selected
    exact List.mem_map.mpr ⟨position, List.mem_filter.mpr
      ⟨(query_exact callbacks body accepted leaves view wanted position).mpr ⟨term, classRead, projected⟩,
        decide_eq_true within⟩, same⟩

/-- Valid class positions cannot collapse when converted to global ranks. -/
theorem global_injective (body : RecursiveTermAlignment.Recipe Root Symbol Root) (first second : Position)
    (firstValid : first.rank < (environment body first.size).length)
    (secondValid : second.rank < (environment body second.size).length)
    (same : globalRank body first = globalRank body second) : first = second := by
  have left := PlanVariants.position_sized_offset (environment body) (max first.size second.size)
    first (Nat.le_max_left _ _) firstValid
  have right := PlanVariants.position_sized_offset (environment body) (max first.size second.size)
    second (Nat.le_max_right _ _) secondValid
  change PlanVariants.position _ (globalRank body first) = some first at left
  change PlanVariants.position _ (globalRank body second) = some second at right
  rw [same, right] at left
  exact (Option.some.inj left).symm

/-- Bounded inverse callbacks return each matching global rank once. -/
theorem bounded_query_nodup [DecidableEq Symbol] [DecidableEq (EngineTerm Symbol)] (callbacks : LeafCallbacks Symbol)
    (body : RecursiveTermAlignment.Recipe Root Symbol Root)
    (accepted : RecursiveSource.guarded (RecursiveTermAlignment.valueRecipe body)
      (RecursiveSource.assumption (RecursiveTermAlignment.valueRecipe body)) = true)
    (leaves : LeavesExact (compile callbacks body)) (bounded : LeavesBounded (compile callbacks body))
    (distinct : RecursiveCallbackDistinct.LeavesDistinct (compile callbacks body))
    (bound : Nat) (view : View) (wanted : List (EngineTerm Symbol)) :
    (boundedQuery callbacks body bound view wanted).Nodup := by
  have unique := (query_nodup callbacks body accepted bounded distinct view wanted).filter
    (fun position => decide (position.size ≤ bound))
  rw [boundedQuery, List.Nodup, List.pairwise_map]
  apply unique.imp_of_mem
  intro first second firstMember secondMember different same
  obtain ⟨firstTerm, firstRead, _⟩ := (query_exact callbacks body accepted leaves view wanted first).mp
    (List.mem_filter.mp firstMember).1
  obtain ⟨secondTerm, secondRead, _⟩ := (query_exact callbacks body accepted leaves view wanted second).mp
    (List.mem_filter.mp secondMember).1
  exact different (global_injective body first second
    (List.getElem?_eq_some_iff.mp (by simpa only [decode_table] using firstRead)).1
    (List.getElem?_eq_some_iff.mp (by simpa only [decode_table] using secondRead)).1 same)

/-- Prefix sums of nonnegative class counts cannot decrease. -/
theorem prefix_monotone (counts : Nat → Nat) (first second : Nat) (within : first ≤ second) :
    ((List.range first).map counts).sum ≤ ((List.range second).map counts).sum := by
  have split : second = first + (second - first) := by omega
  rw [split, List.range_add, List.map_append, List.sum_append]
  omega

/-- Source size-major order agrees with the global rank order. -/
theorem global_monotone (body : RecursiveTermAlignment.Recipe Root Symbol Root) (first second : Position)
    (valid : first.rank < (environment body first.size).length)
    (ordered : first.size < second.size ∨ (first.size = second.size ∧ first.rank ≤ second.rank)) :
    globalRank body first ≤ globalRank body second := by
  rcases ordered with earlier | ⟨same, within⟩
  · have prefixBound := prefix_monotone (fun size => (environment body size).length)
      (first.size + 1) second.size (by omega)
    simp only [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero] at prefixBound
    dsimp only [globalRank, PlanVariants.sizedOffset]
    omega
  · simp only [globalRank, same]
    omega

/-- The bounded public inverse retains ascending global rank order. -/
theorem bounded_query_ordered [DecidableEq Symbol] [DecidableEq (EngineTerm Symbol)] (callbacks : LeafCallbacks Symbol)
    (body : RecursiveTermAlignment.Recipe Root Symbol Root)
    (accepted : RecursiveSource.guarded (RecursiveTermAlignment.valueRecipe body)
      (RecursiveSource.assumption (RecursiveTermAlignment.valueRecipe body)) = true)
    (leaves : LeavesExact (compile callbacks body)) (ordered : LeavesOrdered (compile callbacks body))
    (bound : Nat) (view : View) (wanted : List (EngineTerm Symbol)) :
    (boundedQuery callbacks body bound view wanted).Pairwise (· ≤ ·) := by
  have sourceOrder := (query_ordered callbacks body ordered view wanted).sublist
    (List.filter_sublist (p := fun position : Position => decide (position.size ≤ bound)))
  rw [boundedQuery, List.pairwise_map]
  apply sourceOrder.imp_of_mem
  intro first second firstMember _ order
  obtain ⟨term, selected, _⟩ := (query_exact callbacks body accepted leaves view wanted first).mp
    (List.mem_filter.mp firstMember).1
  exact global_monotone body first second
    (List.getElem?_eq_some_iff.mp (by simpa only [decode_table] using selected)).1 order

end MicroCFTA.RecursiveCallbackAPI
