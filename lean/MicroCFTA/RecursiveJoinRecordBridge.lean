import MicroCFTA.RecursiveJoinMass

/-!
# Grouped records and direct recursive join selectors

Local leaf count and decoder fields connect grouped probability records to
the separately constructed direct product selectors. The connection then
holds for every argument of a heterogeneous curried chain.
-/
namespace MicroCFTA.RecursiveJoinRecordBridge
open Language GeneratorCombinators IntegerTermViews SizedRank SamplerReplay
open RecursiveCallbackTermination RecursiveJoinFields RecursiveJoinTyped
open GroupedRecord (Group Classes)

/-- Local provenance connects a class record to its independently supplied source index. -/
def Realizes (classes : Classes Value) (index : ValueIndex Value) : Prop :=
  (∀ size, Decoder.count (classes size).members.plan = index.counts size) ∧
  ∀ position, Decoder.decode (classes position.size).members.plan position.rank = index.select position

/-- The decoder field determines the complete successful interval of a realized index. -/
theorem realized_indexed (classes : Classes Value) (index : ValueIndex Value) (realizes : Realizes classes index) : Indexed index := by
  intro position
  rw [← realizes.1 position.size]
  constructor
  · rintro ⟨value, selected⟩
    rw [← realizes.2 position, Decoder.decode_correct] at selected
    simpa [Decoder.count_correct] using (List.getElem?_eq_some_iff.mp selected).1
  · intro within
    obtain ⟨value, found⟩ := Decoder.decode_exists (classes position.size).members.plan position.rank within
    exact ⟨value, by rw [← realizes.2 position]; exact found⟩

/-- Mapping a source record and its independent index preserves local provenance. -/
theorem map_realizes (transform : Value → Result) (classes : Classes Value) (index : ValueIndex Value)
    (realizes : Realizes classes index) :
    Realizes (RecursiveJoinMass.mapClasses transform classes) (mapIndex transform index) := by
  constructor
  · exact realizes.1
  · intro position
    simp only [RecursiveJoinMass.mapClasses, GroupedRecord.map, mapRecord, Decoder.decode, mapIndex]
    rw [realizes.2]

/-- A grouped product replays the direct mixed-radix position of both operand decoders. -/
theorem product_replay (combine : Left → Right → Result) (left : Classes Left) (right : Classes Right)
    (first second : Position) (before : Left) (after : Right)
    (leftFound : Decoder.decode (left first.size).members.plan first.rank = some before)
    (rightFound : Decoder.decode (right second.size).members.plan second.rank = some after) :
    let position := productPosition (fun size => Decoder.count (left size).members.plan)
      (fun size => Decoder.count (right size).members.plan) first second
    Decoder.decode (RecursiveJoinMass.product combine left right position.size).members.plan position.rank = some (combine before after) := by
  rw [Decoder.decode_correct] at leftFound rightFound
  have replay := SizedRank.productPosition_replay
    (fun size => (Decoder.values (left size).members.plan).map (fun first second => combine first second))
    (fun size => Decoder.values (right size).members.plan) first second
    (by simpa using (List.getElem?_eq_some_iff.mp leftFound).1)
    (List.getElem?_eq_some_iff.mp rightFound).1
  simp only [List.length_map, ← Decoder.count_correct] at replay
  simpa only [Decoder.decode_correct, RecursiveJoinMass.product_values, productPosition,
    Decoder.applyValues, List.flatMap_map, List.getElem?_map, leftFound, rightFound,
    Option.map_some, Option.bind_some] using replay

/-- Independent grouped product records and direct selectors retain identical count and decoder fields. -/
theorem product_realizes (combine : Left → Right → Result) (left : Classes Left) (right : Classes Right)
    (leftIndex : ValueIndex Left) (rightIndex : ValueIndex Right)
    (leftRealizes : Realizes left leftIndex) (rightRealizes : Realizes right rightIndex) :
    Realizes (RecursiveJoinMass.product combine left right) (productIndex combine leftIndex rightIndex) := by
  have counts : ∀ size, Decoder.count (RecursiveJoinMass.product combine left right size).members.plan =
      (productIndex combine leftIndex rightIndex).counts size := by
    intro size
    rw [Decoder.count_correct, RecursiveJoinMass.product_values]
    simp [List.length_flatMap, List.map_const', List.sum_replicate_nat, productIndex, convolve, ← Decoder.count_correct,
      leftRealizes.1, rightRealizes.1]
  refine ⟨counts, ?_⟩
  intro position
  have leftIndexed := realized_indexed left leftIndex leftRealizes
  have rightIndexed := realized_indexed right rightIndex rightRealizes
  have resultIndexed := product_indexed combine leftIndex rightIndex leftIndexed rightIndexed
  by_cases within : position.rank < (productIndex combine leftIndex rightIndex).counts position.size
  · obtain ⟨first, second, combined, firstBound, secondBound⟩ :=
      RecursiveCallbackTables.product_split leftIndex.counts rightIndex.counts position within
    obtain ⟨before, firstFound⟩ := (leftIndexed first).mpr firstBound
    obtain ⟨after, secondFound⟩ := (rightIndexed second).mpr secondBound
    have replay := product_replay combine left right first second before after
      (by rw [leftRealizes.2]; exact firstFound) (by rw [rightRealizes.2]; exact secondFound)
    have leftCounts : (fun size => Decoder.count (left size).members.plan) = leftIndex.counts := funext leftRealizes.1
    have rightCounts : (fun size => Decoder.count (right size).members.plan) = rightIndex.counts := funext rightRealizes.1
    simp only [leftCounts, rightCounts, combined] at replay
    rw [replay, ← combined]
    simp [productIndex, productSplit_productPosition _ _ _ _ firstBound secondBound, firstFound, secondFound]
  · have decoded : Decoder.decode (RecursiveJoinMass.product combine left right position.size).members.plan position.rank = none := by
      rw [Decoder.decode_none_iff, counts]
      omega
    rw [decoded]
    cases found : (productIndex combine leftIndex rightIndex).select position with
    | none => rfl
    | some value => exact False.elim (within ((resultIndexed position).mp ⟨value, found⟩))

/-- Each actual chain leaf has its local count and decoder correspondence. -/
def LeavesRealize (leaves : RecursiveJoinMass.LeafClasses Symbol) : Chain Symbol Operand Result → Prop
  | .nil => True
  | .cons argument rest => Realizes (leaves argument) argument.paired ∧ LeavesRealize leaves rest

/-- Every heterogeneous correlated chain realizes its separately constructed direct index. -/
theorem paired_realizes (leaves : RecursiveJoinMass.LeafClasses Symbol) (chain : Chain Symbol Operand Result)
    (classes : Classes (Operand × Accumulated Symbol)) (index : ValueIndex (Operand × Accumulated Symbol))
    (source : Realizes classes index) (children : LeavesRealize leaves chain) :
    Realizes (RecursiveJoinMass.paired leaves classes chain) (chain.paired index) := by
  induction chain with
  | nil => exact source
  | cons argument rest ih =>
      exact ih _ _ (product_realizes _ _ _ _ _ source children.1) children.2

/-- Every independent user-value chain realizes its separately constructed direct index. -/
theorem values_realizes (leaves : RecursiveJoinMass.LeafClasses Symbol) (chain : Chain Symbol Operand Result)
    (classes : Classes Operand) (index : ValueIndex Operand)
    (source : Realizes classes index) (children : LeavesRealize leaves chain) :
    Realizes (RecursiveJoinMass.values leaves classes chain) (chain.values index) := by
  induction chain with
  | nil => exact source
  | cons argument rest ih =>
      exact ih _ _ (product_realizes _ _ _ _ _ source (map_realizes Prod.fst _ _ children.1)) children.2

end MicroCFTA.RecursiveJoinRecordBridge
