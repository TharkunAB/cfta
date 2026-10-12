import MicroCFTA.IntegerSizeClosure

/-!
# Size fields of generated finite open compiler sources

This adapter builds size records from the same recipes and grouped source
constructors as the private-term decoder. Parent labels pay one unit. Integer
closure adds one unit for each integer coordinate, at every selected point.
-/
namespace MicroCFTA.OpenGroupedSize
open Probability SourcePlanPositions FiniteSizeFields

/-- Generated bare compiler spines use size zero for pure values and holes. -/
def generated : OpenIntegerSource.Recipe Value → Record
  | .pure _ => uniform .pure
  | .integer _ => uniform (fixedPlan 0 1)
  | .map _ inner => mapRecord (generated inner)
  | .pay inner => pay (generated inner)
  | .app functions arguments => sourcePair (generated functions) (generated arguments)

/-- Every generated recipe derives its complete finite size-field invariant. -/
theorem generated_valid (recipe : OpenIntegerSource.Recipe Value) : Valid (generated recipe) := by
  induction recipe with
  | pure value => exact uniform_valid _
  | integer domain => exact uniform_valid _
  | map transform inner ih => exact map_valid _ ih
  | pay inner ih => exact pay_valid _ ih
  | app functions arguments left right => exact sourcePair_valid _ _ left right

/-- The bare compiler source has one original member before integer closure. -/
theorem generated_count (recipe : OpenIntegerSource.Recipe Value) : count (generated recipe).plan = 1 := by
  induction recipe with
  | pure value => rfl
  | integer domain => exact fixedPlan_count _ _
  | map transform inner ih | pay inner ih => exact ih
  | app functions arguments left right =>
      change count (pairPlan (generated functions).plan (generated arguments).plan) = 1
      rw [pairPlan_count, left, right]

/-- Generated bare spines have no observed-member retained mass table. -/
theorem generated_retained (recipe : OpenIntegerSource.Recipe Value) : (generated recipe).retained = none := by
  induction recipe with
  | pure value | integer domain => rfl
  | map transform inner ih => exact ih
  | pay inner ih => simp [generated, pay, ih]
  | app functions arguments left right => simp [generated, sourcePair, pair, finish, left, right]

/-- Finite bucket merging keeps the source positive-singleton plan. -/
def merge : List Record → Record
  | [record] => record
  | records => choice records

theorem merge_valid (records : List Record) (valid : ∀ record ∈ records, Valid record) : Valid (merge records) := by
  unfold merge
  split
  · exact valid _ (by simp)
  · exact choice_valid records valid

theorem choice_count (records : List Record) : count (choice records).plan = (records.map (fun record => count record.plan)).sum := by
  induction records with
  | nil => rfl
  | cons record rest ih => change count record.plan + count (choice rest).plan = _; rw [ih]; rfl

theorem merge_count (records : List Record) : count (merge records).plan = (records.map (fun record => count record.plan)).sum := by
  unfold merge
  split
  · simp
  · exact choice_count records

theorem merge_retained (records : List Record) (none : ∀ record ∈ records, record.retained = Option.none) :
    (merge records).retained = Option.none := by
  have absent : records.any (fun record => record.retained.isSome) = false := by
    induction records with
    | nil => rfl
    | cons record rest ih => simp [none record (by simp), ih (fun record member => none record (by simp [member]))]
  unfold merge
  split
  · exact none _ (by simp)
  · simp [choice, finish, absent]

/-- Build the actual generated, repeated-key, and binary grouped source size fields. -/
def source : OpenGroupedApplication.Source Value → Record
  | .generated original => generated original.recipe
  | .repeated group => merge (group.originals.map (fun original => generated original.recipe))
  | .app _ functions arguments => sourcePair (source functions) (source arguments)

/-- No whole-record coherence premise is needed for any represented grouped source constructor. -/
theorem source_valid (description : OpenGroupedApplication.Source Value) : Valid (source description) := by
  induction description with
  | generated original => exact generated_valid original.recipe
  | repeated group =>
      apply merge_valid
      intro record member
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      exact generated_valid original.recipe
  | app component functions arguments left right => exact sourcePair_valid _ _ left right

/-- The plan count is the exact private-term decoder count derived by the grouped compiler. -/
theorem source_count (description : OpenGroupedApplication.Source Value) :
    count (source description).plan = OpenGroupedApplication.cardinality description := by
  induction description with
  | generated original => exact generated_count original.recipe
  | repeated group =>
      change count (merge _).plan = group.originals.length
      rw [merge_count]
      simp only [List.map_map, Function.comp_def, generated_count]
      induction group.originals <;> simp_all [Nat.add_comm]
  | app component functions arguments left right =>
      change count (pairPlan _ _) = _
      rw [pairPlan_count, left, right]
      rfl

theorem source_retained (description : OpenGroupedApplication.Source Value) : (source description).retained = none := by
  induction description with
  | generated original => exact generated_retained original.recipe
  | repeated group =>
      apply merge_retained
      intro record member
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      exact generated_retained original.recipe
  | app component functions arguments left right => simp [source, sourcePair, pair, finish, left, right]

/-- Parent construction pays once before closePoints adds its heterogeneous coordinate width. -/
def closed (description : OpenGroupedApplication.Source Value) (pointCount : Nat) : Record :=
  IntegerSizeClosure.close (OpenGroupedApplication.width description) pointCount (pay (source description))

theorem closed_valid (description : OpenGroupedApplication.Source Value) (pointCount : Nat) : Valid (closed description pointCount) :=
  IntegerSizeClosure.close_valid _ _ _ (pay_valid _ (source_valid description))

/-- Decoder, global outcome index, and size plan use the same original-times-point cardinality. -/
theorem closed_count (description : OpenGroupedApplication.Source Value) (pointCount : Nat) :
    count (closed description pointCount).plan = OpenGroupedApplication.cardinality description * pointCount := by
  rw [closed, IntegerSizeClosure.close_count]
  change count (source description).plan * pointCount = _
  rw [source_count]

/-- Successful parent settlement supplies a global term index with precisely the same finite size plan count. -/
theorem settled_count (origin : Nat)
    (specialize : List Int → IntegerLabelCodec.Symbol → IntegerLabelCodec.Symbol)
    (symbol : IntegerLabelCodec.Symbol) (record : OpenGroupedApplication.ClosedBucket Value) :
    count (closed record.original.source (LatticeSelect.pointCount record.points.levels)).plan =
      (FinalObservationMass.settledBucket origin specialize symbol record).index.count :=
  closed_count _ _

/-- Select a term through the independent exact-size rank list. -/
def selectClass (index : FinalObservationRanks.Index Symbol) (fields : Record) (size rank : Nat) :
    Option (Language.Term (GeneratorCombinators.Label Symbol)) := do
  let original ← (classRanks fields.plan size)[rank]?
  index.select original

/-- Every derived class position selects the exact original global term. -/
theorem selectClass_replay (index : FinalObservationRanks.Index Symbol) (fields : Record)
    (part : SizedRank.Position) (original : Nat)
    (converted : position fields.plan original = some part) :
    selectClass index fields part.size part.rank = index.select original := by
  simp [selectClass, SourcePlanPositions.position_replay fields.plan original part converted]

/-- A complete global decoder yields a complete exact-size decoder at the derived class count. -/
theorem selectClass_exists (index : FinalObservationRanks.Index Symbol) (exact : FinalObservationRanks.Exact index)
    (fields : Record) (counts : count fields.plan = index.count) (size rank : Nat) :
    (∃ term, selectClass index fields size rank = some term) ↔ rank < (classRanks fields.plan size).length := by
  constructor
  · rintro ⟨term, selected⟩
    cases found : (classRanks fields.plan size)[rank]? with
    | none => simp [selectClass, found] at selected
    | some original => exact List.getElem?_eq_some_iff.mp found |>.1
  · intro inside
    let original := (classRanks fields.plan size)[rank]
    have found : (classRanks fields.plan size)[rank]? = some original := List.getElem?_eq_getElem inside
    have bound : original < index.count := by
      rw [← counts]
      exact class_rank_bound fields.plan size original (List.getElem_mem inside)
    obtain ⟨term, selected⟩ := (exact.bounds original).mpr bound
    exact ⟨term, by simp [selectClass, found, selected]⟩

/-- The actual successful integer settlement and generated source constructors discharge class-decoder alignment. -/
theorem settled_class_decoder (origin : Nat)
    (specialize : List Int → IntegerLabelCodec.Symbol → IntegerLabelCodec.Symbol)
    (symbol : IntegerLabelCodec.Symbol)
    (specialized : ∀ point, IntegerLabelCodec.exactLabel point symbol = .ok (specialize point symbol))
    (parents : List FullSyntax.Formula) (bucket : OpenGroupedApplication.Bucket Value)
    (record : OpenGroupedApplication.ClosedBucket Value)
    (success : OpenGroupedApplication.settle parents bucket = .ok (some record)) (size rank : Nat) :
    let fields := closed record.original.source (LatticeSelect.pointCount record.points.levels)
    (∃ term, selectClass (FinalObservationMass.settledBucket origin specialize symbol record).index fields size rank = some term) ↔
      rank < (classRanks fields.plan size).length := by
  dsimp only
  apply selectClass_exists
  · have same := (OpenGroupedApplication.settle_fields parents bucket record success).1
    simp only [FinalObservationMass.settledBucket, same]
    exact FinalObservationRanks.settledIndex_exact specialize symbol specialized parents bucket record success
  · exact settled_count origin specialize symbol record

end MicroCFTA.OpenGroupedSize
