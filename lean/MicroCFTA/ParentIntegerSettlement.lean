import MicroCFTA.OpenIntegerSource
import MicroCFTA.LatticeDeclaredNames
import MicroCFTA.RecipeCompile

/-!
# Parent restrictions and retained integer mass

The parent appends its integer conditions to the renamed child formulas.
Successful point counting identifies the filtered finite tuple domain.
The retained share is then the exact mass of that filter.
-/
namespace MicroCFTA.ParentIntegerSettlement
open FullSyntax OpenIntegerKeys Probability

local instance : Std.Associative (α := Rat) (· * ·) := ⟨Rat.mul_assoc⟩
local instance : Std.Commutative (α := Rat) (· * ·) := ⟨Rat.mul_comm⟩

/-- Integer comparisons satisfy every primitive law used by conjunction simplification. -/
theorem integer_laws : FormulaSimplify.RelationLaws integerModel := by
  constructor <;> intros <;> simp_all [integerModel, CoreFormula.evalRelation]

/-- The source parent conjoins renamed child formulas before its translated open guards. -/
def restrictedFormula (keys : List Key) (parents : List Formula) : Formula :=
  foldFormulas (renamedFormulas keys ++ parents)

/-- Parent formulas are tested on the full joined coordinate tuple. -/
noncomputable def parentAllows (parents : List Formula) (tuple : List Int) : Bool :=
  @decide (∀ formula ∈ parents, Holds integerModel (tupleEnv tuple) formula) (Classical.propDecidable _)

/-- The finite reference filter retains actual child tuples that pass every parent condition. -/
noncomputable def retainedTuples (domains : Key → List (List Int)) (keys : List Key) (parents : List Formula) :
    List (List Int) := (joinedTuples domains keys).filter (parentAllows parents)

/-- The actual source formula fold keeps both the child domain and every parent restriction. -/
theorem restrictedFormula_exact (keys : List Key) (parents : List Formula) (tuple : List Int) :
    Holds integerModel (tupleEnv tuple) (restrictedFormula keys parents) ↔
      Holds integerModel (tupleEnv tuple) (join keys).formula ∧
      ∀ formula ∈ parents, Holds integerModel (tupleEnv tuple) formula := by
  simp only [restrictedFormula, join, foldFormulas_exact integerModel integer_laws,
    List.mem_append, or_imp, forall_and]

/-- Exact child domains derive the full parent-restricted tuple language. -/
theorem retainedTuples_exact (keys : List Key) (parents : List Formula)
    (within : ∀ key ∈ keys, Scoped key.width key.formula)
    (domains : Key → List (List Int))
    (exactDomains : ∀ key ∈ keys, ∀ tuple, tuple ∈ domains key ↔
      tuple.length = key.width ∧ Holds integerModel (tupleEnv tuple) key.formula) (tuple : List Int) :
    tuple ∈ retainedTuples domains keys parents ↔
      tuple.length = (join keys).width ∧ Holds integerModel (tupleEnv tuple) (restrictedFormula keys parents) := by
  rw [retainedTuples, List.mem_filter, joined_formula_exact integerModel integer_laws
    (by intro value; rfl) keys within domains exactDomains, restrictedFormula_exact]
  simp only [parentAllows, decide_eq_true_eq]
  exact and_assoc

/-- Finite tuple filtering retains distinct points. -/
theorem retainedTuples_distinct (keys : List Key) (parents : List Formula)
    (domains : Key → List (List Int))
    (valid : ∀ key ∈ keys, ∀ tuple ∈ domains key, tuple.length = key.width)
    (distinct : ∀ key ∈ keys, (domains key).Nodup) :
    (retainedTuples domains keys parents).Nodup :=
  (joinedTuples_nodup domains keys valid distinct).filter _

/-- The actual point decoder enumerates precisely the retained tuples, with its own rank order. -/
theorem counter_domain_perm (keys : List Key) (parents : List Formula)
    (within : ∀ key ∈ keys, Scoped key.width key.formula)
    (domains : Key → List (List Int))
    (exactDomains : ∀ key ∈ keys, ∀ tuple, tuple ∈ domains key ↔
      tuple.length = key.width ∧ Holds integerModel (tupleEnv tuple) key.formula)
    (distinct : ∀ key ∈ keys, (domains key).Nodup)
    (points : LatticeAPI.Points)
    (built : LatticeAPI.points (names (join keys).width) (lowerFormula (restrictedFormula keys parents)) = .ok points) :
    (OpenIntegerSource.pointDomain points).Perm (retainedTuples domains keys parents) := by
  apply (List.perm_ext_iff_of_nodup (OpenIntegerSource.pointDomain_distinct _ _ points built)
    (retainedTuples_distinct keys parents domains
      (fun key member tuple found => ((exactDomains key member tuple).mp found).1) distinct)).mpr
  intro tuple
  rw [OpenIntegerSource.pointDomain_exact _ _ points built,
    retainedTuples_exact keys parents within domains exactDomains]

/-- Successful actual point counting gives exactly the parent filter's finite cardinality. -/
theorem counter_matches_filter (keys : List Key) (parents : List Formula)
    (within : ∀ key ∈ keys, Scoped key.width key.formula)
    (domains : Key → List (List Int))
    (exactDomains : ∀ key ∈ keys, ∀ tuple, tuple ∈ domains key ↔
      tuple.length = key.width ∧ Holds integerModel (tupleEnv tuple) key.formula)
    (distinct : ∀ key ∈ keys, (domains key).Nodup)
    (points : LatticeAPI.Points)
    (built : LatticeAPI.points (names (join keys).width) (lowerFormula (restrictedFormula keys parents)) = .ok points) :
    points.count.toNat = (retainedTuples domains keys parents).length := by
  rw [← OpenIntegerSource.pointDomain_count _ _ points built]
  exact (counter_domain_perm keys parents within domains exactDomains distinct points built).length_eq

/-- Project only the OpenKey fields read by source settlement. -/
def childInfo (key : Key) : RecipeCompile.OpenInfo := ⟨key.width, key.points⟩

/-- Known child point records give the cardinality denominator of the actual joined tuple list. -/
theorem denominator_exact (keys : List Key) (domains : Key → List (List Int))
    (counts : ∀ key ∈ keys, key.points = some (domains key).length) :
    ((keys.map childInfo).map (fun key => key.points.getD 1)).prod = (joinedTuples domains keys).length := by
  rw [joinedTuples_count]
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro key member
  simp [childInfo, counts key member]

/-- The source kept ratio equals the probability that independent finite child points pass the parent. -/
theorem retainedShare_exact (keys : List Key) (parents : List Formula)
    (within : ∀ key ∈ keys, Scoped key.width key.formula)
    (domains : Key → List (List Int))
    (exactDomains : ∀ key ∈ keys, ∀ tuple, tuple ∈ domains key ↔
      tuple.length = key.width ∧ Holds integerModel (tupleEnv tuple) key.formula)
    (distinct : ∀ key ∈ keys, (domains key).Nodup)
    (counts : ∀ key ∈ keys, key.points = some (domains key).length)
    (points : LatticeAPI.Points)
    (built : LatticeAPI.points (names (join keys).width) (lowerFormula (restrictedFormula keys parents)) = .ok points) :
    RecipeCompile.retainedShare points.count.toNat (keys.map childInfo) =
      eventMass (parentAllows parents) (normalize (counting (joinedTuples domains keys))) := by
  rw [RecipeCompile.retainedShare, denominator_exact keys domains counts,
    counter_matches_filter keys parents within domains exactDomains distinct points built,
    uniform_event_probability]
  simp only [retainedTuples, List.countP_eq_length_filter]

/-- Scaling by the incoming tuple mass gives its exact accepted contribution. -/
theorem retained_mass (keys : List Key) (parents : List Formula)
    (within : ∀ key ∈ keys, Scoped key.width key.formula)
    (domains : Key → List (List Int))
    (exactDomains : ∀ key ∈ keys, ∀ tuple, tuple ∈ domains key ↔
      tuple.length = key.width ∧ Holds integerModel (tupleEnv tuple) key.formula)
    (distinct : ∀ key ∈ keys, (domains key).Nodup)
    (counts : ∀ key ∈ keys, key.points = some (domains key).length)
    (points : LatticeAPI.Points)
    (built : LatticeAPI.points (names (join keys).width) (lowerFormula (restrictedFormula keys parents)) = .ok points)
    (mass : Rat) :
    mass * RecipeCompile.retainedShare points.count.toNat (keys.map childInfo) =
      eventMass (parentAllows parents) (scale mass (normalize (counting (joinedTuples domains keys)))) := by
  rw [retainedShare_exact keys parents within domains exactDomains distinct counts points built, eventMass_scale]

/-- Filtering a constant-density finite domain keeps the same density on its retained points. -/
theorem restrict_scaled_counting (accepted : Value → Bool) (density : Rat) (values : List Value) :
    restrict accepted (scale density (counting values)) = scale density (counting (values.filter accepted)) := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      cases kept : accepted value <;> simp [restrict, scale, counting, kept] at ih ⊢ <;> exact ih

/-- A settled finite block uses the source kept mass and uniform retained-point closure. -/
def settledBlock (mass : Rat) (values : List Value) (accepted : Value → Bool) : Distribution Value :=
  let kept := values.filter accepted
  scale (mass * ((kept.length : Rat) / values.length)) (normalize (counting kept))

/-- The kept-ratio update followed by point closure is exactly the original block's restriction. -/
theorem settledBlock_exact (mass : Rat) (values : List Value) (accepted : Value → Bool) :
    settledBlock mass values accepted = restrict accepted (scale mass (normalize (counting values))) := by
  simp only [settledBlock, normalize, total_counting, scale_scale, restrict_scaled_counting]
  by_cases empty : (values.filter accepted).length = 0
  · have none : values.filter accepted = [] := List.length_eq_zero_iff.mp empty
    simp [none, counting, scale]
  · have nonzero : ((values.filter accepted).length : Rat) ≠ 0 := by simpa using empty
    congr 1
    simp only [Rat.div_def]
    calc
      _ = (mass * (values.length : Rat)⁻¹) *
          (((values.filter accepted).length : Rat) * ((values.filter accepted).length : Rat)⁻¹) := by ac_rfl
      _ = _ := by rw [Rat.mul_inv_cancel _ nonzero]; simp

/-- Every retained finite tuple has a positive source denominator; dropped empty tuples need no division. -/
theorem retained_denominator_positive (keys : List Key) (parents : List Formula)
    (within : ∀ key ∈ keys, Scoped key.width key.formula)
    (domains : Key → List (List Int))
    (exactDomains : ∀ key ∈ keys, ∀ tuple, tuple ∈ domains key ↔
      tuple.length = key.width ∧ Holds integerModel (tupleEnv tuple) key.formula)
    (distinct : ∀ key ∈ keys, (domains key).Nodup)
    (counts : ∀ key ∈ keys, key.points = some (domains key).length)
    (points : LatticeAPI.Points)
    (built : LatticeAPI.points (names (join keys).width) (lowerFormula (restrictedFormula keys parents)) = .ok points)
    (retained : 0 < points.count.toNat) :
    0 < ((keys.map childInfo).map (fun key => key.points.getD 1)).prod := by
  rw [denominator_exact keys domains counts]
  rw [counter_matches_filter keys parents within domains exactDomains distinct points built] at retained
  have subset := List.length_filter_le (parentAllows parents) (joinedTuples domains keys)
  dsimp only [retainedTuples] at retained
  omega

/-- The actual counter-derived source share and closed-point distribution equal finite rejection. -/
theorem source_block_exact (keys : List Key) (parents : List Formula)
    (within : ∀ key ∈ keys, Scoped key.width key.formula)
    (domains : Key → List (List Int))
    (exactDomains : ∀ key ∈ keys, ∀ tuple, tuple ∈ domains key ↔
      tuple.length = key.width ∧ Holds integerModel (tupleEnv tuple) key.formula)
    (distinct : ∀ key ∈ keys, (domains key).Nodup)
    (counts : ∀ key ∈ keys, key.points = some (domains key).length)
    (points : LatticeAPI.Points)
    (built : LatticeAPI.points (names (join keys).width) (lowerFormula (restrictedFormula keys parents)) = .ok points)
    (mass : Rat) :
    scale (mass * RecipeCompile.retainedShare points.count.toNat (keys.map childInfo))
        (normalize (counting (retainedTuples domains keys parents))) =
      restrict (parentAllows parents) (scale mass (normalize (counting (joinedTuples domains keys)))) := by
  rw [RecipeCompile.retainedShare, denominator_exact keys domains counts,
    counter_matches_filter keys parents within domains exactDomains distinct points built]
  exact settledBlock_exact mass (joinedTuples domains keys) (parentAllows parents)

/-- Actual source decoder order gives the same event mass as rejection from the original child points. -/
theorem source_block_event (keys : List Key) (parents : List Formula)
    (within : ∀ key ∈ keys, Scoped key.width key.formula)
    (domains : Key → List (List Int))
    (exactDomains : ∀ key ∈ keys, ∀ tuple, tuple ∈ domains key ↔
      tuple.length = key.width ∧ Holds integerModel (tupleEnv tuple) key.formula)
    (distinct : ∀ key ∈ keys, (domains key).Nodup)
    (counts : ∀ key ∈ keys, key.points = some (domains key).length)
    (points : LatticeAPI.Points)
    (built : LatticeAPI.points (names (join keys).width) (lowerFormula (restrictedFormula keys parents)) = .ok points)
    (mass : Rat) (event : List Int → Bool) :
    eventMass event (scale (mass * RecipeCompile.retainedShare points.count.toNat (keys.map childInfo))
        (normalize (counting (OpenIntegerSource.pointDomain points)))) =
      eventMass event (restrict (parentAllows parents) (scale mass (normalize (counting (joinedTuples domains keys))))) := by
  have ordered := (counter_domain_perm keys parents within domains exactDomains distinct points built).map
    (fun tuple => ((1 : Rat), tuple))
  have same : eventMass event (normalize (counting (OpenIntegerSource.pointDomain points))) =
      eventMass event (normalize (counting (retainedTuples domains keys parents))) :=
    normalized_perm_event event ordered
  rw [eventMass_scale, same, ← eventMass_scale,
    source_block_exact keys parents within domains exactDomains distinct counts points built mass]

/-- Successful child counters and the parent counter derive the final restricted count without semantic premises. -/
theorem counted_parent_cardinality (keys : List Key) (parents : List Formula)
    (tables : Key → LatticeAPI.Points)
    (childrenBuilt : ∀ key ∈ keys,
      LatticeAPI.points (names key.width) (lowerFormula key.formula) = .ok (tables key))
    (points : LatticeAPI.Points)
    (built : LatticeAPI.points (names (join keys).width) (lowerFormula (restrictedFormula keys parents)) = .ok points) :
    points.count.toNat =
      (retainedTuples (fun key => OpenIntegerSource.pointDomain (tables key)) keys parents).length := by
  apply counter_matches_filter keys parents
    (fun key member => LatticeDeclaredNames.points_scoped _ _ _ (childrenBuilt key member))
    (fun key => OpenIntegerSource.pointDomain (tables key))
    (fun key member tuple => OpenIntegerSource.pointDomain_exact _ _ _ (childrenBuilt key member) tuple)
    (fun key member => OpenIntegerSource.pointDomain_distinct _ _ _ (childrenBuilt key member)) points built

/-- Exact source count records and successful counters give the parent closure's actual event mass. -/
theorem counted_parent_event (keys : List Key) (parents : List Formula)
    (tables : Key → LatticeAPI.Points)
    (childrenBuilt : ∀ key ∈ keys,
      LatticeAPI.points (names key.width) (lowerFormula key.formula) = .ok (tables key))
    (records : ∀ key ∈ keys, key.points = some (tables key).count.toNat)
    (points : LatticeAPI.Points)
    (built : LatticeAPI.points (names (join keys).width) (lowerFormula (restrictedFormula keys parents)) = .ok points)
    (mass : Rat) (event : List Int → Bool) :
    eventMass event (scale (mass * RecipeCompile.retainedShare points.count.toNat (keys.map childInfo))
        (normalize (counting (OpenIntegerSource.pointDomain points)))) =
      eventMass event (restrict (parentAllows parents)
        (scale mass (normalize (counting
          (joinedTuples (fun key => OpenIntegerSource.pointDomain (tables key)) keys))))) := by
  apply source_block_event keys parents
    (fun key member => LatticeDeclaredNames.points_scoped _ _ _ (childrenBuilt key member))
    (fun key => OpenIntegerSource.pointDomain (tables key))
    (fun key member tuple => OpenIntegerSource.pointDomain_exact _ _ _ (childrenBuilt key member) tuple)
    (fun key member => OpenIntegerSource.pointDomain_distinct _ _ _ (childrenBuilt key member))
    (fun key member => ?_) points built mass event
  rw [OpenIntegerSource.pointDomain_count _ _ _ (childrenBuilt key member)]
  exact records key member

/-- Restriction distributes over the finite sequence of source groups. -/
theorem restrict_blocks (accepted : Value → Bool) (blocks : List (Rat × List Value)) :
    restrict accepted (blocks.flatMap fun block => scale block.1 (normalize (counting block.2))) =
      blocks.flatMap (fun block => restrict accepted (scale block.1 (normalize (counting block.2)))) := by
  simp [restrict, List.filter_flatMap]

/-- Normalizing the source kept blocks gives exactly the conditioned original finite distribution. -/
theorem settle_groups_condition (accepted : Value → Bool) (blocks : List (Rat × List Value)) :
    normalize (blocks.flatMap fun block => settledBlock block.1 block.2 accepted) =
      condition accepted (blocks.flatMap fun block => scale block.1 (normalize (counting block.2))) := by
  simp only [settledBlock_exact, condition, restrict_blocks]

/-- Counter errors precede all drop, open, and closed settlement branches. -/
def settleResult (symbolic : Bool) (children : List RecipeCompile.OpenInfo) :
    Except Error Nat → Except Error RecipeCompile.Settlement :=
  fun result => result.map (RecipeCompile.settle symbolic children)

theorem settleResult_error (symbolic : Bool) (children : List RecipeCompile.OpenInfo) (error : Error) :
    settleResult symbolic children (.error error) = .error error := rfl

/-- A zero count drops the tuple before its label can select an open or closed branch. -/
theorem settleResult_empty (symbolic : Bool) (children : List RecipeCompile.OpenInfo) :
    settleResult (Error := Error) symbolic children (.ok 0) = .ok .drop := by
  simp [settleResult, RecipeCompile.settle, Except.map]

/-- Execute the source tuple mass update and optional point-closure metadata update. -/
def buildBucket (variables : Nat) (bucket : RecipeCompile.BucketMeta) :
    RecipeCompile.Settlement → Option RecipeCompile.BucketMeta
  | .drop => none
  | .open _ _ share | .closed none share => some (RecipeCompile.retainBucket share bucket)
  | .closed (some points) share =>
      some (RecipeCompile.closeBucket variables points (RecipeCompile.retainBucket share bucket))

/-- Leaving a group open changes only its outer mass. Point cardinality is still deferred. -/
theorem build_open (variables found : Nat) (share : Rat) (bucket : RecipeCompile.BucketMeta) :
    buildBucket variables bucket (.open variables found share) =
      some { bucket with mass := bucket.mass * share } := rfl

/-- Closing a kept tuple multiplies member counts and retained size masses once. -/
theorem build_closed (variables found : Nat) (share : Rat) (bucket : RecipeCompile.BucketMeta) :
    buildBucket variables bucket (.closed (some found) share) =
      some ⟨bucket.mass * share, bucket.size + variables, bucket.count * found, false,
        bucket.sizeMass.map (fun mass => mass * (found : Rat))⟩ := rfl

/-- A source pay and the integer-coordinate size shift commute without changing either mass scale. -/
theorem pay_close (variables found : Nat) (bucket : RecipeCompile.BucketMeta) :
    RecipeCompile.closeBucket variables found (RecipeCompile.payBucket bucket) =
      RecipeCompile.payBucket (RecipeCompile.closeBucket variables found bucket) := by
  cases bucket
  simp [RecipeCompile.closeBucket, RecipeCompile.payBucket, Nat.add_assoc, Nat.add_comm]

/-- An unavailable child count uses density one, not a uniform probability over an infinite domain. -/
theorem unknown_share (found : Nat) :
    RecipeCompile.retainedShare found [⟨1, none⟩] = (found : Rat) := by
  simp [RecipeCompile.retainedShare, Rat.div_def]

/-- Source closeOpen skips counting closed keys, drops empty counted keys, and otherwise closes points. -/
def closeOpenBucket (key : Key) (bucket : RecipeCompile.BucketMeta) :
    Except (LatticeAPI.Error String) (Option RecipeCompile.BucketMeta) :=
  if key.width = 0 then .ok (some bucket)
  else do
    let points ← LatticeAPI.points (names key.width) (lowerFormula key.formula)
    if points.count = 0 then pure none
    else pure (some (RecipeCompile.closeBucket key.width points.count.toNat bucket))

/-- A closed key preserves all metadata without evaluating its formula counter. -/
theorem closeOpen_zero (key : Key) (bucket : RecipeCompile.BucketMeta) (closed : key.width = 0) :
    closeOpenBucket key bucket = .ok (some bucket) := by simp [closeOpenBucket, closed]

/-- An open key keeps the exact counter error instead of treating the group as empty. -/
theorem closeOpen_error (key : Key) (bucket : RecipeCompile.BucketMeta) (openKey : key.width ≠ 0)
    (error : LatticeAPI.Error String)
    (failed : LatticeAPI.points (names key.width) (lowerFormula key.formula) = .error error) :
    closeOpenBucket key bucket = .error error := by
  simp [closeOpenBucket, openKey, failed, Bind.bind, Except.bind]

/-- A positive-width empty point table drops the group. -/
theorem closeOpen_empty (key : Key) (bucket : RecipeCompile.BucketMeta) (openKey : key.width ≠ 0)
    (points : LatticeAPI.Points)
    (built : LatticeAPI.points (names key.width) (lowerFormula key.formula) = .ok points)
    (empty : points.count = 0) : closeOpenBucket key bucket = .ok none := by
  simp [closeOpenBucket, openKey, built, empty, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Final closure preserves settled outer mass and adds each coordinate exactly once. -/
theorem closeOpen_kept (key : Key) (bucket : RecipeCompile.BucketMeta) (openKey : key.width ≠ 0)
    (points : LatticeAPI.Points)
    (built : LatticeAPI.points (names key.width) (lowerFormula key.formula) = .ok points)
    (nonempty : points.count ≠ 0) :
    closeOpenBucket key bucket = .ok (some ⟨bucket.mass, bucket.size + key.width,
      bucket.count * points.count.toNat, false,
      bucket.sizeMass.map (fun mass => mass * (points.count.toNat : Rat))⟩) := by
  simp [closeOpenBucket, openKey, built, nonempty, Bind.bind, Except.bind, Pure.pure, Except.pure,
    RecipeCompile.closeBucket]

end MicroCFTA.ParentIntegerSettlement
