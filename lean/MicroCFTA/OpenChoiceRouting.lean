import MicroCFTA.OpenIntegerSource
import MicroCFTA.Probability

/-!
# Open choice preflight, branch records, and finite mass

This is the metadata projection of compileOpen Chosen and Uniform.
The input list preserves child order. Each bucket list has the source map order.
The point recount callback retains its source error, including readable names.
-/
namespace MicroCFTA.OpenChoiceRouting
open OpenIntegerKeys Probability

attribute [local simp] LatticeLinear.except_bind_ok LatticeLinear.except_bind_error

/-- Source errors inspected by this caller. Other errors retain their identity. -/
inductive Error (Cause : Type) where
  | empty | unbounded | nonPositive (weight : Int) | recursiveWeights | other (cause : Cause)
  deriving DecidableEq, Repr

/-- One source key and its original member count. -/
structure Bucket where
  key : Key
  originals : Nat

/-- Recursive status is independent of an embedded source failure. -/
structure Family (Cause : Type) where
  cyclic : Bool
  result : Except (Error Cause) (List Bucket)

/-- finiteGroups followed by the stored count projection. -/
def cardinalities (family : Family Cause) : Except (Error Cause) (List Bucket) :=
  match family.result with
  | .error error => .error error
  | .ok buckets => if family.cyclic then .error .unbounded else .ok buckets

/-- A finite family is empty exactly when every stored count is zero. -/
def empty (family : Family Cause) : Bool :=
  match cardinalities family with
  | .error .empty => true
  | .error _ => false
  | .ok buckets => buckets.all (fun bucket => bucket.originals == 0)

/-- The source hides keys when cardinalities fails. -/
def openKeys (family : Family Cause) : List Key :=
  match cardinalities family with
  | .error _ => []
  | .ok buckets => buckets.map Bucket.key

/-- Recount supplies its diagnostic; success uses UnboundedGenerator as fallback. -/
def unknownError (recount : Key → Except (Error Cause) Nat) (key : Key) : Error Cause :=
  match recount key with
  | .error error => error
  | .ok _ => .unbounded

/-- The source live alternatives before weight validation. -/
def live (families : List (Family Cause)) := families.filter (fun family => !empty family)

/-- Unknown keys in alternative order and source map order. -/
def unknownKeys (families : List (Family Cause)) :=
  ((live families).flatMap openKeys).filter (fun key => key.points.isNone)

/-- Chosen rejects unknown points only when comparing multiple live alternatives. -/
def chosenPreflight (recount : Key → Except (Error Cause) Nat) (families : List (Family Cause)) :
    Except (Error Cause) Unit :=
  if 1 < (live families).length then
    match (unknownKeys families).head? with
    | some key => .error (unknownError recount key)
    | none => .ok ()
  else .ok ()

/-- One key contributes original members times available points. -/
def pointsOf (recount : Key → Except (Error Cause) Nat) (bucket : Bucket) : Except (Error Cause) Nat :=
  match bucket.key.points with
  | some found => .ok (bucket.originals * found)
  | none => .error (unknownError recount bucket.key)

/-- Source traverse followed by sum. Failure stops at the first unknown key. -/
def sumPoints (recount : Key → Except (Error Cause) Nat) : List Bucket → Except (Error Cause) Nat
  | [] => .ok 0
  | bucket :: rest => do
      let count ← pointsOf recount bucket
      let later ← sumPoints recount rest
      pure (count + later)

/-- cardinalities failure uses weight one. Grouped validation later reports embedded errors. -/
def members (recount : Key → Except (Error Cause) Nat) (family : Family Cause) : Except (Error Cause) Int :=
  match cardinalities family with
  | .error _ => .ok 1
  | .ok buckets => (sumPoints recount buckets).map Int.ofNat

/-- Source-order sequence separates outer child errors from later preflight errors. -/
def sequenceResults : List (Except ε α) → Except ε (List α)
  | [] => .ok []
  | first :: rest => do
      let value ← first
      let values ← sequenceResults rest
      pure (value :: values)

/-- Uniform counts members only for multiple live, nonrecursive alternatives. -/
def uniformWeights (recount : Key → Except (Error Cause) Nat) (families : List (Family Cause)) :
    Except (Error Cause) (List Int) :=
  if 1 < (live families).length ∧ families.any Family.cyclic = false then
    sequenceResults (families.map (members recount))
  else .ok (families.map (fun _ => 1))

/-- Original branch positions survive removal of empty alternatives. -/
structure Branch (Cause : Type) where
  index : Nat
  weight : Int
  family : Family Cause

/-- Execute zip [0..] and empty filtering in source order. -/
def chooseFrom (first : Nat) : List (Int × Family Cause) → List (Branch Cause)
  | [] => []
  | (weight, family) :: rest =>
      let later := chooseFrom (first + 1) rest
      if empty family then later else ⟨first, weight, family⟩ :: later

abbrev choose (weighted : List (Int × Family Cause)) := chooseFrom 0 weighted

/-- Chosen's outer error channel ends before grouped frequency validation. -/
def chosen (recount : Key → Except (Error Cause) Nat)
    (compiled : List (Except (Error Cause) (Int × Family Cause))) :
    Except (Error Cause) (List (Branch Cause)) := do
  let weighted ← sequenceResults compiled
  let _ ← chosenPreflight recount (weighted.map Prod.snd)
  pure (chooseFrom 0 weighted)

/-- Uniform derives weights before dropping empty alternatives. -/
def uniform (recount : Key → Except (Error Cause) Nat)
    (compiled : List (Except (Error Cause) (Family Cause))) :
    Except (Error Cause) (List (Branch Cause)) := do
  let groups ← sequenceResults compiled
  let weights ← uniformWeights recount groups
  pure (chooseFrom 0 (weights.zip groups))

/-- Retained nonpositive weights precede embedded source errors. -/
def badWeight : List (Branch Cause) → Option Int
  | [] => none
  | first :: rest => if first.weight ≤ 0 then some first.weight else badWeight rest

/-- EmptyGenerator is skipped; other embedded errors retain branch order. -/
def sourceError : List (Branch Cause) → Option (Error Cause)
  | [] => none
  | first :: rest =>
      match first.family.result with
      | .error .empty => sourceError rest
      | .error error => some error
      | .ok _ => sourceError rest

/-- frequencies' status gate. Bucket merging is a separate operation. -/
def frequenciesGate (branches : List (Branch Cause)) : Except (Error Cause) Bool :=
  match badWeight branches with
  | some weight => .error (.nonPositive weight)
  | none =>
      match sourceError branches with
      | some error => .error error
      | none =>
          match branches with
          | [] => .error .empty
          | first :: rest =>
              if branches.any (fun branch => branch.family.cyclic) then
                if rest.all (fun branch => branch.weight == first.weight) then .ok true
                else .error .recursiveWeights
              else .ok false

/-- A successful recount still produces the source fallback diagnostic. -/
theorem unknownError_success (recount : Key → Except (Error Cause) Nat) (key : Key) (found : Nat)
    (success : recount key = .ok found) : unknownError recount key = .unbounded := by
  simp [unknownError, success]

/-- A child failure precedes Chosen's cardinality gate. -/
theorem chosen_child_error (recount : Key → Except (Error Cause) Nat)
    (compiled : List (Except (Error Cause) (Int × Family Cause))) (error : Error Cause)
    (failed : sequenceResults compiled = .error error) : chosen recount compiled = .error error := by
  simp [chosen, failed]

/-- A child failure precedes Uniform's member computation. -/
theorem uniform_child_error (recount : Key → Except (Error Cause) Nat)
    (compiled : List (Except (Error Cause) (Family Cause))) (error : Error Cause)
    (failed : sequenceResults compiled = .error error) : uniform recount compiled = .error error := by
  simp [uniform, failed]

/-- A prefix of successful child calls exposes the first subsequent child error. -/
theorem sequence_first_error (before : List α) (error : ε) (after : List (Except ε α)) :
    sequenceResults (before.map Except.ok ++ .error error :: after) = .error error := by
  induction before with
  | nil => rfl
  | cons first rest ih => simp [sequenceResults, ih]; rfl

/-- The first unknown key gives the exact preflight error. -/
theorem chosen_first_unknown (recount : Key → Except (Error Cause) Nat) (families : List (Family Cause))
    (multiple : 1 < (live families).length) (first : Key) (rest : List Key)
    (keys : unknownKeys families = first :: rest) :
    chosenPreflight recount families = .error (unknownError recount first) := by
  simp [chosenPreflight, multiple, keys]

/-- A successful comparison of multiple alternatives has no unknown finite key. -/
theorem chosen_known (recount : Key → Except (Error Cause) Nat) (families : List (Family Cause))
    (multiple : 1 < (live families).length) (success : chosenPreflight recount families = .ok ()) :
    unknownKeys families = [] := by
  cases keys : unknownKeys families with
  | nil => rfl
  | cons first rest => simp [chosenPreflight, multiple, keys] at success

/-- An unknown key that passes Chosen can belong only to a single live alternative. -/
theorem unknown_chosen_single (recount : Key → Except (Error Cause) Nat) (families : List (Family Cause))
    (unknown : unknownKeys families ≠ []) (success : chosenPreflight recount families = .ok ()) :
    (live families).length ≤ 1 := by
  by_cases multiple : 1 < (live families).length
  · exact False.elim (unknown (chosen_known recount families multiple success))
  · omega

/-- Single-live preflight permits unknown points without an infinite-uniform claim. -/
theorem chosen_single (recount : Key → Except (Error Cause) Nat) (families : List (Family Cause))
    (single : (live families).length ≤ 1) : chosenPreflight recount families = .ok () := by
  simp [chosenPreflight, Nat.not_lt.mpr single]

/-- The singleton route uses unit weights without invoking the point counter. -/
theorem uniform_single (recount : Key → Except (Error Cause) Nat) (families : List (Family Cause))
    (single : (live families).length ≤ 1) :
    uniformWeights recount families = .ok (families.map (fun _ => 1)) := by
  simp [uniformWeights, Nat.not_lt.mpr single]

/-- Any recursive family selects unit weights. -/
theorem uniform_recursive (recount : Key → Except (Error Cause) Nat) (families : List (Family Cause))
    (recursive : families.any Family.cyclic = true) :
    uniformWeights recount families = .ok (families.map (fun _ => 1)) := by
  simp [uniformWeights, recursive]

/-- members defers an embedded source failure rather than declaring an empty family. -/
theorem members_failed (recount : Key → Except (Error Cause) Nat) (cyclic : Bool) (error : Error Cause) :
    members recount ⟨cyclic, .error error⟩ = .ok 1 := by
  simp [members, cardinalities]

/-- Recursive success uses the explicit members fallback. -/
theorem members_recursive (recount : Key → Except (Error Cause) Nat) (buckets : List Bucket) :
    members recount ⟨true, .ok buckets⟩ = .ok 1 := by
  simp [members, cardinalities]

/-- Retained identifiers are in the original input index interval. -/
theorem choose_bounds (first : Nat) (weighted : List (Int × Family Cause)) (branch : Branch Cause)
    (present : branch ∈ chooseFrom first weighted) :
    first ≤ branch.index ∧ branch.index < first + weighted.length := by
  induction weighted generalizing first with
  | nil => simp [chooseFrom] at present
  | cons entry rest ih =>
      rcases entry with ⟨weight, family⟩
      by_cases gone : empty family = true
      · have bound := ih (first + 1) (by simpa [chooseFrom, gone] using present)
        simp only [List.length_cons]; omega
      · simp only [chooseFrom, gone, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at present
        rcases present with rfl | present
        · simp
        · have bound := ih (first + 1) present
          simp only [List.length_cons]; omega

/-- An empty first alternative increments the next branch index. -/
theorem choose_gap (first : Nat) (weight : Int) (family : Family Cause)
    (rest : List (Int × Family Cause)) (gone : empty family = true) :
    chooseFrom first ((weight, family) :: rest) = chooseFrom (first + 1) rest := by
  simp [chooseFrom, gone]

/-- Empty branches cannot invalidate their unused weights after chooseGroups filtering. -/
theorem choose_empty_weight (first : Nat) (left right : Int) (family : Family Cause)
    (rest : List (Int × Family Cause)) (gone : empty family = true) :
    chooseFrom first ((left, family) :: rest) = chooseFrom first ((right, family) :: rest) := by
  simp [chooseFrom, gone]

/-- Known point records give the exact sum used as branch weight. -/
theorem sumPoints_known (recount : Key → Except (Error Cause) Nat) (buckets : List Bucket)
    (counts : Bucket → Nat) (known : ∀ bucket ∈ buckets, bucket.key.points = some (counts bucket)) :
    sumPoints recount buckets = .ok ((buckets.map (fun bucket => bucket.originals * counts bucket)).sum) := by
  induction buckets with
  | nil => rfl
  | cons bucket rest ih =>
      simp [sumPoints, pointsOf, known bucket (by simp), ih (fun b hb => known b (by simp [hb]))]
      rfl

/-- A finite Uniform weight is derived from original and point counts. -/
theorem members_known (recount : Key → Except (Error Cause) Nat) (buckets : List Bucket)
    (counts : Bucket → Nat) (known : ∀ bucket ∈ buckets, bucket.key.points = some (counts bucket)) :
    members recount ⟨false, .ok buckets⟩ =
      .ok (((buckets.map (fun bucket => bucket.originals * counts bucket)).sum : Nat) : Int) := by
  simp [members, cardinalities, sumPoints_known recount buckets counts known, Except.map]

/-- Closure retains one position per original member and integer tuple. -/
def closedPositions (bucket : Bucket) (points : LatticeAPI.Points) : List (Nat × List Int) :=
  (List.range bucket.originals).flatMap fun rank =>
    (OpenIntegerSource.pointDomain points).map (fun tuple => (rank, tuple))

/-- Actual successful point construction derives original-times-points cardinality. -/
theorem closedPositions_count (bucket : Bucket) (points : LatticeAPI.Points)
    (built : LatticeAPI.points (names bucket.key.width) (FullSyntax.lowerFormula bucket.key.formula) = .ok points) :
    (closedPositions bucket points).length = bucket.originals * points.count.toNat := by
  simp only [closedPositions, List.length_flatMap, List.length_map]
  rw [OpenIntegerSource.pointDomain_count _ _ points built]
  have sumConstant (items : List Nat) (count : Nat) :
      (items.map (fun _ => count)).sum = items.length * count := by
    induction items with
    | nil => simp
    | cons first rest ih => simp [ih, Nat.add_mul, Nat.add_comm]
  simpa using sumConstant (List.range bucket.originals) points.count.toNat

/-- The stored point record derives weight from actual closed replay positions. -/
theorem pointsOf_positions (recount : Key → Except (Error Cause) Nat) (bucket : Bucket)
    (points : LatticeAPI.Points)
    (built : LatticeAPI.points (names bucket.key.width) (FullSyntax.lowerFormula bucket.key.formula) = .ok points)
    (stored : bucket.key.points = some points.count.toNat) :
    pointsOf recount bucket = .ok (closedPositions bucket points).length := by
  rw [closedPositions_count bucket points built]
  simp [pointsOf, stored]

/-- Any successful sum proves every inspected key has a known point count. -/
theorem sumPoints_success_known (recount : Key → Except (Error Cause) Nat) (buckets : List Bucket)
    (count : Nat) (success : sumPoints recount buckets = .ok count) :
    ∀ bucket ∈ buckets, bucket.key.points ≠ none := by
  induction buckets generalizing count with
  | nil => simp
  | cons first rest ih =>
      cases firstCount : first.key.points with
      | none => simp [sumPoints, pointsOf, firstCount] at success
      | some points =>
          cases later : sumPoints recount rest with
          | error error => simp [sumPoints, pointsOf, firstCount, later, Functor.map, Except.map] at success
          | ok found =>
              intro bucket present
              rcases List.mem_cons.mp present with rfl | present
              · simp [firstCount]
              · exact ih found later bucket present

/-- A known prefix does not change the first unknown-key diagnostic. -/
theorem sumPoints_first_unknown (recount : Key → Except (Error Cause) Nat)
    (before : List Bucket) (bucket : Bucket) (after : List Bucket)
    (known : ∀ entry ∈ before, entry.key.points ≠ none) (unknown : bucket.key.points = none) :
    sumPoints recount (before ++ bucket :: after) = .error (unknownError recount bucket.key) := by
  induction before with
  | nil => simp [sumPoints, pointsOf, unknown]
  | cons first rest ih =>
      cases found : first.key.points with
      | none => exact False.elim (known first (by simp) found)
      | some value =>
          simp [sumPoints, pointsOf, found, ih (fun entry member => known entry (by simp [member]))]
          rfl

/-- Successful sequence retains a successful result for every source call. -/
theorem sequence_success (results : List (Except ε α)) (values : List α)
    (success : sequenceResults results = .ok values) :
    ∀ result ∈ results, ∃ value, result = .ok value := by
  induction results generalizing values with
  | nil => simp
  | cons first rest ih =>
      cases first with
      | error error => simp [sequenceResults] at success
      | ok value =>
          cases next : sequenceResults rest with
          | error error => simp [sequenceResults, next, Functor.map, Except.map] at success
          | ok later =>
              intro result member
              rcases List.mem_cons.mp member with rfl | member
              · exact ⟨value, rfl⟩
              · exact ih later next result member

/-- Multiple nonrecursive Uniform alternatives cannot hide an unknown point count. -/
theorem uniform_known (recount : Key → Except (Error Cause) Nat) (families : List (Family Cause))
    (multiple : 1 < (live families).length) (nonrecursive : families.any Family.cyclic = false)
    (weights : List Int) (success : uniformWeights recount families = .ok weights) :
    unknownKeys families = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro key member
  obtain ⟨family, present, keyPresent⟩ := List.mem_flatMap.mp member
  have original := (List.mem_filter.mp present).1
  have sequenced : sequenceResults (families.map (members recount)) = .ok weights := by
    simpa [uniformWeights, multiple, nonrecursive] using success
  obtain ⟨weight, counted⟩ := sequence_success _ _ sequenced _ (List.mem_map.mpr ⟨family, original, rfl⟩)
  cases source : cardinalities family with
  | error error => simp [openKeys, source] at keyPresent
  | ok buckets =>
      obtain ⟨bucket, bucketPresent, rfl⟩ := List.mem_map.mp (by simpa [openKeys, source] using keyPresent)
      cases total : sumPoints recount buckets with
      | error error => simp [members, source, total, Except.map] at counted
      | ok count =>
          have known := sumPoints_success_known recount buckets count total bucket bucketPresent
          cases points : bucket.key.points with
          | none => exact False.elim (known points)
          | some pointCount => simp

/-- Uniform can retain unknown points only through its singleton or recursive fallback. -/
theorem unknown_uniform_route (recount : Key → Except (Error Cause) Nat) (families : List (Family Cause))
    (unknown : unknownKeys families ≠ []) (weights : List Int)
    (success : uniformWeights recount families = .ok weights) :
    (live families).length ≤ 1 ∨ families.any Family.cyclic = true := by
  by_cases multiple : 1 < (live families).length
  · cases recursive : families.any Family.cyclic with
    | false => exact False.elim (unknown (uniform_known recount families multiple recursive weights success))
    | true => exact Or.inr rfl
  · exact Or.inl (by omega)

/-- The list of retained branch identifiers is strictly increasing. -/
theorem choose_ordered (first : Nat) (weighted : List (Int × Family Cause)) :
    (chooseFrom first weighted).Pairwise (fun left right => left.index < right.index) := by
  induction weighted generalizing first with
  | nil => simp [chooseFrom]
  | cons entry rest ih =>
      rcases entry with ⟨weight, family⟩
      by_cases gone : empty family = true
      · simpa [chooseFrom, gone] using ih (first + 1)
      · simp only [chooseFrom, gone, Bool.false_eq_true, ↓reduceIte, List.pairwise_cons]
        exact ⟨fun branch present => by have bound := choose_bounds (first + 1) rest branch present; omega,
          ih (first + 1)⟩

/-- A source zero-count family never contributes an alternative, regardless of its open points. -/
theorem zero_family_empty (buckets : List Bucket) (zero : ∀ bucket ∈ buckets, bucket.originals = 0) :
    empty (⟨false, .ok buckets⟩ : Family Cause) = true := by
  simp only [empty, cardinalities, Bool.false_eq_true, ↓reduceIte, List.all_eq_true]
  intro bucket member
  simp [zero bucket member]

/-- The number of branch weights is exactly the number of source alternatives on success. -/
theorem sequence_length (results : List (Except ε α)) (values : List α)
    (success : sequenceResults results = .ok values) : values.length = results.length := by
  induction results generalizing values with
  | nil =>
      have same : values = [] := Except.ok.inj success.symm
      simp [same]
  | cons first rest ih =>
      cases first with
      | error error => simp [sequenceResults] at success
      | ok value =>
          cases later : sequenceResults rest with
          | error error => simp [sequenceResults, later, Functor.map, Except.map] at success
          | ok output =>
              have same : values = value :: output := by
                simpa [sequenceResults, later, Functor.map, Except.map] using success.symm
              simp [same, ih output later]

/-- zip cannot silently drop an alternative after successful Uniform weighting. -/
theorem uniform_weights_length (recount : Key → Except (Error Cause) Nat) (families : List (Family Cause))
    (weights : List Int) (success : uniformWeights recount families = .ok weights) :
    weights.length = families.length := by
  unfold uniformWeights at success
  split at success
  · simpa using sequence_length _ weights success
  · have same : weights = families.map (fun _ => 1) := Except.ok.inj success.symm
    simp [same]

/-- Finite groups retain every original replay position and every admitted lattice point. -/
def familyPositions (buckets : List Bucket) (tables : Bucket → LatticeAPI.Points) :=
  buckets.flatMap (fun bucket => closedPositions bucket (tables bucket))

/-- Uniform derives a finite family's weight from the complete closed position list. -/
theorem members_positions (recount : Key → Except (Error Cause) Nat) (buckets : List Bucket)
    (tables : Bucket → LatticeAPI.Points)
    (built : ∀ bucket ∈ buckets, LatticeAPI.points (names bucket.key.width)
      (FullSyntax.lowerFormula bucket.key.formula) = .ok (tables bucket))
    (stored : ∀ bucket ∈ buckets, bucket.key.points = some (tables bucket).count.toNat) :
    members recount ⟨false, .ok buckets⟩ = .ok ((familyPositions buckets tables).length : Int) := by
  rw [members_known recount buckets (fun bucket => (tables bucket).count.toNat) stored]
  congr 2
  simp only [familyPositions, List.length_flatMap]
  congr 1
  apply List.map_congr_left
  intro bucket present
  exact (closedPositions_count bucket (tables bucket) (built bucket present)).symm

/-- The source finite frequencies scale each bucket by its retained external weight share. -/
def bucketShare (branches : List (Branch Cause)) (branch : Branch Cause) (mass : Rat) : Rat :=
  (branch.weight : Rat) / ((branches.map Branch.weight).sum : Rat) * mass

/-- Actual bucket-mass scaling preserves each branch's internal relative weights. -/
theorem bucketShare_add (branches : List (Branch Cause)) (branch : Branch Cause) (left right : Rat) :
    bucketShare branches branch (left + right) = bucketShare branches branch left + bucketShare branches branch right := by
  simp [bucketShare, Rat.mul_add]

/-- The finite branch distribution uses the existing exact frequency interpretation. -/
def distribution (branches : List (Branch Cause)) (outcomes : Branch Cause → Distribution Value) : Distribution Value :=
  Probability.frequency (branches.map (fun branch => ((branch.weight : Rat), outcomes branch)))

/-- Every event gets its weighted branch numerator divided by the retained total weight. -/
theorem distribution_event (branches : List (Branch Cause)) (outcomes : Branch Cause → Distribution Value)
    (event : Value → Bool) :
    eventMass event (distribution branches outcomes) =
      weightedEvent event (branches.map (fun branch => ((branch.weight : Rat), outcomes branch))) /
        branchWeight (branches.map (fun branch => ((branch.weight : Rat), outcomes branch))) :=
  eventMass_frequency event _

/-- Positive weights and normalized finite branch records derive a normalized distribution. -/
theorem distribution_probability (branches : List (Branch Cause)) (outcomes : Branch Cause → Distribution Value)
    (valid : ∀ branch ∈ branches, 0 ≤ (branch.weight : Rat) ∧ IsProbability (outcomes branch))
    (positive : 0 < branchWeight (branches.map (fun branch => ((branch.weight : Rat), outcomes branch)))) :
    IsProbability (distribution branches outcomes) := by
  apply frequency_probability _ _ positive
  intro entry present
  obtain ⟨branch, member, rfl⟩ := List.mem_map.mp present
  exact valid branch member

/-- A source traverse of known successful calls returns their values in order. -/
theorem sequence_map_success (items : List α) (operation : α → Except ε β) (values : α → β)
    (success : ∀ item ∈ items, operation item = .ok (values item)) :
    sequenceResults (items.map operation) = .ok (items.map values) := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
      simp [sequenceResults, success first (by simp), ih (fun item present => success item (by simp [present]))]
      rfl

/-- Multiple finite alternatives get their actual closed replay counts as source weights. -/
theorem uniform_finite_positions (recount : Key → Except (Error Cause) Nat) (alternatives : List (List Bucket))
    (tables : Bucket → LatticeAPI.Points)
    (built : ∀ buckets ∈ alternatives, ∀ bucket ∈ buckets,
      LatticeAPI.points (names bucket.key.width) (FullSyntax.lowerFormula bucket.key.formula) = .ok (tables bucket))
    (stored : ∀ buckets ∈ alternatives, ∀ bucket ∈ buckets, bucket.key.points = some (tables bucket).count.toNat)
    (multiple : 1 < (live (alternatives.map (fun buckets => (⟨false, .ok buckets⟩ : Family Cause)))).length) :
    uniformWeights recount (alternatives.map (fun buckets => ⟨false, .ok buckets⟩)) =
      .ok (alternatives.map (fun buckets => ((familyPositions buckets tables).length : Int))) := by
  have noRecursive : (alternatives.map (fun buckets => (⟨false, .ok buckets⟩ : Family Cause))).any Family.cyclic = false := by
    simp
  simp only [uniformWeights, multiple, noRecursive, and_self, ↓reduceIte, List.map_map, Function.comp_def]
  exact sequence_map_success alternatives _ _ (fun buckets present =>
    members_positions recount buckets tables (built buckets present) (stored buckets present))

/-- Multiplying a uniform finite branch by its cardinality restores one unit per member. -/
theorem cardinality_scale (values : List Value) :
    scale (values.length : Rat) (normalize (counting values)) = counting values := by
  cases values with
  | nil => rfl
  | cons first rest =>
      rw [normalize, total_counting, scale_scale]
      have nonzero : ((first :: rest).length : Rat) ≠ 0 :=
        Rat.ne_of_gt (Rat.natCast_pos.mpr (by simp))
      rw [Rat.mul_inv_cancel _ nonzero, scale_one]

/-- Count-weighted alternatives are globally uniform exactly when their own members are uniform. -/
theorem uniform_counting (alternatives : List (List Value)) :
    frequency (alternatives.map (fun values => ((values.length : Rat), normalize (counting values)))) =
      normalize (counting alternatives.flatten) := by
  have numerator : mix (alternatives.map (fun values => ((values.length : Rat), normalize (counting values)))) =
      counting alternatives.flatten := by
    induction alternatives with
    | nil => rfl
    | cons first rest ih =>
        simp only [List.map_cons, mix, cardinality_scale, ih, List.flatten_cons]
        simp [counting, List.map_append]
  have denominator : branchWeight
      (alternatives.map (fun values => ((values.length : Rat), normalize (counting values)))) =
      (alternatives.flatten.length : Rat) := by
    clear numerator
    induction alternatives with
    | nil => simp [branchWeight]
    | cons first rest ih => simp [branchWeight, ih, Rat.natCast_add]
  rw [frequency, numerator, denominator, normalize, total_counting]

/-- A rank interval keeps its source branch identifier separate from its cumulative member offset. -/
structure Interval where
  branch : Nat
  offset : Nat
  count : Nat

/-- Finite merge intervals advance by cardinality, independently of branch weights. -/
def intervals (count : Family Cause → Nat) (offset : Nat) : List (Branch Cause) → List Interval
  | [] => []
  | branch :: rest => ⟨branch.index, offset, count branch.family⟩ ::
      intervals count (offset + count branch.family) rest

/-- Every local rank lies in the half-open interval assigned to its finite branch. -/
theorem interval_rank (interval : Interval) (rank : Nat) (bound : rank < interval.count) :
    interval.offset ≤ interval.offset + rank ∧ interval.offset + rank < interval.offset + interval.count := by omega

/-- Every finite interval is within the total cardinality range. -/
theorem intervals_bounds (count : Family Cause → Nat) (offset : Nat) (branches : List (Branch Cause))
    (interval : Interval) (present : interval ∈ intervals count offset branches) :
    offset ≤ interval.offset ∧ interval.offset + interval.count ≤
      offset + (branches.map (fun branch => count branch.family)).sum := by
  induction branches generalizing offset with
  | nil => simp [intervals] at present
  | cons first rest ih =>
      simp only [intervals, List.mem_cons] at present
      rcases present with rfl | present
      · simp
      · have bound := ih (offset + count first.family) present
        simp only [List.map_cons, List.sum_cons]; omega

/-- Rank intervals are disjoint even if two branches contain equal decoded values. -/
theorem intervals_disjoint (count : Family Cause → Nat) (offset : Nat) (branches : List (Branch Cause)) :
    (intervals count offset branches).Pairwise (fun left right => left.offset + left.count ≤ right.offset) := by
  induction branches generalizing offset with
  | nil => simp [intervals]
  | cons first rest ih =>
      simp only [intervals, List.pairwise_cons]
      exact ⟨fun interval present => (intervals_bounds count _ rest interval present).1, ih _⟩

/-- Preflight unknown errors precede retained invalid weights in the Chosen outer channel. -/
theorem unknown_precedes_weight :
    let unknown : Family String := ⟨false, .ok [⟨⟨1, .top, none⟩, 1⟩]⟩
    let known : Family String := ⟨false, .ok [⟨⟨1, .top, some 2⟩, 1⟩]⟩
    chosen (fun _ => .error (.other "unknown points")) [.ok (-1, unknown), .ok (1, known)] =
      .error (.other "unknown points") := by rfl

/-- A singleton unknown alternative passes only the outer metadata route. -/
theorem singleton_unknown_route :
    let family : Family String := ⟨false, .ok [⟨⟨1, .top, none⟩, 1⟩]⟩
    uniform (fun _ => .error (.other "unknown points")) [.ok family] = .ok [⟨0, 1, family⟩] := by rfl

/-- Every retained branch keeps its complete original family and external weight. -/
theorem choose_records (first : Nat) (weighted : List (Int × Family Cause)) (branch : Branch Cause)
    (present : branch ∈ chooseFrom first weighted) :
    (branch.weight, branch.family) ∈ weighted ∧ empty branch.family = false := by
  induction weighted generalizing first with
  | nil => simp [chooseFrom] at present
  | cons entry rest ih =>
      rcases entry with ⟨weight, family⟩
      cases gone : empty family with
      | true =>
          have kept := ih (first + 1) (by simpa [chooseFrom, gone] using present)
          exact ⟨List.mem_cons_of_mem _ kept.1, kept.2⟩
      | false =>
          simp only [chooseFrom, gone, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at present
          rcases present with rfl | present
          · exact ⟨by simp, gone⟩
          · have kept := ih (first + 1) present
            exact ⟨List.mem_cons_of_mem _ kept.1, kept.2⟩

/-- Every nonempty source alternative survives with its original occurrence identifier. -/
theorem choose_complete (first : Nat) (weighted : List (Int × Family Cause)) (rank : Nat)
    (weight : Int) (family : Family Cause) (atRank : weighted[rank]? = some (weight, family))
    (nonempty : empty family = false) :
    (⟨first + rank, weight, family⟩ : Branch Cause) ∈ chooseFrom first weighted := by
  induction weighted generalizing first rank with
  | nil => simp at atRank
  | cons entry rest ih =>
      rcases entry with ⟨headWeight, headFamily⟩
      cases rank with
      | zero =>
          have same : (headWeight, headFamily) = (weight, family) := by simpa using atRank
          cases same
          simp [chooseFrom, nonempty]
      | succ rank =>
          have later := ih (first + 1) rank (by simpa using atRank)
          have shifted : first + (rank + 1) = first + 1 + rank := by omega
          cases gone : empty headFamily <;> simp [chooseFrom, gone, shifted, later]

/-- Grouped weight validation precedes an embedded error once the outer preflight succeeds. -/
theorem weight_error_first (branches : List (Branch Cause)) (weight : Int)
    (bad : badWeight branches = some weight) : frequenciesGate branches = .error (.nonPositive weight) := by
  simp [frequenciesGate, bad]

/-- With valid retained weights, the first embedded source error is preserved. -/
theorem embedded_error_next (branches : List (Branch Cause)) (error : Error Cause)
    (weights : badWeight branches = none) (failed : sourceError branches = some error) :
    frequenciesGate branches = .error error := by
  simp [frequenciesGate, weights, failed]

/-- Uniform inspects every finite key during its counting route, including an empty record. -/
theorem uniform_empty_unknown_checked :
    let unknown : Family String := ⟨false, .ok [⟨⟨1, .top, none⟩, 0⟩]⟩
    let known : Family String := ⟨false, .ok [⟨⟨1, .top, some 2⟩, 1⟩]⟩
    uniformWeights (fun _ => .error (.other "unknown points")) [known, unknown, known] =
      .error (.other "unknown points") := by rfl

/-- Chosen excludes that same empty record from its unknown-key scan. -/
theorem chosen_empty_unknown_ignored :
    let unknown : Family String := ⟨false, .ok [⟨⟨1, .top, none⟩, 0⟩]⟩
    let known : Family String := ⟨false, .ok [⟨⟨1, .top, some 2⟩, 1⟩]⟩
    chosenPreflight (fun _ => .error (.other "unknown points")) [known, unknown, known] = .ok () := by rfl

end MicroCFTA.OpenChoiceRouting
