import MicroCFTA.FinalSizeFields

/-!
# Static sampler flags and atomic size provenance

The atomic marker takes priority over a stored class sampler. Ordinary
records use that sampler when present and use member counts otherwise.
The size of an atom comes from its plan. The constructor relation records
which operations preserve a positive atomic size.
-/
namespace MicroCFTA.StaticSamplingDispatch
open Probability SourcePlanPositions FiniteSizeFields

/-- The fields read by the source static sampler. Retained bucket masses are separate. -/
structure Fields (Value : Type) where
  plan : Plan
  outcomes : Distribution Value
  atomic : Bool
  minimum : Option Nat
  uniformMass : Option Rat
  storedWeights : Option (Nat → Distribution Nat)

/-- The three source branches, in guard order. -/
inductive Branch where
  | atomic | stored | uniform
  deriving DecidableEq, Repr

/-- The atomic flag has priority even when an earlier class sampler is stored. -/
def branch (fields : Fields Value) : Branch :=
  if fields.atomic then .atomic else if fields.storedWeights.isSome then .stored else .uniform

/-- The source uses size one when the atom has no finite member. -/
def atomSize (fields : Fields Value) : Nat := fields.minimum.getD 1

/-- Construct count-scale weights exactly as staticSampling does. -/
def sampling (fields : Fields Value) : Record :=
  if fields.atomic then
    { atomic (atomSize fields) fields.outcomes with plan := fields.plan }
  else
    match fields.storedWeights with
    | some weights => ⟨fields.plan, weights, none⟩
    | none => uniform fields.plan

/-- The optional weight callback has the same priority as the sampler. -/
def hasWeight (fields : Fields Value) : Bool :=
  if fields.atomic then fields.uniformMass.isNone else fields.storedWeights.isSome

/-- Primitive constructors clear the atomic marker. Atom, map, and pay set or preserve it.
A resize preserves the marker, so a positive requested size is needed for an atom. -/
inductive Origin : Bool → Option Nat → Plan → Prop where
  | ordinary (plan : Plan) (minimum : Option Nat) : Origin false minimum plan
  | atom (count : Nat) : Origin true (if count = 0 then none else some 1) (.select count)
  | map {flag minimum plan} : Origin flag minimum plan → Origin flag minimum (.map plan)
  | pay {flag minimum plan} : Origin flag minimum plan →
      Origin flag (minimum.map (· + 1)) (.pay plan)
  | resize {flag minimum plan} (size : Nat) : Origin flag minimum plan →
      (flag = true → 0 < size) →
      Origin flag (if count plan = 0 then none else some size) (fixedPlan size (count plan))

/-- Every nonempty constructed atom occupies one positive size and retains original rank order. -/
theorem origin_atomic {flag : Bool} {minimum : Option Nat} {plan : Plan}
    (origin : Origin flag minimum plan) (marked : flag = true) (live : 0 < count plan) :
    ∃ size, 0 < size ∧ minimum = some size ∧
      ∀ found, classRanks plan found = if found = size then List.range (count plan) else [] := by
  induction origin with
  | ordinary plan minimum => contradiction
  | atom count =>
      refine ⟨1, by omega, ?_, ?_⟩
      · simp [show count ≠ 0 by simpa only [SourcePlanPositions.count] using Nat.ne_of_gt live]
      · intro found; rfl
  | map origin ih => exact ih marked live
  | pay origin ih =>
      obtain ⟨size, positive, same, shape⟩ := ih marked live
      refine ⟨size + 1, by omega, by simp [same], ?_⟩
      intro found
      cases found with
      | zero => simp [classRanks]
      | succ found => simpa [classRanks, count] using shape found
  | resize size origin positive ih =>
      have before := live
      rw [fixedPlan_count] at before
      refine ⟨size, positive marked, by simp [Nat.ne_of_gt before], ?_⟩
      intro found
      simp [fixedPlan_classes, fixedPlan_count]

/-- An atom with a reported minimum cannot have size zero under constructor provenance. -/
theorem origin_no_zero {minimum : Option Nat} {plan : Plan}
    (origin : Origin true minimum plan) (live : 0 < count plan) : minimum ≠ some 0 := by
  obtain ⟨size, positive, same, _⟩ := origin_atomic origin rfl live
  rw [same]
  intro impossible
  have := Option.some.inj impossible
  omega

/-- Common atom constructors derive the exact fallback size used by staticSampling. -/
theorem origin_atomSize (fields : Fields Value)
    (origin : Origin fields.atomic fields.minimum fields.plan)
    (marked : fields.atomic = true) (live : 0 < count fields.plan) :
    0 < atomSize fields ∧ ∀ found,
      classRanks fields.plan found = if found = atomSize fields then List.range (count fields.plan) else [] := by
  obtain ⟨size, positive, same, shape⟩ := origin_atomic origin marked live
  simpa [atomSize, same] using And.intro positive shape

/-- Equal ordered class lists transport size validity; no rank or weight property is assumed. -/
theorem replace_plan_valid (record : Record) (valid : Valid record) (plan : Plan)
    (classes : ∀ size, classRanks plan size = classRanks record.plan size) :
    Valid { record with plan := plan } := by
  constructor
  · intro size; simpa only [classes] using valid.ranks size
  · exact valid.positive
  · intro size; simpa only [classes] using valid.total size
  · intro size
    have sameMass : massAt { record with plan := plan } size = massAt record size := by
      cases same : record.retained <;> simp [massAt, classes, same]
    simpa only [classes, sameMass] using valid.mass size

/-- A normalized finite distribution has at least one member. -/
theorem probability_live (outcomes : Distribution Value) (probability : IsProbability outcomes) :
    0 < outcomes.length := by
  apply List.length_pos_iff.mpr
  intro empty
  have normalized := probability.2
  simp [empty, total] at normalized

/-- The atomic branch derives its weights from actual global masses and plan provenance. -/
theorem sampling_atomic_valid (fields : Fields Value)
    (origin : Origin fields.atomic fields.minimum fields.plan) (marked : fields.atomic = true)
    (counts : count fields.plan = fields.outcomes.length)
    (probability : IsProbability fields.outcomes)
    (positive : ∀ entry ∈ fields.outcomes, 0 < entry.1) : Valid (sampling fields) := by
  rw [sampling, marked]
  simp only [↓reduceIte]
  apply replace_plan_valid _ (atomic_valid _ _ probability positive)
  intro size
  have shape := (origin_atomSize fields origin marked (by rw [counts]; exact probability_live _ probability)).2 size
  simpa [atomic, fixedPlan_classes, counts] using shape

/-- The stored branch needs only its local class-weight invariant. -/
theorem sampling_stored (fields : Fields Value) (weights : Nat → Distribution Nat)
    (ordinary : fields.atomic = false) (stored : fields.storedWeights = some weights) :
    sampling fields = ⟨fields.plan, weights, none⟩ ∧ branch fields = .stored ∧ hasWeight fields = true := by
  simp [sampling, branch, hasWeight, ordinary, stored]

/-- The fallback branch builds uniform weights from the actual plan. -/
theorem sampling_uniform (fields : Fields Value)
    (ordinary : fields.atomic = false) (absent : fields.storedWeights = none) :
    sampling fields = uniform fields.plan ∧ branch fields = .uniform ∧ hasWeight fields = false := by
  simp [sampling, branch, hasWeight, ordinary, absent]

/-- Removing the external retained mass table leaves every Static sampling field valid. -/
theorem forget_retained_valid (record : Record) (valid : Valid record) :
    Valid { record with retained := none } :=
  ⟨valid.ranks, valid.positive, valid.total, (uniform_valid record.plan).mass⟩

/-- All source sampling branches derive validity from constructor provenance and local stored fields. -/
theorem sampling_valid (fields : Fields Value)
    (origin : Origin fields.atomic fields.minimum fields.plan)
    (counts : count fields.plan = fields.outcomes.length)
    (probability : IsProbability fields.outcomes)
    (positive : ∀ entry ∈ fields.outcomes, 0 < entry.1)
    (stored : ∀ weights, fields.storedWeights = some weights → Valid ⟨fields.plan, weights, none⟩) :
    Valid (sampling fields) := by
  cases marked : fields.atomic with
  | true => exact sampling_atomic_valid fields origin marked counts probability positive
  | false =>
      cases available : fields.storedWeights with
      | none => simpa [sampling, marked, available] using uniform_valid fields.plan
      | some weights => simpa [sampling, marked, available] using stored weights available

/-- Stored class weights cannot override an atomic source distribution. -/
theorem atomic_priority (fields : Fields Value) (marked : fields.atomic = true) :
    branch fields = .atomic ∧
    sampling fields = { atomic (atomSize fields) fields.outcomes with plan := fields.plan } ∧
    hasWeight fields = fields.uniformMass.isNone := by
  simp [branch, sampling, hasWeight, marked]

/-- The dispatched sampler keeps the global law of each atom at its actual source size. -/
theorem sampling_atomic_probability (fields : Fields Value)
    (origin : Origin fields.atomic fields.minimum fields.plan) (marked : fields.atomic = true)
    (counts : count fields.plan = fields.outcomes.length) (live : fields.outcomes ≠ []) :
    FiniteSizeSampling.sample (sampling fields) (atomSize fields) = rankedMasses fields.outcomes := by
  have shape := (origin_atomSize fields origin marked
    (by rw [counts]; exact List.length_pos_iff.mpr live)).2 (atomSize fields)
  simp only [sampling, marked, ↓reduceIte, FiniteSizeSampling.sample]
  change scale ((classRanks fields.plan (atomSize fields)).length : Rat)⁻¹
    ((atomic (atomSize fields) fields.outcomes).weights (atomSize fields)) = _
  rw [shape]
  simpa [atomic, fixedPlan_classes, counts] using atomic_probability (atomSize fields) fields.outcomes live

/-- The source weight callback is unnecessary when all global atomic masses are uniform. -/
theorem uniform_atom_weights (outcomes : Distribution Value) (live : outcomes ≠ [])
    (uniform : rankedMasses outcomes = scale (outcomes.length : Rat)⁻¹ (counting (List.range outcomes.length))) :
    scale (outcomes.length : Rat) (rankedMasses outcomes) = counting (List.range outcomes.length) := by
  rw [uniform, scale_scale, Rat.mul_inv_cancel _
    (Rat.ne_of_gt (Rat.natCast_pos.mpr (List.length_pos_iff.mpr live))), scale_one]

/-- A common source mass gives the same ordered rank list with that mass at each rank. -/
theorem common_mass_ranks (outcomes : Distribution Value) (mass : Rat)
    (common : ∀ entry ∈ outcomes, entry.1 = mass) :
    rankedMasses outcomes = scale mass (counting (List.range outcomes.length)) := by
  rw [← rankedMasses_ranks outcomes]
  simp only [scale, counting, rankedMasses, List.map_map, Function.comp_def, Rat.mul_one]
  apply List.map_congr_left
  intro entry member
  have same := common entry.1 (List.fst_mem_of_mem_zipIdx member)
  simp [same]

/-- Normalization makes suppression of an atomic uniform-weight callback exact. -/
theorem common_mass_atomic_weights (outcomes : Distribution Value) (mass : Rat)
    (probability : IsProbability outcomes) (common : ∀ entry ∈ outcomes, entry.1 = mass) :
    scale (outcomes.length : Rat) (rankedMasses outcomes) = counting (List.range outcomes.length) := by
  have ranked := common_mass_ranks outcomes mass common
  have normalized : mass * (outcomes.length : Rat) = 1 := by
    have totals := congrArg total ranked
    simpa [rankedMasses_total, total_scale, total_counting, probability.2] using totals.symm
  rw [ranked, scale_scale, Rat.mul_comm, normalized, scale_one]

/-- A missing weight callback means weight one at every actual rank. The common-mass
premise is the local meaning of outcomeUniformMass, not a whole sampler contract. -/
theorem missing_callback_weights (fields : Fields Value)
    (origin : Origin fields.atomic fields.minimum fields.plan)
    (counts : count fields.plan = fields.outcomes.length)
    (probability : IsProbability fields.outcomes)
    (common : ∀ mass, fields.uniformMass = some mass → ∀ entry ∈ fields.outcomes, entry.1 = mass)
    (absent : hasWeight fields = false) :
    ∀ size, (sampling fields).weights size = counting (classRanks fields.plan size) := by
  cases marked : fields.atomic with
  | false =>
      have noStored : fields.storedWeights = none := by
        cases stored : fields.storedWeights with
        | none => rfl
        | some weights => simp [hasWeight, marked, stored] at absent
      intro size
      simp [sampling, marked, noStored, uniform]
  | true =>
      have shape := (origin_atomSize fields origin marked
        (by rw [counts]; exact probability_live _ probability)).2
      cases uniform : fields.uniformMass with
      | none => simp [hasWeight, marked, uniform] at absent
      | some mass =>
          have equal := common_mass_atomic_weights fields.outcomes mass probability (common mass uniform)
          intro size
          simp only [sampling, marked, ↓reduceIte, atomic, shape, counts]
          split <;> simp_all [counting]

/-- The omitted callback and the explicit relative-weight lookup agree on every valid rank. -/
theorem missing_callback_rank (fields : Fields Value)
    (origin : Origin fields.atomic fields.minimum fields.plan)
    (counts : count fields.plan = fields.outcomes.length)
    (probability : IsProbability fields.outcomes)
    (common : ∀ mass, fields.uniformMass = some mass → ∀ entry ∈ fields.outcomes, entry.1 = mass)
    (absent : hasWeight fields = false) (rank : Nat) (valid : rank < count fields.plan) :
    FiniteSizeSampling.weightAt (sampling fields) rank = some 1 := by
  have weights := missing_callback_weights fields origin counts probability common absent
  have samePlan : (sampling fields).plan = fields.plan := by
    unfold sampling
    split
    · rfl
    · split <;> rfl
  obtain ⟨part, converted⟩ := position_complete fields.plan rank valid
  have found := position_replay fields.plan rank part converted
  simp [FiniteSizeSampling.weightAt, samePlan, converted, weights, counting, found]

/-- atomicStatic resets every source size to one and clears stored size sampling. -/
def atomicFields (fields : Fields Value) : Fields Value :=
  { fields with
    plan := .select (count fields.plan)
    atomic := true
    minimum := (if count fields.plan = 0 then none else some 1)
    storedWeights := none }

/-- The atomic marker and minimum follow from the reset constructor itself. -/
theorem atomicFields_origin (fields : Fields Value) :
    Origin (atomicFields fields).atomic (atomicFields fields).minimum (atomicFields fields).plan :=
  Origin.atom _

/-- Resizing clears stored weights but preserves the source atomic marker. -/
def resizedFields (size : Nat) (fields : Fields Value) : Fields Value :=
  { fields with
    plan := fixedPlan size (count fields.plan)
    minimum := (if count fields.plan = 0 then none else some size)
    storedWeights := none }

/-- A non-atomic size-zero resize remains in the ordinary sampling branch. -/
theorem resized_ordinary (size : Nat) (fields : Fields Value) (ordinary : fields.atomic = false) :
    branch (resizedFields size fields) = .uniform ∧ hasWeight (resizedFields size fields) = false := by
  simp [branch, hasWeight, resizedFields, ordinary]

/-- A positive resize preserves the atomic constructor invariant. -/
theorem resized_origin (size : Nat) (fields : Fields Value)
    (origin : Origin fields.atomic fields.minimum fields.plan)
    (positive : fields.atomic = true → 0 < size) :
    Origin (resizedFields size fields).atomic (resizedFields size fields).minimum (resizedFields size fields).plan :=
  Origin.resize size origin positive

/-- boundedStatic always clears the atomic marker. It preserves recursive class
weights exactly when recursiveWeighted is set. -/
def boundedFields (plan : Plan) (outcomes : Distribution Value) (minimum : Option Nat)
    (weighted : Bool) (weights : Nat → Distribution Nat) : Fields Value :=
  ⟨plan, outcomes, false, minimum,
    if weighted then none else some (outcomes.length : Rat)⁻¹,
    if weighted then some weights else none⟩

/-- The bound wrapper cannot accidentally select the atomic sampler branch. -/
theorem bounded_dispatch (plan : Plan) (outcomes : Distribution Value) (minimum : Option Nat)
    (weighted : Bool) (weights : Nat → Distribution Nat) :
    branch (boundedFields plan outcomes minimum weighted weights) =
      (if weighted then .stored else .uniform) ∧
    hasWeight (boundedFields plan outcomes minimum weighted weights) = weighted ∧
    Origin (boundedFields plan outcomes minimum weighted weights).atomic
      (boundedFields plan outcomes minimum weighted weights).minimum
      (boundedFields plan outcomes minimum weighted weights).plan := by
  refine ⟨?_, ?_, Origin.ordinary _ _⟩ <;>
    cases weighted <;> rfl

/-- Apply the actual finite number of pay constructors used by retainAtomic. -/
def paySteps : Nat → Record → Record
  | 0, record => record
  | steps + 1, record => pay (paySteps steps record)

/-- Repeated pay shifts the complete fixed-size atomic record and retains all weights. -/
theorem paySteps_atomic (steps : Nat) (outcomes : Distribution Value) :
    count (paySteps steps (atomic 1 outcomes)).plan = outcomes.length ∧
    (∀ size, classRanks (paySteps steps (atomic 1 outcomes)).plan size =
      classRanks (atomic (steps + 1) outcomes).plan size) ∧
    (∀ size, (paySteps steps (atomic 1 outcomes)).weights size =
      (atomic (steps + 1) outcomes).weights size) := by
  induction steps with
  | zero => exact ⟨fixedPlan_count _ _, fun _ => rfl, fun _ => rfl⟩
  | succ steps ih =>
      refine ⟨ih.1, ?_, ?_⟩
      · intro size
        cases size with
        | zero => simp [paySteps, pay, classRanks, atomic, fixedPlan_classes]
        | succ size =>
            simpa [paySteps, pay, classRanks, atomic, fixedPlan_classes] using ih.2.1 size
      · intro size
        cases size with
        | zero => simp [paySteps, pay, atomic]
        | succ size =>
            simpa [paySteps, pay, atomic] using ih.2.2 size

/-- The source size-minus-one operation has exactly the selected size when that size is positive. -/
theorem retainAtomic_exact (size : Nat) (positive : 0 < size) (outcomes : Distribution Value) :
    count (paySteps (size - 1) (atomic 1 outcomes)).plan = outcomes.length ∧
    (∀ found, classRanks (paySteps (size - 1) (atomic 1 outcomes)).plan found =
      classRanks (atomic size outcomes).plan found) ∧
    (∀ found, (paySteps (size - 1) (atomic 1 outcomes)).weights found =
      (atomic size outcomes).weights found) := by
  simpa [Nat.sub_add_cancel (show 1 ≤ size by omega)] using paySteps_atomic (size - 1) outcomes

/-- Atomic priority preserves a nonuniform global law even if a uniform class sampler is stored. -/
private def priorityExample : Fields Unit :=
  ⟨.select 2, [(9 / 10, ()), (1 / 10, ())], true, some 1, none,
    some (fun size => if size = 1 then [(1, 0), (1, 1)] else [])⟩

example : FiniteSizeSampling.sample (sampling priorityExample) 1 = [(9 / 10, 0), (1 / 10, 1)] := by cbv

example : FiniteSizeSampling.sample (sampling { priorityExample with atomic := false }) 1 =
    [(1 / 2, 0), (1 / 2, 1)] := by cbv

/-- Unrestricted internal resize can construct an atomic size-zero record. The provenance
condition is necessary; this example does not claim that a public compiler reaches it. -/
example : classRanks (fixedPlan 0 1) 0 = [0] := by cbv

end MicroCFTA.StaticSamplingDispatch
