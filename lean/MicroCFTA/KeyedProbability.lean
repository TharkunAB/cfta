import MicroCFTA.KeyedSource

/-!
# Independent grouped recursive probabilities

The mass recurrence adds same-key alternatives and convolves product sizes.
The probability recurrence chooses each alternative by that retained mass,
then uses its own conditional distribution. Structural member counts remain
separate and provide the rank offsets and bounded-size probabilities.
-/

namespace MicroCFTA.KeyedProbability
open Probability SamplerReplay GroupedRecord KeyedSource

/-- The source sum of group masses equals an ordinary rational list sum. -/
theorem massSum_eq_sum (groups : List (Group α)) : massSum groups = (groups.map Group.mass).sum := by
  induction groups with
  | nil => rfl
  | cons first rest ih => simp [massSum, ih]

/-- Compute a body's unnormalized class mass independently of its compiled record. -/
def mass : Recipe Key Root α → (Key → Nat → Rat) → Nat → Rat
  | .finite source, _, size => ((FiniteSource.classMembers source size).length : Rat)
  | .retained weight _ source, _, size => if 0 < (FiniteSource.classMembers source size).length then weight size else 0
  | .occurrence key, environment, size => environment key size
  | .map _ inner, environment, size => mass inner environment size
  | .pay inner, environment, size => match size with | 0 => 0 | next + 1 => mass inner environment next
  | .choice left right, environment, size => mass left environment size + mass right environment size
  | .ap functions arguments, environment, size =>
      ((List.range (size + 1)).map fun split => mass functions environment split * mass arguments environment (size - split)).sum

/-- The actual stored mass field implements the independent sum and convolution recurrence. -/
theorem record_mass (recipe : Recipe Key Root α) (environment : Key → Classes Root) (size : Nat) :
    (record recipe environment size).mass = mass recipe (fun key size => (environment key size).mass) size := by
  induction recipe generalizing size with
  | finite source => simp [record, mass, finiteClass, counted, Decoder.count_correct, FiniteSource.class_members]
  | retained weight positive source =>
      simp [record, mass, retained, Decoder.count_correct, FiniteSource.class_members]
  | occurrence key => rfl
  | map transform inner ih => exact ih size
  | pay inner ih => cases size <;> simp [record, mass, GroupedRecord.pay, empty, ih]
  | choice left right ihl ihr => simp [record, mass, merge, massSum, ihl, ihr, Rat.add_zero]
  | ap functions arguments ihf iha =>
      simp [record, mass, productClasses, merge, massSum_eq_sum, List.map_map, Function.comp_def, GroupedRecord.apply, ihf, iha]

/-- Independent conditional probabilities retain source weights and choose grouped alternatives by mass. -/
def probabilities : Recipe Key Root α → (Key → Nat → List Root) → (Key → Nat → Rat) →
    (Key → Nat → Distribution Root) → Nat → Distribution α
  | .finite source, _, _, _, size | .retained _ _ source, _, _, _, size => FiniteSource.classDistribution source size
  | .occurrence key, _, _, environment, size => environment key size
  | .map transform inner, members, masses, environment, size => Probability.map transform (probabilities inner members masses environment size)
  | .pay inner, members, masses, environment, size => match size with | 0 => [] | next + 1 => probabilities inner members masses environment next
  | .choice left right, members, masses, environment, size => weightedChoice
      [((values left members size).length, mass left masses size, probabilities left members masses environment size),
       ((values right members size).length, mass right masses size, probabilities right members masses environment size)]
  | .ap functions arguments, members, masses, environment, size => weightedChoice ((List.range (size + 1)).map fun split =>
      ((values functions members split).length * (values arguments members (size - split)).length,
        mass functions masses split * mass arguments masses (size - split),
        Probability.map (fun pair => pair.1 pair.2)
          (product (probabilities functions members masses environment split) (probabilities arguments members masses environment (size - split)))))

/-- Each body sampler equals the separate probability formula and reads the proved mass and count fields. -/
theorem record_probability (recipe : Recipe Key Root α) (environment : Key → Classes Root) (size : Nat) :
    (record recipe environment size).members.sampling.values = probabilities recipe
      (fun key size => Decoder.values (environment key size).members.plan)
      (fun key size => (environment key size).mass)
      (fun key size => (environment key size).members.sampling.values) size := by
  induction recipe generalizing size with
  | finite source => exact FiniteSource.class_distribution source size
  | retained weight positive source => exact FiniteSource.class_distribution source size
  | occurrence key => rfl
  | map transform inner ih => simp [record, probabilities, GroupedRecord.map, mapRecord, Sampler.mapSampler, ih]
  | pay inner ih =>
      cases size <;> simp [record, probabilities, GroupedRecord.pay, empty, FiniteSource.empty, SamplerReplay.source, normalize, scale, ih]
  | choice left right ihl ihr =>
      simp [record, probabilities, merge_probability, Decoder.count_correct, record_values, record_mass, ihl, ihr]
  | ap functions arguments ihf iha =>
      simp [record, probabilities, productClasses_probability, Decoder.count_correct, record_values, record_mass, ihf, iha]

/-- The key mass knot is an independent recurrence over strictly smaller sizes. -/
def classMass (program : Key → Recipe Key Root Root) (size : Nat) (key : Key) : Rat :=
  mass (program key) (fun childKey childSize => if _smaller : childSize < size then classMass program childSize childKey else 0) size
termination_by size

/-- The sampler knot follows the independent mass recurrence and the independent ordered member classes. -/
def classProbability (program : Key → Recipe Key Root Root) (size : Nat) (key : Key) : Distribution Root :=
  probabilities (program key)
    (fun childKey childSize => if childSize < size then languageClass program childSize childKey else [])
    (fun childKey childSize => if childSize < size then classMass program childSize childKey else 0)
    (fun childKey childSize => if _smaller : childSize < size then classProbability program childSize childKey else []) size
termination_by size

/-- Every compiled key's stored mass is the independently specified recursive mass. -/
theorem family_mass (program : Key → Recipe Key Root Root) (size : Nat) (key : Key) :
    (family program size key).mass = classMass program size key := by
  induction size using Nat.strongRecOn generalizing key with
  | ind size ih =>
      rw [family, record_mass, classMass]
      congr 1
      funext childKey childSize
      by_cases smaller : childSize < size
      · simp only [dite_eq_left smaller, ih childSize smaller]
      · simp [smaller, empty]

/-- Every compiled key's conditional sampler equals the declared grouped recursive probability recurrence. -/
theorem family_probability (program : Key → Recipe Key Root Root) (size : Nat) (key : Key) :
    (family program size key).members.sampling.values = classProbability program size key := by
  induction size using Nat.strongRecOn generalizing key with
  | ind size ih =>
      rw [family, record_probability, classProbability]
      congr 1
      · funext childKey childSize
        by_cases smaller : childSize < size
        · simp only [dite_eq_left smaller, ite_eq_left smaller, family_values]
        · simp [smaller, empty, FiniteSource.empty, SamplerReplay.source, Decoder.values]
      · funext childKey childSize
        by_cases smaller : childSize < size
        · simp only [dite_eq_left smaller, ite_eq_left smaller, family_mass]
        · simp [smaller, empty]
      · funext childKey childSize
        by_cases smaller : childSize < size
        · simp only [dite_eq_left smaller, ih childSize smaller]
        · simp [smaller, empty, FiniteSource.empty, SamplerReplay.source, normalize, scale]

/-- Bounding one key uses exact member counts between sizes and retained conditional probabilities within sizes. -/
theorem bounded_probability (program : Key → Recipe Key Root Root) (key : Key) (bound : Nat) :
    (GroupedRecord.bounded (fun size => family program size key) bound).sampling.values =
      weightedChoice ((List.range (bound + 1)).map fun size =>
        ((languageClass program size key).length, ((languageClass program size key).length : Rat), classProbability program size key)) := by
  simp [GroupedRecord.bounded, boundedRecord, many_values, List.map_map, Function.comp_def, family_count, family_probability]

end MicroCFTA.KeyedProbability
