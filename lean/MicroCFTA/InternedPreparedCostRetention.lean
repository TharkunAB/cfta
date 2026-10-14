import MicroCFTA.InternedStoredCostRetention

/-!
# Retention bounds for actual prepared replacement inputs

Source availability supplies exact canonical slot lookup. Closed captures
keep their original shape. Open replacements supply positive occurrence
costs. In particular, replacing an outer reference with its open Mu keeps
every external original body occurrence at no greater cost.
-/
namespace MicroCFTA.InternedPreparedCostRetention
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedStoredSubstitution InternedStoredCostInputs InternedStoredCostRetention
open InternedFreeOccurrenceRank
open InternedBinderProtocol (Reference)

/-- Actual available records supply supported cost lists at every optional lexical slot. -/
theorem supported_inputs (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (available : ∀ value ∈ values, Available state value) :
    InternedOccurrenceCostSupport.Inputs (values.map InternedRecordDepthShape.shape) (values.map costs) := by
  intro index name count member
  cases found : values[index]? with
  | none => simp [List.getElem?_map, found] at member
  | some value =>
      have source := available value (List.mem_of_getElem? found)
      simp only [List.getElem?_map, found, Option.map_some, Option.getD_some] at member ⊢
      exact (InternedRecordDepthShape.shape_free value state coherent source name).mpr
        ((costs_free value state coherent source name).mp ⟨count, member⟩)

/-- Exact source preparation supplies all input premises for the structural retention theorem. -/
theorem prepared_inputs (body : Value Symbol Guard) (environment : Environment Symbol Guard)
    (state : State Symbol Guard) (normal : InternedStoredMuOrigins.Normal state)
    (available : Available state body) (replacements : Replacements state environment)
    (opened : ∀ name value, environment name = some value → value.free ≠ []) :
    Inputs (leaves body) []
      (((leaves body).map (input environment)).map InternedRecordDepthShape.shape)
      (((leaves body).map (input environment)).map costs)
      (fun name => costs ((environment name).getD (.reference name))) := by
  have originals := leaves_available body state available
  have inputs := inputs_available body environment state available replacements
  refine ⟨InternedRecordDepthShape.input_coherent _, supported_inputs _ state normal.facts.coherent inputs, ?_, ?_, ?_⟩
  · intro value member closed
    simp only [List.length_nil, Nat.zero_add, List.getElem?_map,
      InternedStoredSubstitutionScope.slot_lookup _ value state normal.facts.coherent originals member,
      Option.map_some, Option.getD_some, InternedStoredSubstitutionScope.input_closed value environment closed]
    exact (InternedRecordDepthShape.observed value state normal (originals value member)).empty.symm
  · intro name member
    simp only [encode, Value.free, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.findIdx?_nil,
      List.length_nil, Nat.zero_add, InternedOccurrenceCostSemantics.evaluate, List.getElem?_map,
      InternedStoredSubstitutionScope.slot_lookup _ (.reference name) state normal.facts.coherent originals member,
      Option.map_some, Option.getD_some, input]
  · intro name
    cases found : environment name with
    | none => simp [costs]
    | some value =>
        have source := replacements name value found
        cases freeFound : value.free with
        | nil => exact False.elim (opened name value found freeFound)
        | cons first rest =>
            obtain ⟨count, member⟩ := (costs_free value state normal.facts.coherent source first).mpr (by simp [freeFound])
            intro empty
            simp only [Option.getD_some] at empty
            simp [empty] at member

/-- Actual prepared execution retains every supplied occurrence with its original Mu cost bound. -/
theorem prepared_retains (body : Value Symbol Guard) (environment : Environment Symbol Guard)
    (state : State Symbol Guard) (normal : InternedStoredMuOrigins.Normal state)
    (available : Available state body) (replacements : Replacements state environment)
    (opened : ∀ name value, environment name = some value → value.free ≠ []) :
    Retains (costs body) (InternedFreshOrdinaryStoredSubstitution.preparedCosts body environment)
      (fun name => costs ((environment name).getD (.reference name))) :=
  (encode_retains (leaves body) [] body state normal available (fun _ member => member) _ _ _
    (prepared_inputs body environment state normal available replacements opened)).1

/-- Substitution of an open outer value retains each other original body occurrence at no greater cost. -/
theorem unfold_retains (body outer : Value Symbol Guard) (own : Reference) (state : State Symbol Guard)
    (normal : InternedStoredMuOrigins.Normal state) (available : Available state body)
    (outerAvailable : Available state outer) (opened : outer.free ≠ [])
    (name : Reference) (count : Nat) (different : name ≠ own) (member : (name, count) ∈ costs body) :
    ∃ after, after ≤ count ∧ (name, after) ∈ InternedFreshOrdinaryStoredSubstitution.preparedCosts body
      (fun reference => if reference = own then some outer else none) := by
  let environment : Environment Symbol Guard := fun reference => if reference = own then some outer else none
  have replacements : Replacements state environment := by
    intro reference value found
    dsimp only [environment] at found
    split at found
    · cases found; exact outerAvailable
    · contradiction
  have openReplacements : ∀ reference value, environment reference = some value → value.free ≠ [] := by
    intro reference value found
    dsimp only [environment] at found
    split at found
    · cases found; exact opened
    · contradiction
  have supplied : (name, 0) ∈ costs ((environment name).getD (.reference name)) := by
    simp [environment, different, costs]
  simpa only [Nat.add_zero] using
    prepared_retains body environment state normal available replacements openReplacements name count member name 0 supplied

end MicroCFTA.InternedPreparedCostRetention
