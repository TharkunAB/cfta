import MicroCFTA.RecursiveJoinRuntime
import MicroCFTA.RecursiveRuntimeDispatch

/-!
# Constructor-derived runtime metadata across recursive rebuilds

A template retains its source leaves and recursive keys. The same checked
body is rebuilt with probe placeholders or term placeholders. Constructor
proofs derive runtime term availability and weight provenance in both phases.
-/
namespace MicroCFTA.RecursiveRuntimeOrigins
open RecursiveJoinRuntime

/-- A primitive input is a completed source record or one recursive key. -/
abbrev Input (Key : Type) := Sum Metadata Key

/-- Recursive rebuilds change occurrence fields but preserve source fields. -/
def resolve (roots : Key → Metadata) : Input Key → Metadata
  | .inl fields => fields
  | .inr key => roots key

/-- The promoted weight flag, mass flag, and term presence retain their exact primitive origins. -/
def Provenance (fields : Metadata) (inputs : List Metadata) : Prop :=
  fields.terms = inputs.all Metadata.terms ∧
  fields.massWeighted = inputs.any Metadata.massWeighted ∧
  (fields.weighted || fields.massWeighted) = inputs.any (fun input => input.weighted || input.massWeighted)

/-- A primitive source has exactly its own fields, including an unpromoted mass flag. -/
theorem source_provenance (fields : Metadata) : Provenance fields [fields] := by
  simp [Provenance]

/-- Promoting key mass in a choice is exactly the disjunction of both input flags. -/
theorem choice_weighted (inputs : List Metadata) :
    (choiceMetadata inputs).weighted = inputs.any (fun input => input.weighted || input.massWeighted) := by
  apply Bool.eq_iff_iff.mpr
  simp only [choiceMetadata, Bool.or_eq_true, List.any_eq_true]
  constructor
  · rintro (⟨input, present, mass⟩ | ⟨input, present, weighted⟩)
    · exact ⟨input, present, Or.inr mass⟩
    · exact ⟨input, present, Or.inl weighted⟩
  · rintro ⟨input, present, weighted | mass⟩
    · exact Or.inr ⟨input, present, weighted⟩
    · exact Or.inl ⟨input, present, mass⟩

/-- Choice promotion is idempotent. -/
theorem choice_promoted (inputs : List Metadata) :
    ((choiceMetadata inputs).weighted || (choiceMetadata inputs).massWeighted) = (choiceMetadata inputs).weighted := by
  simp [choiceMetadata, Bool.or_comm, Bool.or_left_comm]

/-- Choice metadata exposes exactly its complete list of primitive records. -/
theorem choice_provenance (inputs : List Metadata) : Provenance (choiceMetadata inputs) inputs := by
  exact ⟨rfl, rfl, (choice_promoted inputs).trans (choice_weighted inputs)⟩

/-- Local child provenance composes through the complete source choice. -/
theorem flatten_provenance (names : List Name) (fields : Name → Metadata) (inputs : Name → List Metadata)
    (same : ∀ name ∈ names, Provenance (fields name) (inputs name)) :
    Provenance (choiceMetadata (names.map fields)) (names.flatMap inputs) := by
  have terms : (names.map fields).all Metadata.terms = (names.flatMap inputs).all Metadata.terms := by
    induction names with
    | nil => rfl
    | cons name rest ih =>
        simp only [List.map_cons, List.all_cons, List.flatMap_cons, List.all_append]
        rw [(same name (by simp)).1, ih (fun other member => same other (by simp [member]))]
  have mass : (names.map fields).any Metadata.massWeighted = (names.flatMap inputs).any Metadata.massWeighted := by
    clear terms
    induction names with
    | nil => rfl
    | cons name rest ih =>
        simp only [List.map_cons, List.any_cons, List.flatMap_cons, List.any_append]
        rw [(same name (by simp)).2.1, ih (fun other member => same other (by simp [member]))]
  have weighted : (names.map fields).any (fun input => input.weighted || input.massWeighted) =
      (names.flatMap inputs).any (fun input => input.weighted || input.massWeighted) := by
    clear terms mass
    induction names with
    | nil => rfl
    | cons name rest ih =>
        simp only [List.map_cons, List.any_cons, List.flatMap_cons, List.any_append]
        rw [(same name (by simp)).2.2, ih (fun other member => same other (by simp [member]))]
  exact ⟨terms, mass, ((choice_provenance _).2.2).trans weighted⟩

/-- Join uses the same complete input flags as a promoted choice, despite its
different value, term, and probability operations. -/
theorem join_choice (operation : Metadata) (arguments : List Metadata) :
    joinMetadata operation arguments = choiceMetadata (operation :: arguments) := by
  simp [joinMetadata, choiceMetadata, Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]

/-- A typed template keeps a local metadata compiler and its exact source-input inventory. -/
structure Template (Key Root Symbol Value : Type) where
  checked : RecursiveJoinBodyFields.CheckedBody Key Root Symbol Value
  metadata : (Key → Metadata) → Metadata
  inputs : List (Input Key)
  provenance : ∀ roots, Provenance (metadata roots) (inputs.map (resolve roots))

/-- A source record supplies its actual runtime fields once. -/
def source (body : Body Key Root Symbol Value) : Template Key Root Symbol Value where
  checked := body.checked
  metadata := fun _ => body.metadata
  inputs := [.inl body.metadata]
  provenance := fun _ => source_provenance body.metadata

/-- Static leaves always supply terms and derive their original weight marker
from the finite sampling fields. -/
def staticSource (checked : RecursiveJoinBodyFields.CheckedBody Key Root Symbol Value)
    (fields : StaticSamplingDispatch.Fields Value) : Template Key Root Symbol Value :=
  source ⟨checked, fromStatic fields⟩

/-- Finite keyed leaves preserve the separate retained-mass flag. -/
def bucketSource (checked : RecursiveJoinBodyFields.CheckedBody Key Root Symbol Value)
    (fields : StaticSamplingDispatch.Fields Value) (storedMasses : Bool)
    (totalCount bucketCount : Nat) (bucketMass : Rat) : Template Key Root Symbol Value :=
  source ⟨checked, fromBucket fields storedMasses totalCount bucketCount bucketMass⟩

/-- Occurrences read the current rebuild's runtime fields for their own key. -/
def occurrence [DecidableEq Symbol] (callbacks : KeyedNaryFields.LeafCallbacks Symbol) (key : Key) :
    Template Key Root Symbol Root where
  checked := RecursiveJoinBodyFields.ofNary callbacks (.occurrence key) (by simp [KeyedNaryFields.LeavesExact])
  metadata := fun roots => roots key
  inputs := [.inr key]
  provenance := fun roots => source_provenance (roots key)

/-- User-value maps retain the complete source-field inventory. -/
def map (transform : Value → Result) (inner : Template Key Root Symbol Value) : Template Key Root Symbol Result where
  checked := RecursiveJoinBodyFields.map transform inner.checked
  metadata := inner.metadata
  inputs := inner.inputs
  provenance := inner.provenance

/-- Pay changes the size compiler but leaves runtime field origins unchanged. -/
def pay [DecidableEq Symbol] (inner : Template Key Root Symbol Value) : Template Key Root Symbol Value where
  checked := RecursiveJoinBodyFields.pay inner.checked
  metadata := inner.metadata
  inputs := inner.inputs
  provenance := inner.provenance

/-- A label does not alter weight flags or term availability. -/
def label [DecidableEq Symbol] (symbol : Symbol) (inner : Template Key Root Symbol Value) : Template Key Root Symbol Value where
  checked := RecursiveJoinBodyFields.label symbol inner.checked
  metadata := inner.metadata
  inputs := inner.inputs
  provenance := inner.provenance

/-- Source flat choices concatenate primitive inputs in their original branch order. -/
def nary (count : Nat) (branches : Fin count → Template Key Root Symbol Value) : Template Key Root Symbol Value where
  checked := RecursiveJoinBodyFields.nary count (fun index => (branches index).checked)
  metadata := fun roots => choiceMetadata (List.ofFn fun index => (branches index).metadata roots)
  inputs := (List.ofFn id).flatMap (fun index => (branches index).inputs)
  provenance := by
    intro roots
    simpa only [List.map_ofFn, Function.comp_def, id_eq, List.map_flatMap] using
      flatten_provenance (List.ofFn id) (fun index => (branches index).metadata roots)
        (fun index => (branches index).inputs.map (resolve roots)) (fun index _ => (branches index).provenance roots)

/-- Each typed argument retains its independent metadata compiler. -/
inductive Chain (Key Root Symbol : Type) : Type → Type → Type 1 where
  | nil : Chain Key Root Symbol Result Result
  | cons (argument : Template Key Root Symbol Argument) (rest : Chain Key Root Symbol Operand Result) :
      Chain Key Root Symbol (Argument → Operand) Result

/-- Lower the same typed arguments to the complete callback compiler. -/
def Chain.lower : Chain Key Root Symbol Operand Result → RecursiveJoinBodyFields.Chain Key Root Symbol Operand Result
  | .nil => .nil
  | .cons argument rest => .cons argument.checked rest.lower

/-- Every rebuild reads the same argument metadata compilers in order. -/
def Chain.fields (roots : Key → Metadata) : Chain Key Root Symbol Operand Result → List Metadata
  | .nil => []
  | .cons argument rest => argument.metadata roots :: rest.fields roots

/-- Concatenate argument input inventories without identifying repeated occurrences. -/
def Chain.inputs : Chain Key Root Symbol Operand Result → List (Input Key)
  | .nil => []
  | .cons argument rest => argument.inputs ++ rest.inputs

/-- Chain provenance follows each argument independently under the current rebuild. -/
theorem Chain.provenance (arguments : Chain Key Root Symbol Operand Result) (roots : Key → Metadata) :
    Provenance (choiceMetadata (arguments.fields roots)) (arguments.inputs.map (resolve roots)) := by
  induction arguments with
  | nil => exact choice_provenance []
  | cons argument rest ih =>
      rcases argument.provenance roots with ⟨terms, mass, weighted⟩
      rcases ih with ⟨tailTerms, tailMass, tailWeighted⟩
      rw [choice_promoted, choice_weighted] at tailWeighted
      refine ⟨?_, ?_, ?_⟩
      · simpa only [Provenance, Chain.fields, Chain.inputs, List.map_append, choiceMetadata,
          List.all_cons, List.all_append, terms] using congrArg (fun value =>
            (argument.inputs.map (resolve roots)).all Metadata.terms && value) tailTerms
      · simpa only [Chain.fields, Chain.inputs, List.map_append, choiceMetadata,
          List.any_cons, List.any_append, mass] using congrArg (fun value =>
            (argument.inputs.map (resolve roots)).any Metadata.massWeighted || value) tailMass
      · rw [choice_promoted, choice_weighted]
        simp only [Chain.fields, Chain.inputs, List.map_append, List.any_cons, List.any_append, weighted, tailWeighted]

/-- Join metadata is derived for all recursive environments, not just one probe snapshot. -/
def join (component : Nat) (operation : Template Key Root Symbol Operand)
    (arguments : Chain Key Root Symbol Operand Result) : Template Key Root Symbol Result where
  checked := RecursiveJoinBodyFields.join component operation.checked arguments.lower
  metadata := fun roots => joinMetadata (operation.metadata roots) (arguments.fields roots)
  inputs := operation.inputs ++ arguments.inputs
  provenance := by
    intro roots
    rcases operation.provenance roots with ⟨terms, mass, weighted⟩
    rcases arguments.provenance roots with ⟨tailTerms, tailMass, tailWeighted⟩
    rw [choice_promoted, choice_weighted] at tailWeighted
    rw [join_choice]
    refine ⟨?_, ?_, ?_⟩
    · simpa only [choiceMetadata, List.all_cons, List.map_append, List.all_append, terms] using
        congrArg (fun value => (operation.inputs.map (resolve roots)).all Metadata.terms && value) tailTerms
    · simpa only [choiceMetadata, List.any_cons, List.map_append, List.any_append, mass] using
        congrArg (fun value => (operation.inputs.map (resolve roots)).any Metadata.massWeighted || value) tailMass
    · rw [choice_promoted, choice_weighted]
      simp only [List.any_cons, List.map_append, List.any_append, weighted, tailWeighted]

/-- Build the runtime view for one phase without changing its typed compiler. -/
def instantiate (body : Template Key Root Symbol Value) (roots : Key → Metadata) : Body Key Root Symbol Value :=
  ⟨body.checked, body.metadata roots⟩

/-- Terms are available exactly when every primitive source or occurrence supplies them. -/
theorem terms_exact (body : Template Key Root Symbol Value) (roots : Key → Metadata) :
    (body.metadata roots).terms = true ↔ ∀ input ∈ body.inputs, (resolve roots input).terms = true := by
  rw [(body.provenance roots).1]
  simp

/-- The term rebuild supplies every recursive occurrence. Only absent source
term fields can make the complete body's term field absent. -/
theorem term_rebuild_exact (body : Template Key Root Symbol Value) :
    (body.metadata (fun _ => termPlaceholder)).terms = true ↔
      ∀ fields, Sum.inl fields ∈ body.inputs → fields.terms = true := by
  rw [terms_exact]
  constructor
  · intro all fields present
    exact all (.inl fields) present
  · intro sources input present
    cases input with
    | inl fields => exact sources fields present
    | inr key => rfl

/-- Probe and term rebuilds have identical original weight flags. -/
theorem rebuild_weight_origins (body : Template Key Root Symbol Value) :
    (body.metadata (fun _ => placeholder)).massWeighted = (body.metadata (fun _ => termPlaceholder)).massWeighted ∧
    ((body.metadata (fun _ => placeholder)).weighted || (body.metadata (fun _ => placeholder)).massWeighted) =
      ((body.metadata (fun _ => termPlaceholder)).weighted || (body.metadata (fun _ => termPlaceholder)).massWeighted) := by
  constructor
  · rw [(body.provenance _).2.1, (body.provenance _).2.1]
    simp only [List.any_map]
    congr 1
    funext input
    cases input <;> rfl
  · rw [(body.provenance _).2.2, (body.provenance _).2.2]
    simp only [List.any_map]
    congr 1
    funext input
    cases input <;> rfl

/-- Read all successful rebuilt body fields before the source removes empty keys. -/
def bodyMetadata (keys : List Key) (program : Key → Template Key Root Symbol Root) : List Metadata :=
  keys.map (fun key => (program key).metadata (fun _ => placeholder))

/-- The separate term rebuild supplies every recursive term placeholder. -/
def termsAt (program : Key → Template Key Root Symbol Root) (key : Key) : Bool :=
  ((program key).metadata (fun _ => termPlaceholder)).terms

/-- The original family flag is derived from primitive weighted or mass-weighted
source records. Recursive placeholder markers do not create a weight flag. -/
theorem family_weighted_origins (keys : List Key) (program : Key → Template Key Root Symbol Root)
    (terms : Bool) :
    (familyMetadata (bodyMetadata keys program) terms).weighted = true ↔
      ∃ key ∈ keys, ∃ fields, Sum.inl fields ∈ (program key).inputs ∧
        (fields.weighted = true ∨ fields.massWeighted = true) := by
  change (choiceMetadata (bodyMetadata keys program)).weighted = true ↔ _
  rw [choice_weighted]
  simp only [bodyMetadata, List.any_map, Function.comp_def, List.any_eq_true]
  constructor
  · rintro ⟨key, member, weighted⟩
    rw [(program key).provenance _ |>.2.2] at weighted
    obtain ⟨input, present, positive⟩ := List.any_eq_true.mp weighted
    obtain ⟨origin, original, rfl⟩ := List.mem_map.mp present
    cases origin with
    | inl fields => exact ⟨key, member, fields, original, Bool.or_eq_true_iff.mp positive⟩
    | inr key => simp [resolve, placeholder] at positive
  · rintro ⟨key, member, fields, present, weighted⟩
    refine ⟨key, member, ?_⟩
    rw [(program key).provenance _ |>.2.2]
    exact List.any_eq_true.mpr ⟨fields, List.mem_map.mpr ⟨.inl fields, present, rfl⟩,
      Bool.or_eq_true_iff.mpr weighted⟩

/-- The family's retained-mass marker has the same primitive-source provenance. -/
theorem family_mass_origins (keys : List Key) (program : Key → Template Key Root Symbol Root)
    (terms : Bool) :
    (familyMetadata (bodyMetadata keys program) terms).massWeighted = true ↔
      ∃ key ∈ keys, ∃ fields, Sum.inl fields ∈ (program key).inputs ∧ fields.massWeighted = true := by
  change (bodyMetadata keys program).any Metadata.massWeighted = true ↔ _
  simp only [bodyMetadata, List.any_map, Function.comp_def, List.any_eq_true]
  constructor
  · rintro ⟨key, member, weighted⟩
    rw [(program key).provenance _ |>.2.1] at weighted
    obtain ⟨input, present, positive⟩ := List.any_eq_true.mp weighted
    obtain ⟨origin, original, rfl⟩ := List.mem_map.mp present
    cases origin with
    | inl fields => exact ⟨key, member, fields, original, positive⟩
    | inr key => simp [resolve, placeholder] at positive
  · rintro ⟨key, member, fields, present, weighted⟩
    refine ⟨key, member, ?_⟩
    rw [(program key).provenance _ |>.2.1]
    exact List.any_eq_true.mpr ⟨fields, List.mem_map.mpr ⟨.inl fields, present, rfl⟩, weighted⟩

/-- Family term tracking is determined by the source fields of that key's
body. Missing probe placeholder terms do not suppress the term rebuild. -/
theorem family_terms_origins (program : Key → Template Key Root Symbol Root) (key : Key) :
    termsAt program key = true ↔ ∀ fields, Sum.inl fields ∈ (program key).inputs → fields.terms = true :=
  term_rebuild_exact (program key)

/-- The final per-key record combines family weight flags with its own derived term availability. -/
def memberMetadata (keys : List Key) (program : Key → Template Key Root Symbol Root) (key : Key) : Metadata :=
  familyMetadata (bodyMetadata keys program) (termsAt program key)

/-- The runtime term compiler is complete when every primitive source at the
key tracks terms. This condition is discharged by ordinary Static leaves. -/
theorem member_terms (keys : List Key) (program : Key → Template Key Root Symbol Root) (key : Key)
    (tracked : ∀ fields, Sum.inl fields ∈ (program key).inputs → fields.terms = true) :
    (memberMetadata keys program key).terms = true :=
  (family_terms_origins program key).mpr tracked

/-- Source Static leaves require no extra term-availability premise. -/
theorem static_terms (checked : RecursiveJoinBodyFields.CheckedBody Key Root Symbol Root)
    (fields : StaticSamplingDispatch.Fields Root) :
    ((staticSource checked fields).metadata (fun _ => termPlaceholder)).terms = true := rfl

/-- A source-derived weighted flag selects the complete bounded family sampler. -/
theorem family_sampler_from_origin (keys : List Key) (code : Key → Nat)
    (program : Key → Template Key Root Symbol Root) (key sourceKey : Key) (bound : Nat)
    (sourceKeyPresent : sourceKey ∈ keys) (fields : Metadata)
    (sourcePresent : Sum.inl fields ∈ (program sourceKey).inputs)
    (weighted : fields.weighted = true ∨ fields.massWeighted = true) :
    Probability.map (fun entry => (entry.1, entry.2.1))
      (GroupedRecord.bounded (fun size => KeyedSource.family
        (RecursiveJoinFamily.pairedProgram code (fun key => (program key).checked.body)) size key) bound).sampling.ranked =
      (boundedSampler (memberMetadata keys program key).weighted (fun size => KeyedSource.family
        (RecursiveJoinFamily.valueProgram (fun key => (program key).checked.body)) size key) bound).sampling.ranked :=
  weighted_family_sampler code _ key bound _
    ((family_weighted_origins keys program _).mpr ⟨sourceKey, sourceKeyPresent, fields, sourcePresent, weighted⟩)

/-- The derived member term flag connects the original template to complete
bounded decoding, without an independent per-key availability hypothesis. -/
theorem member_outcome_exact (keys : List Key) (code : Key → Nat)
    (program : Key → Template Key Root Symbol Root) (key : Key) (bound : Nat) (rank : Int)
    (term : KeyedNaryAlignment.EngineTerm Symbol)
    (tracked : ∀ fields, Sum.inl fields ∈ (program key).inputs → fields.terms = true) :
    RecursiveRuntimeDispatch.familyOutcome (Cause := Cause) code (fun key => (program key).checked) key
      (memberMetadata keys program key) bound rank = .ok term ↔
      0 ≤ rank ∧ RecursiveJoinQuery.boundedDecode code (fun key => (program key).checked) key bound rank.toNat = some term := by
  rw [RecursiveRuntimeDispatch.familyOutcome_exact, member_terms keys program key tracked]
  simp

end MicroCFTA.RecursiveRuntimeOrigins
