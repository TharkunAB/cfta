import MicroCFTA.RecursiveJoinBodyFields
import MicroCFTA.RecursiveJoinFamily
import MicroCFTA.StaticSamplingDispatch

/-!
# Runtime flags and optional term fields of recursive joins

These adapters keep source runtime fields beside the complete typed body.
Base fields come from a source record. Join and same-key merge derive their
flags and optional callback fields from those records. The Boolean flags
are not reconstructed from an erased value recipe.
-/
namespace MicroCFTA.RecursiveJoinRuntime
open Language RecursiveCallbackTermination

/-- The three runtime fields read by recursive joining and public queries. -/
structure Metadata where
  weighted : Bool
  massWeighted : Bool
  terms : Bool
  deriving DecidableEq, Repr

/-- A plain recursive placeholder has no weights and no term field. -/
def placeholder : Metadata := ⟨false, false, false⟩

/-- The term reconstruction phase changes only the placeholder's term field. -/
def termPlaceholder : Metadata := { placeholder with terms := true }

/-- Reading a finite Static computes its weighted flag from the actual sampling dispatch. -/
def fromStatic (fields : StaticSamplingDispatch.Fields Value) : Metadata :=
  ⟨StaticSamplingDispatch.hasWeight fields, false, true⟩

/-- Finite keyed buckets keep a separate flag for retained or non-count key mass. -/
def fromBucket (fields : StaticSamplingDispatch.Fields Value) (storedMasses : Bool)
    (totalCount bucketCount : Nat) (bucketMass : Rat) : Metadata :=
  { fromStatic fields with massWeighted := storedMasses ||
      (fields.atomic && decide ((totalCount : Rat) * bucketMass ≠ (bucketCount : Rat))) }

/-- An explicitly retained mass table keeps the mass flag even when its values happen to equal counts. -/
theorem retained_bucket_flag (fields : StaticSamplingDispatch.Fields Value)
    (totalCount bucketCount : Nat) (bucketMass : Rat) :
    (fromBucket fields true totalCount bucketCount bucketMass).massWeighted = true := by
  simp [fromBucket]

/-- Join promotes any retained key mass into the recursive sampling flag. -/
def joinMetadata (operation : Metadata) (arguments : List Metadata) : Metadata :=
  let massWeighted := operation.massWeighted || arguments.any Metadata.massWeighted
  ⟨operation.weighted || arguments.any Metadata.weighted || massWeighted,
    massWeighted, operation.terms && arguments.all Metadata.terms⟩

/-- A raw multi-group choice uses the source's two independent weight checks. -/
def choiceMetadata (alternatives : List Metadata) : Metadata :=
  let massWeighted := alternatives.any Metadata.massWeighted
  ⟨massWeighted || alternatives.any Metadata.weighted, massWeighted, alternatives.all Metadata.terms⟩

/-- Same-key merging keeps an existing singleton record unchanged. -/
def mergeMetadata : List Metadata → Option Metadata
  | [] => none
  | [only] => some only
  | first :: second :: rest => some (choiceMetadata (first :: second :: rest))

/-- A joined sampler is unweighted exactly when no input carries either flag. -/
theorem join_unweighted (operation : Metadata) (arguments : List Metadata) :
    (joinMetadata operation arguments).weighted = false ↔
      operation.weighted = false ∧ operation.massWeighted = false ∧
        ∀ argument ∈ arguments, argument.weighted = false ∧ argument.massWeighted = false := by
  simp [joinMetadata, List.any_eq_false, and_assoc, and_left_comm, forall_and]

/-- The exact source flag is true even when only retained mass differs from counts. -/
theorem join_mass_promoted (operation : Metadata) (arguments : List Metadata)
    (mass : (joinMetadata operation arguments).massWeighted = true) :
    (joinMetadata operation arguments).weighted = true := by
  simp only [joinMetadata] at mass ⊢
  simp [mass]

/-- The nullary value index is unchanged, but its runtime weighted flag can change. -/
theorem nullary_mass_promoted :
    joinMetadata ⟨false, true, true⟩ [] = ⟨true, true, true⟩ ∧
    mergeMetadata [⟨false, true, true⟩] = some ⟨false, true, true⟩ := by decide

/-- A runtime view retains the typed callback compiler and its source metadata. -/
structure Body (Key Root Symbol Value : Type) where
  checked : RecursiveJoinBodyFields.CheckedBody Key Root Symbol Value
  metadata : Metadata

/-- Attach the fields of one already constructed source record. -/
def source (checked : RecursiveJoinBodyFields.CheckedBody Key Root Symbol Value)
    (metadata : Metadata) : Body Key Root Symbol Value := ⟨checked, metadata⟩

/-- Value maps preserve every source runtime field. -/
def map (transform : Value → Result) (inner : Body Key Root Symbol Value) : Body Key Root Symbol Result :=
  ⟨RecursiveJoinBodyFields.map transform inner.checked, inner.metadata⟩

/-- Pay changes the size fields but keeps weights and optional terms. -/
def pay [DecidableEq Symbol] (inner : Body Key Root Symbol Value) : Body Key Root Symbol Value :=
  ⟨RecursiveJoinBodyFields.pay inner.checked, inner.metadata⟩

/-- Labels preserve weights and optional term availability. -/
def label [DecidableEq Symbol] (symbol : Symbol) (inner : Body Key Root Symbol Value) : Body Key Root Symbol Value :=
  ⟨RecursiveJoinBodyFields.label symbol inner.checked, inner.metadata⟩

/-- A flat mass-weighted choice checks every branch for term tracking. -/
def nary (count : Nat) (branches : Fin count → Body Key Root Symbol Value) : Body Key Root Symbol Value :=
  ⟨RecursiveJoinBodyFields.nary count (fun index => (branches index).checked),
    choiceMetadata (List.ofFn fun index => (branches index).metadata)⟩

/-- Runtime argument records retain the original heterogeneous chain order. -/
inductive Chain (Key Root Symbol : Type) : Type → Type → Type 1 where
  | nil : Chain Key Root Symbol Result Result
  | cons (argument : Body Key Root Symbol Argument) (rest : Chain Key Root Symbol Operand Result) :
      Chain Key Root Symbol (Argument → Operand) Result

/-- Erase only runtime fields before the established typed callback compiler. -/
def Chain.lower : Chain Key Root Symbol Operand Result → RecursiveJoinBodyFields.Chain Key Root Symbol Operand Result
  | .nil => .nil
  | .cons argument rest => .cons argument.checked rest.lower

/-- The source's `chainToList` reads argument fields from left to right. -/
def Chain.metadata : Chain Key Root Symbol Operand Result → List Metadata
  | .nil => []
  | .cons argument rest => argument.metadata :: rest.metadata

/-- The compiled join derives both weight flags and term tracking from its inputs. -/
def join (component : Nat) (operation : Body Key Root Symbol Operand)
    (arguments : Chain Key Root Symbol Operand Result) : Body Key Root Symbol Result :=
  ⟨RecursiveJoinBodyFields.join component operation.checked arguments.lower,
    joinMetadata operation.metadata arguments.metadata⟩

/-- An available runtime term field is the complete compiled field, not a filtered class. -/
def termField (body : Body Key Root Symbol Value) (roots : Key → Finite Symbol) : Option (Finite Symbol) :=
  if body.metadata.terms then some (body.checked.compile roots) else none

/-- The source's Maybe traversal rejects an argument with no term field. -/
def Chain.termFields (roots : Key → Finite Symbol) : Chain Key Root Symbol Operand Result → Option (List (Finite Symbol))
  | .nil => some []
  | .cons argument rest => do
      let field ← termField argument roots
      let fields ← rest.termFields roots
      pure (field :: fields)

/-- Optional traversal returns exactly the full ordered chain when every field exists. -/
theorem Chain.termFields_exact (arguments : Chain Key Root Symbol Operand Result) (roots : Key → Finite Symbol) :
    arguments.termFields roots =
      if arguments.metadata.all Metadata.terms then some (arguments.lower.fields roots) else none := by
  induction arguments with
  | nil => rfl
  | cons argument rest ih =>
      simp only [Chain.termFields, Chain.metadata, List.all_cons, Chain.lower,
        RecursiveJoinBodyFields.Chain.fields, termField, ih]
      cases argument.metadata.terms <;> cases rest.metadata.all Metadata.terms <;> rfl

/-- The source bind checks the operation before traversing argument term fields. -/
def joinedTermField (component : Nat) (operation : Body Key Root Symbol Operand)
    (arguments : Chain Key Root Symbol Operand Result) (roots : Key → Finite Symbol) : Option (Finite Symbol) := do
  let operationTerms ← termField operation roots
  let argumentTerms ← arguments.termFields roots
  pure (RecursiveJoinCallbacks.field component operationTerms argumentTerms)

/-- Exact source optional construction agrees with the complete typed join compiler. -/
theorem joinedTermField_exact (component : Nat) (operation : Body Key Root Symbol Operand)
    (arguments : Chain Key Root Symbol Operand Result) (roots : Key → Finite Symbol) :
    joinedTermField component operation arguments roots = termField (join component operation arguments) roots := by
  simp only [joinedTermField, Chain.termFields_exact, termField, join, joinMetadata,
    RecursiveJoinBodyFields.join]
  by_cases operationTerms : operation.metadata.terms = true <;>
    by_cases argumentTerms : arguments.metadata.all Metadata.terms = true <;>
      simp [operationTerms, argumentTerms]

/-- No missing operation or argument term field is silently dropped. -/
theorem joinedTermField_present (component : Nat) (operation : Body Key Root Symbol Operand)
    (arguments : Chain Key Root Symbol Operand Result) (roots : Key → Finite Symbol) :
    (joinedTermField component operation arguments roots).isSome = true ↔
      operation.metadata.terms = true ∧ ∀ argument ∈ arguments.metadata, argument.terms = true := by
  rw [joinedTermField_exact]
  simp [termField, join, joinMetadata, List.all_eq_true]

/-- Any present runtime field inherits the existing local count and decoder proof. -/
theorem termField_realizes (body : Body Key Root Symbol Value) (roots : Key → Finite Symbol)
    (environment : Key → GroupedRecord.Classes (KeyedNaryAlignment.EngineTerm Symbol))
    (rootRealized : ∀ key, RecursiveJoinRecordBridge.Realizes (environment key) (RecursiveJoinFields.termIndex (roots key)))
    (field : Finite Symbol) (present : termField body roots = some field) :
    RecursiveJoinRecordBridge.Realizes (KeyedSource.record body.checked.body.term environment)
      (RecursiveJoinFields.termIndex field) := by
  unfold termField at present
  split at present
  · cases present
    exact body.checked.realizes environment roots rootRealized
  · cases present

/-- Family flags inspect all built bodies before unproductive keys are removed. -/
def familyMetadata (bodies : List Metadata) (termAvailable : Bool) : Metadata :=
  { choiceMetadata bodies with terms := termAvailable }

/-- Every retained family member receives the same two promoted weight flags. -/
theorem family_flags (bodies : List Metadata) (leftTerms rightTerms : Bool) :
    (familyMetadata bodies leftTerms).weighted = (familyMetadata bodies rightTerms).weighted ∧
    (familyMetadata bodies leftTerms).massWeighted = (familyMetadata bodies rightTerms).massWeighted := ⟨rfl, rfl⟩

/-- A mass-weighted body marks the whole family, even when that body's output key is dropped. -/
theorem family_mass_promoted (bodies : List Metadata) (body : Metadata) (member : body ∈ bodies)
    (weighted : body.massWeighted = true) (terms : Bool) : (familyMetadata bodies terms).weighted = true := by
  have mass : bodies.any Metadata.massWeighted = true := List.any_eq_true.mpr ⟨body, member, weighted⟩
  simp [familyMetadata, choiceMetadata, mass]

/-- The weighted runtime branch uses the already proved recursive class sampler. -/
def boundedSampler (weighted : Bool) (classes : GroupedRecord.Classes Value) (bound : Nat) :
    SamplerReplay.Record Value :=
  if weighted then GroupedRecord.bounded classes bound
  else SamplerReplay.source (Probability.counting (Decoder.values (GroupedRecord.bounded classes bound).plan))

/-- Both runtime sampler routes preserve every bounded member and rank order. -/
theorem boundedSampler_members (weighted : Bool) (classes : GroupedRecord.Classes Value) (bound : Nat) :
    Decoder.values (boundedSampler weighted classes bound).plan =
      Decoder.values (GroupedRecord.bounded classes bound).plan := by
  cases weighted <;> simp [boundedSampler, SamplerReplay.source, Probability.counting,
    Decoder.values, List.map_map, Function.comp_def]

/-- The unweighted branch is the exact uniform member distribution, including duplicates. -/
theorem unweighted_sampler (classes : GroupedRecord.Classes Value) (bound : Nat) :
    (boundedSampler false classes bound).sampling.values =
      Probability.normalize (Probability.counting (Decoder.values (GroupedRecord.bounded classes bound).plan)) := rfl

/-- Runtime selection of the weighted branch preserves the correlated family's
full bounded rank probabilities. No desired sampler equation is a premise. -/
theorem weighted_family_sampler (code : Key → Nat)
    (program : Key → RecursiveJoinComposition.Body Key Root Symbol Root) (key : Key) (bound : Nat)
    (metadata : Metadata) (weighted : metadata.weighted = true) :
    Probability.map (fun entry => (entry.1, entry.2.1))
      (GroupedRecord.bounded (fun size => KeyedSource.family
        (RecursiveJoinFamily.pairedProgram code program) size key) bound).sampling.ranked =
      (boundedSampler metadata.weighted (fun size => KeyedSource.family
        (RecursiveJoinFamily.valueProgram program) size key) bound).sampling.ranked := by
  simpa only [boundedSampler, weighted, ↓reduceIte] using
    RecursiveJoinFamily.bounded_ranked_values code program key bound

/-- The Static wrapper selects stored weights exactly when the recursive runtime flag is set. -/
theorem bounded_static_dispatch (plan : SourcePlanPositions.Plan) (outcomes : Probability.Distribution Value)
    (minimum : Option Nat) (metadata : Metadata) (weights : Nat → Probability.Distribution Nat) :
    StaticSamplingDispatch.branch (StaticSamplingDispatch.boundedFields plan outcomes minimum metadata.weighted weights) =
      (if metadata.weighted then .stored else .uniform) ∧
    StaticSamplingDispatch.hasWeight (StaticSamplingDispatch.boundedFields plan outcomes minimum metadata.weighted weights) = metadata.weighted :=
  ⟨(StaticSamplingDispatch.bounded_dispatch plan outcomes minimum metadata.weighted weights).1,
    (StaticSamplingDispatch.bounded_dispatch plan outcomes minimum metadata.weighted weights).2.1⟩

end MicroCFTA.RecursiveJoinRuntime
