import MicroCFTA.RecursiveRuntimeOrigins
import MicroCFTA.RecursiveUniformRuntime

/-!
# Runtime markers connected to complete family probabilities

Only primitive source records supply an unweighted finite-leaf contract.
All typed constructors derive the contract for their result. The source
family marker then chooses an equivalent sampler in both runtime branches.
-/
namespace MicroCFTA.RecursiveRuntimeVerified
open RecursiveJoinRuntime RecursiveRuntimeOrigins RecursiveUniformRuntime

/-- A checked template retains only the finite-leaf law needed when both
source weight flags are absent. It assumes no family sampler equation. -/
structure Body (Key Root Symbol Value : Type) where
  template : Template Key Root Symbol Value
  ordinary : (template.metadata (fun _ => placeholder)).weighted = false →
    (template.metadata (fun _ => placeholder)).massWeighted = false → Leaves template.checked.body.value

/-- Primitive source records expose their local unweighted finite-leaf law. -/
def source (body : RecursiveJoinRuntime.Body Key Root Symbol Value)
    (ordinary : body.metadata.weighted = false → body.metadata.massWeighted = false → Leaves body.checked.body.value) :
    Body Key Root Symbol Value := ⟨RecursiveRuntimeOrigins.source body, ordinary⟩

/-- An ordinary finite source supplies its actual weighted marker. If the
marker is false, only that source's finite class laws are required. -/
def finite [DecidableEq Symbol] (callbacks : KeyedNaryFields.LeafCallbacks Symbol)
    (description : FiniteSource.Source (Value × KeyedNaryAlignment.EngineTerm Symbol))
    (inverse : KeyedNaryFields.LeavesExact callbacks (.finite description : KeyedNaryAlignment.Recipe Key Root Symbol Value)) (weighted : Bool)
    (ordinary : weighted = false → ∀ size, Uniform (FiniteSource.atSize description size)) :
    Body Key Root Symbol Value :=
  source ⟨RecursiveJoinBodyFields.ofNary callbacks (.finite description) inverse, ⟨weighted, false, true⟩⟩
    (by
      intro unweighted _ size
      exact uniform_map Prod.fst _ (ordinary unweighted size))

/-- A pure finite source needs no probability premise beyond its local inverse callback. -/
def pure [DecidableEq Symbol] (callbacks : KeyedNaryFields.LeafCallbacks Symbol)
    (entry : Value × KeyedNaryAlignment.EngineTerm Symbol)
    (inverse : KeyedNaryFields.LeavesExact callbacks (.finite (.pure entry) : KeyedNaryAlignment.Recipe Key Root Symbol Value)) : Body Key Root Symbol Value :=
  finite callbacks (.pure entry) inverse false (by
    intro _ size
    cases size with
    | zero => exact uniform_counting [entry]
    | succ size => exact uniform_counting [])

/-- An explicitly retained finite key mass sets the source mass marker. Its
sampler is handled by the weighted path without an unweighted premise. -/
def retained [DecidableEq Symbol] (callbacks : KeyedNaryFields.LeafCallbacks Symbol)
    (mass : Nat → Rat) (positive : ∀ size, 0 < mass size)
    (description : FiniteSource.Source (Value × KeyedNaryAlignment.EngineTerm Symbol))
    (inverse : KeyedNaryFields.LeavesExact callbacks (.retained mass positive description : KeyedNaryAlignment.Recipe Key Root Symbol Value))
    (weighted : Bool) : Body Key Root Symbol Value :=
  source ⟨RecursiveJoinBodyFields.ofNary callbacks (.retained mass positive description) inverse,
    ⟨weighted, true, true⟩⟩ (by intro _ impossible; cases impossible)

/-- Recursive occurrences require no new finite-leaf probability assumption. -/
def occurrence [DecidableEq Symbol] (callbacks : KeyedNaryFields.LeafCallbacks Symbol) (key : Key) :
    Body Key Root Symbol Root where
  template := RecursiveRuntimeOrigins.occurrence callbacks key
  ordinary := by
    intro _ _
    simp [RecursiveRuntimeOrigins.occurrence, RecursiveJoinBodyFields.ofNary,
      RecursiveJoinComposition.ofNary, KeyedNaryAlignment.valueRecipe, Leaves]

/-- Value maps preserve the source finite-leaf contracts. -/
def map (transform : Value → Result) (inner : Body Key Root Symbol Value) : Body Key Root Symbol Result where
  template := RecursiveRuntimeOrigins.map transform inner.template
  ordinary := inner.ordinary

/-- Pay preserves all finite-leaf probability requirements. -/
def pay [DecidableEq Symbol] (inner : Body Key Root Symbol Value) : Body Key Root Symbol Value where
  template := RecursiveRuntimeOrigins.pay inner.template
  ordinary := inner.ordinary

/-- Labels preserve probabilities while the term compiler supplies their wrapper. -/
def label [DecidableEq Symbol] (symbol : Symbol) (inner : Body Key Root Symbol Value) : Body Key Root Symbol Value where
  template := RecursiveRuntimeOrigins.label symbol inner.template
  ordinary := inner.ordinary

/-- A false promoted choice marker means that both flags are false in every input. -/
theorem choice_unweighted (fields : List Metadata)
    (ordinary : (choiceMetadata fields).weighted = false) :
    ∀ field ∈ fields, field.weighted = false ∧ field.massWeighted = false := by
  rw [choice_weighted] at ordinary
  simpa [List.any_eq_false] using ordinary

/-- Empty alternatives have no nonuniform member. -/
theorem empty_leaves : Leaves (KeyedNaryAlignment.empty : KeyedSource.Recipe Key Root Value) := by
  intro size
  cases size with
  | zero => exact uniform_counting []
  | succ size =>
      cases size <;> exact uniform_counting []

/-- Flat choice composition derives its finite-leaf obligation from every branch. -/
theorem alternatives_leaves (branches : List (KeyedSource.Recipe Key Root Value))
    (leaves : ∀ branch ∈ branches, Leaves branch) : Leaves (KeyedNaryAlignment.alternatives branches) := by
  induction branches with
  | nil => exact empty_leaves
  | cons first rest ih =>
      cases rest with
      | nil => exact leaves first (by simp)
      | cons second rest =>
          exact ⟨leaves first (by simp), ih (fun child member => leaves child (by simp [member]))⟩

/-- Flat choices derive the unweighted contract from their exact runtime marker. -/
def nary (count : Nat) (branches : Fin count → Body Key Root Symbol Value) : Body Key Root Symbol Value where
  template := RecursiveRuntimeOrigins.nary count (fun index => (branches index).template)
  ordinary := by
    intro unweighted _
    have childFlags := choice_unweighted _ unweighted
    change Leaves (RecursiveJoinComposition.nary count _).value
    simp only [RecursiveJoinComposition.nary, RecursiveJoinGuards.alternatives_value, List.map_ofFn]
    apply alternatives_leaves
    intro branch present
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
    have flags := childFlags _ (List.mem_ofFn.mpr ⟨index, rfl⟩)
    exact (branches index).ordinary flags.1 flags.2

/-- Every heterogeneous argument retains its local runtime probability certificate. -/
inductive Chain (Key Root Symbol : Type) : Type → Type → Type 1 where
  | nil : Chain Key Root Symbol Result Result
  | cons (argument : Body Key Root Symbol Argument) (rest : Chain Key Root Symbol Operand Result) :
      Chain Key Root Symbol (Argument → Operand) Result

/-- Lower all local certificates to the previously proved template compiler. -/
def Chain.lower : Chain Key Root Symbol Operand Result → RecursiveRuntimeOrigins.Chain Key Root Symbol Operand Result
  | .nil => .nil
  | .cons argument rest => .cons argument.template rest.lower

/-- The typed product fold retains each argument's derived finite-leaf contract. -/
theorem Chain.accumulate_leaves (arguments : Chain Key Root Symbol Operand Result)
    (source : RecursiveJoinComposition.Compiled Key Root Symbol Operand (RecursiveJoinFields.Accumulated Symbol))
    (start : Leaves source.value)
    (flags : ∀ fields ∈ arguments.lower.fields (fun _ => placeholder),
      fields.weighted = false ∧ fields.massWeighted = false) :
    Leaves (RecursiveJoinComposition.accumulate source arguments.lower.lower.lower).value := by
  induction arguments with
  | nil => exact start
  | cons argument rest ih =>
      apply ih
      · exact ⟨start, argument.ordinary (flags _ (by simp [Chain.lower, RecursiveRuntimeOrigins.Chain.fields])).1
          (flags _ (by simp [Chain.lower, RecursiveRuntimeOrigins.Chain.fields])).2⟩
      · intro fields member
        exact flags fields (by simp [Chain.lower, RecursiveRuntimeOrigins.Chain.fields, member])

/-- Join's source flag promotion discharges every unweighted leaf obligation. -/
def join (component : Nat) (operation : Body Key Root Symbol Operand)
    (arguments : Chain Key Root Symbol Operand Result) : Body Key Root Symbol Result where
  template := RecursiveRuntimeOrigins.join component operation.template arguments.lower
  ordinary := by
    intro unweighted _
    have flags := (join_unweighted _ _).mp unweighted
    exact arguments.accumulate_leaves _ (operation.ordinary flags.1 flags.2.1) flags.2.2

/-- Erase local runtime probability certificates after construction. -/
def templates (program : Key → Body Key Root Symbol Root) : Key → Template Key Root Symbol Root :=
  fun key => (program key).template

/-- The false family marker derives every finite-leaf law from constructor
certificates and complete key enumeration. No global probability premise is used. -/
theorem family_leaves (keys : List Key) (complete : ∀ key, key ∈ keys)
    (program : Key → Body Key Root Symbol Root) (key : Key)
    (ordinary : (memberMetadata keys (templates program) key).weighted = false) :
    ∀ current, Leaves (program current).template.checked.body.value := by
  have all := choice_unweighted (bodyMetadata keys (templates program)) ordinary
  intro current
  have flags := all _ (List.mem_map.mpr ⟨current, complete current, rfl⟩)
  exact (program current).ordinary flags.1 flags.2

/-- The unweighted source branch retains every complete ranked probability
for a typed family that can contain arbitrary nested grouped joins. -/
theorem unweighted_family_exact (keys : List Key) (complete : ∀ key, key ∈ keys)
    (program : Key → Body Key Root Symbol Root) (key : Key) (bound : Nat)
    (ordinary : (memberMetadata keys (templates program) key).weighted = false) :
    (boundedSampler false (fun size => KeyedSource.family
      (fun key => (program key).template.checked.body.value) size key) bound).sampling.ranked =
      (GroupedRecord.bounded (fun size => KeyedSource.family
        (fun key => (program key).template.checked.body.value) size key) bound).sampling.ranked :=
  unweighted_family_ranked _ (family_leaves keys complete program key ordinary) key bound

/-- Both source runtime routes agree with the full derived family sampler.
The proof includes duplicate member values and unequal size-class counts. -/
theorem dispatched_family_exact (keys : List Key) (complete : ∀ key, key ∈ keys)
    (program : Key → Body Key Root Symbol Root) (key : Key) (bound : Nat) :
    (boundedSampler (memberMetadata keys (templates program) key).weighted
      (fun size => KeyedSource.family (fun key => (program key).template.checked.body.value) size key) bound).sampling.ranked =
      (GroupedRecord.bounded
        (fun size => KeyedSource.family (fun key => (program key).template.checked.body.value) size key) bound).sampling.ranked := by
  cases marked : (memberMetadata keys (templates program) key).weighted with
  | false => exact unweighted_family_exact keys complete program key bound marked
  | true => rfl

end MicroCFTA.RecursiveRuntimeVerified
