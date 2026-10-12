import MicroCFTA.RecursiveJoinFamily

/-!
# Direct join selectors from compositional keyed bodies

Every compiled operand supplies its actual grouped count and decoder fields.
The source mixed-radix join selector agrees with the separate term recipe.
Leaf callbacks remain independent. Their local inverse laws imply the full
join callback law against that recipe's decoder.
-/
namespace MicroCFTA.RecursiveJoinCompiledFields
open Language GeneratorCombinators IntegerTermViews SizedRank
open RecursiveJoinComposition RecursiveJoinRecordBridge
open RecursiveJoinFields (ValueIndex)
open RecursiveJoinTyped (mapIndex)
open RecursiveCallbackTermination (EngineTerm Callback Finite FiniteExact)
open RecursiveJoinMass (Projects)

/-- Each compiled operand keeps its own independently supplied term callback. -/
abbrev Callbacks (Key Root Symbol : Type) := {Value : Type} → Body Key Root Symbol Value → Callback Symbol

/-- Read the actual count and direct decoder of each constructed operand class. -/
def recordIndex (classes : GroupedRecord.Classes Value) : ValueIndex Value :=
  ⟨fun size => Decoder.count (classes size).members.plan,
    fun position => Decoder.decode (classes position.size).members.plan position.rank⟩

/-- Constructed operand records supply their local provenance without a premise. -/
theorem record_realizes (classes : GroupedRecord.Classes Value) : Realizes classes (recordIndex classes) :=
  ⟨fun _ => rfl, fun _ => rfl⟩

/-- A correlated compiled body supplies the direct typed leaf and its term callback. -/
def leaf (callbacks : Callbacks Key Root Symbol)
    (environment : Key → GroupedRecord.Classes (Root × EngineTerm Symbol))
    (body : Body Key Root Symbol Value) : RecursiveJoinTyped.Leaf Symbol Value :=
  ⟨recordIndex (KeyedSource.record body.paired environment), callbacks body⟩

/-- Evaluate all heterogeneous operands in one recursive environment. -/
def chain (callbacks : Callbacks Key Root Symbol)
    (environment : Key → GroupedRecord.Classes (Root × EngineTerm Symbol)) :
    Chain Key Root Symbol Operand Result → RecursiveJoinTyped.Chain Symbol Operand Result
  | .nil => .nil
  | .cons argument rest => .cons (leaf callbacks environment argument) (chain callbacks environment rest)

/-- The compiled paired fold realizes the source direct product fold at every arity. -/
theorem accumulate_realizes (callbacks : Callbacks Key Root Symbol)
    (environment : Key → GroupedRecord.Classes (Root × EngineTerm Symbol))
    (arguments : Chain Key Root Symbol Operand Result)
    (source : Compiled Key Root Symbol Operand (RecursiveJoinFields.Accumulated Symbol))
    (index : ValueIndex (Operand × RecursiveJoinFields.Accumulated Symbol))
    (realizes : Realizes (KeyedSource.record source.paired environment) index) :
    Realizes (KeyedSource.record (accumulate source arguments).paired environment)
      ((chain callbacks environment arguments).paired index) := by
  induction arguments with
  | nil => exact realizes
  | cons argument rest ih =>
      exact ih _ _ (product_realizes _ _ _ _ _ realizes (record_realizes _))

/-- The complete compiled join retains the exact independently selected JoinN payload. -/
theorem join_realizes (callbacks : Callbacks Key Root Symbol)
    (environment : Key → GroupedRecord.Classes (Root × EngineTerm Symbol))
    (component : Nat) (operation : Body Key Root Symbol Operand) (arguments : Chain Key Root Symbol Operand Result) :
    Realizes (KeyedSource.record (join component operation arguments).paired environment)
      (mapIndex (fun entry => (entry.1, SupportJoin.joinTerm component entry.2.1 entry.2.2))
        ((chain callbacks environment arguments).paired (RecursiveJoinTyped.initial (leaf callbacks environment operation)))) := by
  exact map_realizes _ _ _ (accumulate_realizes callbacks environment arguments _ _
    (map_realizes _ _ _ (record_realizes _)))

/-- The independent term recipe decodes exactly the source direct join selector. -/
theorem term_selector (callbacks : Callbacks Key Root Symbol)
    (environment : Key → GroupedRecord.Classes (Root × EngineTerm Symbol))
    (terms : Key → GroupedRecord.Classes (EngineTerm Symbol))
    (aligned : ∀ key size, Projects Prod.snd (environment key size) (terms key size))
    (component : Nat) (operation : Body Key Root Symbol Operand) (arguments : Chain Key Root Symbol Operand Result)
    (position : Position) :
    Decoder.decode (KeyedSource.record (join component operation arguments).term terms position.size).members.plan position.rank =
      (RecursiveJoinCallbacks.field component (leaf callbacks environment operation).terms
        (chain callbacks environment arguments).terms).select position := by
  rw [← RecursiveJoinMass.projects_decode _ _ _ ((join component operation arguments).terms environment terms aligned position.size) position.rank,
    (join_realizes callbacks environment component operation arguments).2 position]
  have fields := congrArg (fun index => index.select position)
    (RecursiveJoinTyped.paired_terms (chain callbacks environment arguments)
      (RecursiveJoinTyped.initial (leaf callbacks environment operation)))
  rw [RecursiveJoinTyped.initial_terms] at fields
  simp only [mapIndex] at fields
  simp only [mapIndex, Option.map_map, Function.comp_def, RecursiveJoinCallbacks.field, RecursiveJoinCallbacks.selected]
  rw [← fields]
  simp only [Option.map_map, Function.comp_def]

/-- Every compiled operand term index has its complete successful rank interval. -/
theorem leaf_indexed (callbacks : Callbacks Key Root Symbol)
    (environment : Key → GroupedRecord.Classes (Root × EngineTerm Symbol))
    (body : Body Key Root Symbol Value) :
    RecursiveCallbackTables.FiniteIndex (leaf callbacks environment body).terms :=
  RecursiveJoinTyped.map_indexed Prod.snd _ (realized_indexed _ _ (record_realizes _))

/-- Every heterogeneous compiled argument retains its complete class interval. -/
theorem chain_indexed (callbacks : Callbacks Key Root Symbol)
    (environment : Key → GroupedRecord.Classes (Root × EngineTerm Symbol))
    (arguments : Chain Key Root Symbol Operand Result) :
    ∀ argument ∈ (chain callbacks environment arguments).terms, RecursiveCallbackTables.FiniteIndex argument := by
  induction arguments with
  | nil => simp [chain, RecursiveJoinTyped.Chain.terms]
  | cons argument rest ih =>
      intro field member
      simp only [chain, RecursiveJoinTyped.Chain.terms, List.mem_cons] at member
      rcases member with rfl | member
      · exact leaf_indexed callbacks environment argument
      · exact ih field member

/-- Callback correctness for each operand is stated against its independent term record. -/
def LeafExact (callbacks : Callbacks Key Root Symbol)
    (terms : Key → GroupedRecord.Classes (EngineTerm Symbol)) (body : Body Key Root Symbol Value) : Prop :=
  FiniteExact ⟨fun size => Decoder.count (KeyedSource.record body.term terms size).members.plan,
    fun position => Decoder.decode (KeyedSource.record body.term terms position.size).members.plan position.rank,
    callbacks body⟩

/-- Every argument supplies only its own callback law. -/
def ChainExact (callbacks : Callbacks Key Root Symbol)
    (terms : Key → GroupedRecord.Classes (EngineTerm Symbol)) : Chain Key Root Symbol Operand Result → Prop
  | .nil => True
  | .cons argument rest => LeafExact callbacks terms argument ∧ ChainExact callbacks terms rest

/-- Local term provenance converts operand callback laws to the direct field laws. -/
theorem leaf_exact (callbacks : Callbacks Key Root Symbol)
    (environment : Key → GroupedRecord.Classes (Root × EngineTerm Symbol))
    (terms : Key → GroupedRecord.Classes (EngineTerm Symbol))
    (aligned : ∀ key size, Projects Prod.snd (environment key size) (terms key size))
    (body : Body Key Root Symbol Value) (exact : LeafExact callbacks terms body) :
    FiniteExact (leaf callbacks environment body).terms := by
  intro view wanted position
  have agreement := RecursiveJoinMass.projects_decode _ _ _ (body.terms environment terms aligned position.size) position.rank
  simpa only [leaf, RecursiveJoinTyped.Leaf.terms, recordIndex, agreement] using exact view wanted position

/-- All heterogeneous argument callbacks inherit their local independent decoder laws. -/
theorem chain_exact (callbacks : Callbacks Key Root Symbol)
    (environment : Key → GroupedRecord.Classes (Root × EngineTerm Symbol))
    (terms : Key → GroupedRecord.Classes (EngineTerm Symbol))
    (aligned : ∀ key size, Projects Prod.snd (environment key size) (terms key size))
    (arguments : Chain Key Root Symbol Operand Result) (exact : ChainExact callbacks terms arguments) :
    ∀ argument ∈ (chain callbacks environment arguments).terms, FiniteExact argument := by
  induction arguments with
  | nil => simp [chain, RecursiveJoinTyped.Chain.terms]
  | cons argument rest ih =>
      intro field member
      simp only [chain, RecursiveJoinTyped.Chain.terms, List.mem_cons] at member
      rcases member with rfl | member
      · exact leaf_exact callbacks environment terms aligned argument exact.1
      · exact ih exact.2 field member

/-- The actual join inverse selects precisely the independently compiled term at the same rank. -/
theorem callback_exact (callbacks : Callbacks Key Root Symbol)
    (environment : Key → GroupedRecord.Classes (Root × EngineTerm Symbol))
    (terms : Key → GroupedRecord.Classes (EngineTerm Symbol))
    (aligned : ∀ key size, Projects Prod.snd (environment key size) (terms key size))
    (component : Nat) (operation : Body Key Root Symbol Operand) (arguments : Chain Key Root Symbol Operand Result)
    (operationExact : LeafExact callbacks terms operation) (argumentsExact : ChainExact callbacks terms arguments)
    (view : View) (wanted : List (EngineTerm Symbol)) (position : Position) :
    (position, true) ∈ (RecursiveJoinCallbacks.field component (leaf callbacks environment operation).terms
      (chain callbacks environment arguments).terms).positions view wanted ↔
    ∃ term, Decoder.decode (KeyedSource.record (join component operation arguments).term terms position.size).members.plan position.rank = some term ∧
      project view term = wanted := by
  rw [term_selector callbacks environment terms aligned]
  exact RecursiveJoinCallbacks.field_exact component _ _
    (leaf_indexed callbacks environment operation)
    (chain_indexed callbacks environment arguments)
    (leaf_exact callbacks environment terms aligned operation operationExact)
    (chain_exact callbacks environment terms aligned arguments argumentsExact) view wanted position

end MicroCFTA.RecursiveJoinCompiledFields
