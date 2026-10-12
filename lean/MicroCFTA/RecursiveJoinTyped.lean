import MicroCFTA.RecursiveJoinLocal

/-!
# Typed heterogeneous recursive join fields

Each local leaf supplies a correlated value and term index. The curried
argument chain can have a different value type at every argument position.
Independent value application and term accumulation use the same size split.
-/
namespace MicroCFTA.RecursiveJoinTyped
open Language GeneratorCombinators IntegerTermViews SizedRank
open RecursiveCallbackTermination RecursiveJoinFields

/-- The source mapIndex preserves the complete count field. -/
def mapIndex (transform : Value → Result) (source : ValueIndex Value) : ValueIndex Result :=
  ⟨source.counts, fun position => (source.select position).map transform⟩

/-- The source productIndex selects the left-major Cartesian class directly. -/
def productIndex (combine : Left → Right → Result) (left : ValueIndex Left) (right : ValueIndex Right) : ValueIndex Result :=
  ⟨convolve left.counts right.counts, fun position => do
    let pair ← productSplit left.counts right.counts position
    let first ← left.select pair.1
    let second ← right.select pair.2
    pure (combine first second)⟩

/-- Mapping a finite selector preserves its complete source rank interval. -/
theorem map_indexed (transform : Value → Result) (source : ValueIndex Value) (indexed : Indexed source) :
    Indexed (mapIndex transform source) := by
  intro position
  constructor
  · rintro ⟨value, found⟩
    obtain ⟨original, selected, _⟩ := Option.map_eq_some_iff.mp found
    exact (indexed position).mp ⟨original, selected⟩
  · intro bound
    obtain ⟨value, selected⟩ := (indexed position).mpr bound
    exact ⟨transform value, by simp [mapIndex, selected]⟩

/-- Every typed product has exactly the convolution's successful rank interval. -/
theorem product_indexed (combine : Left → Right → Result) (left : ValueIndex Left) (right : ValueIndex Right)
    (leftIndexed : Indexed left) (rightIndexed : Indexed right) : Indexed (productIndex combine left right) := by
  intro position
  constructor
  · rintro ⟨value, selected⟩
    simp only [productIndex, bind, Option.bind_eq_some_iff] at selected
    obtain ⟨pair, split, before, first, after, second, _⟩ := selected
    have firstBound := (leftIndexed pair.1).mp ⟨before, first⟩
    have secondBound := (rightIndexed pair.2).mp ⟨after, second⟩
    have recombined := productPosition_productSplit left.counts right.counts position pair.1 pair.2 split
    rw [← recombined]
    exact product_rank_bound _ _ _ _ firstBound secondBound
  · intro within
    obtain ⟨first, second, recombined, firstBound, secondBound⟩ := RecursiveCallbackTables.product_split _ _ position within
    obtain ⟨before, firstSelected⟩ := (leftIndexed first).mpr firstBound
    obtain ⟨after, secondSelected⟩ := (rightIndexed second).mpr secondBound
    refine ⟨combine before after, ?_⟩
    rw [← recombined]
    simp [productIndex, productSplit_productPosition _ _ _ _ firstBound secondBound, firstSelected, secondSelected]

/-- Local leaf provenance pairs a user value and its independent private term. -/
structure Leaf (Symbol Value : Type) where
  paired : ValueIndex (Value × EngineTerm Symbol)
  positions : Callback Symbol

/-- Read the source user-value index from one correlated leaf. -/
def Leaf.values (leaf : Leaf Symbol Value) : ValueIndex Value := mapIndex Prod.fst leaf.paired

/-- Read the source term index and its independently supplied inverse callback. -/
def Leaf.terms (leaf : Leaf Symbol Value) : Finite Symbol :=
  ⟨leaf.paired.counts, fun position => (leaf.paired.select position).map Prod.snd, leaf.positions⟩

/-- A typed curried chain permits a distinct argument type at each position. -/
inductive Chain (Symbol : Type) : Type → Type → Type 1 where
  | nil : Chain Symbol Result Result
  | cons {Argument Tail Result : Type} (argument : Leaf Symbol Argument)
      (rest : Chain Symbol Tail Result) : Chain Symbol (Argument → Tail) Result

/-- The source term compiler retains every argument field in its original order. -/
def Chain.terms : Chain Symbol Operand Result → List (Finite Symbol)
  | .nil => []
  | .cons argument rest => argument.terms :: rest.terms

/-- Independent value application follows the source's left fold. -/
def Chain.values (source : ValueIndex Operand) : Chain Symbol Operand Result → ValueIndex Result
  | .nil => source
  | .cons argument rest => rest.values (productIndex (fun function value => function value) source argument.values)

/-- Pair one typed value application with the exact operation and argument forest. -/
def step (source : ValueIndex ((Argument → Result) × Accumulated Symbol))
    (argument : Leaf Symbol Argument) : ValueIndex (Result × Accumulated Symbol) :=
  productIndex (fun before after => (before.1 after.1, (before.2.1, before.2.2 ++ [after.2]))) source argument.paired

/-- The correlated compiler follows the same typed left fold as value application. -/
def Chain.paired (source : ValueIndex (Operand × Accumulated Symbol)) :
    Chain Symbol Operand Result → ValueIndex (Result × Accumulated Symbol)
  | .nil => source
  | .cons argument rest => rest.paired (step source argument)

/-- Each argument leaf has its complete local correlated rank interval. -/
def Chain.IndexedLeaves : Chain Symbol Operand Result → Prop
  | .nil => True
  | .cons argument rest => Indexed argument.paired ∧ rest.IndexedLeaves

/-- The typed collector cannot omit a valid product position. -/
theorem paired_indexed (chain : Chain Symbol Operand Result) (source : ValueIndex (Operand × Accumulated Symbol))
    (sourceIndexed : Indexed source) (leavesIndexed : chain.IndexedLeaves) : Indexed (chain.paired source) := by
  induction chain with
  | nil => exact sourceIndexed
  | cons argument rest ih =>
      exact ih (step source argument) (product_indexed _ source argument.paired sourceIndexed leavesIndexed.1) leavesIndexed.2

/-- The correlated application projects to the independently constructed value application. -/
theorem step_values (source : ValueIndex ((Argument → Result) × Accumulated Symbol))
    (argument : Leaf Symbol Argument) :
    mapIndex Prod.fst (step source argument) =
      productIndex (fun function value => function value) (mapIndex Prod.fst source) argument.values := by
  cases source with
  | mk counts select =>
      simp only [mapIndex, step, productIndex, Leaf.values]
      congr 1
      funext position
      cases split : productSplit counts argument.paired.counts position with
      | none => rfl
      | some pair =>
          cases first : select pair.1 <;> cases second : argument.paired.select pair.2 <;> simp [first, second]

/-- The correlated application projects to the separate term and forest selector. -/
theorem step_terms (source : ValueIndex ((Argument → Result) × Accumulated Symbol))
    (argument : Leaf Symbol Argument) :
    mapIndex Prod.snd (step source argument) = extend (mapIndex Prod.snd source) argument.terms := by
  cases source with
  | mk counts select =>
      simp only [mapIndex, step, productIndex, extend, Leaf.terms]
      congr 1
      funext position
      cases split : productSplit counts argument.paired.counts position with
      | none => rfl
      | some pair =>
          cases first : select pair.1 <;> cases second : argument.paired.select pair.2 <;> simp [first, second]

/-- Every arity preserves the full independently constructed value index. -/
theorem paired_values (chain : Chain Symbol Operand Result) (source : ValueIndex (Operand × Accumulated Symbol)) :
    mapIndex Prod.fst (chain.paired source) = chain.values (mapIndex Prod.fst source) := by
  induction chain with
  | nil => rfl
  | cons argument rest ih =>
      simp only [Chain.paired, Chain.values]
      rw [ih, step_values]

/-- Every arity preserves the separate operation and argument-forest index. -/
theorem paired_terms (chain : Chain Symbol Operand Result) (source : ValueIndex (Operand × Accumulated Symbol)) :
    mapIndex Prod.snd (chain.paired source) = accumulate (mapIndex Prod.snd source) chain.terms := by
  induction chain with
  | nil => rfl
  | cons argument rest ih =>
      simp only [Chain.paired, Chain.terms, accumulate, List.foldl_cons]
      rw [ih, step_terms]
      rfl

/-- Start from the operation's correlated value and term with an empty argument forest. -/
def initial (operation : Leaf Symbol Operand) : ValueIndex (Operand × Accumulated Symbol) :=
  mapIndex (fun entry => (entry.1, (entry.2, []))) operation.paired

/-- The source operation map preserves its independent value index. -/
theorem initial_values (operation : Leaf Symbol Operand) : mapIndex Prod.fst (initial operation) = operation.values := by
  simp only [mapIndex, initial, Leaf.values, Option.map_map]
  rfl

/-- The source operation map gives the same initial term index as recursiveChainTerms. -/
theorem initial_terms (operation : Leaf Symbol Operand) : mapIndex Prod.snd (initial operation) = start operation.terms := by
  simp only [mapIndex, initial, Leaf.terms, start, Option.map_map]
  rfl

/-- A heterogeneous source chain has one shared count field for values and terms. -/
theorem counts_aligned (operation : Leaf Symbol Operand) (chain : Chain Symbol Operand Result) :
    (chain.values operation.values).counts = (accumulate (start operation.terms) chain.terms).counts := by
  have values := congrArg ValueIndex.counts (paired_values chain (initial operation))
  have terms := congrArg ValueIndex.counts (paired_terms chain (initial operation))
  rw [initial_values] at values
  rw [initial_terms] at terms
  exact values.symm.trans terms

/-- A selected correlated result fixes the same value and private join at the same source rank. -/
theorem rank_aligned (component : Nat) (operation : Leaf Symbol Operand) (chain : Chain Symbol Operand Result)
    (position : Position) (value : Result) (payload : Accumulated Symbol)
    (found : (chain.paired (initial operation)).select position = some (value, payload)) :
    (chain.values operation.values).select position = some value ∧
      (RecursiveJoinCallbacks.field component operation.terms chain.terms).select position =
        some (SupportJoin.joinTerm component payload.1 payload.2) := by
  have values := congrArg (fun index => index.select position) (paired_values chain (initial operation))
  have terms := congrArg (fun index => index.select position) (paired_terms chain (initial operation))
  rw [initial_values] at values
  rw [initial_terms] at terms
  simp only [mapIndex, found, Option.map_some] at values terms
  exact ⟨values.symm, by simp [RecursiveJoinCallbacks.field, RecursiveJoinCallbacks.selected, ← terms]⟩

/-- Each valid source rank returns one correlated value and private join term. -/
theorem rank_complete (component : Nat) (operation : Leaf Symbol Operand) (chain : Chain Symbol Operand Result)
    (operationIndexed : Indexed operation.paired) (argumentsIndexed : chain.IndexedLeaves)
    (position : Position) (bound : position.rank < (chain.values operation.values).counts position.size) :
    ∃ value operationTerm argumentTerms,
      (chain.values operation.values).select position = some value ∧
      (RecursiveJoinCallbacks.field component operation.terms chain.terms).select position =
        some (SupportJoin.joinTerm component operationTerm argumentTerms) := by
  have indexed := paired_indexed chain (initial operation) (map_indexed _ operation.paired operationIndexed) argumentsIndexed
  have counts := congrArg ValueIndex.counts (paired_values chain (initial operation))
  rw [initial_values] at counts
  have bound' : position.rank < (chain.paired (initial operation)).counts position.size := by
    simpa only [mapIndex] using counts ▸ bound
  obtain ⟨⟨value, payload⟩, found⟩ := (indexed position).mpr bound'
  exact ⟨value, payload.1, payload.2, rank_aligned component operation chain position value payload found⟩

end MicroCFTA.RecursiveJoinTyped
