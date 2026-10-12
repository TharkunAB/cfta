import MicroCFTA.RecursiveJoinCallbacks
import MicroCFTA.RecursiveNaryCausality

/-!
# Restricted recursive join field contracts

Every operand request is shorter than the private join's children. These
local laws can therefore be used by a mutual callback height induction.
-/
namespace MicroCFTA.RecursiveJoinLocal
open Language GeneratorCombinators IntegerTermViews SizedRank
open RecursiveCallbackTermination RecursiveCallbackTables RecursiveCallbackDistinct
open RecursiveJoinFields RecursiveJoinCallbacks RecursiveFieldBounds
open RecursiveNaryCausality (Agree)

/-- Restricted finite-field exactness supplies a whole-term request law. -/
theorem whole_below (limit : Nat) (source : Finite Symbol) (exact : ExactBelow limit source)
    (term : EngineTerm Symbol) (bound : term.height ≤ limit) : WholeExact source term := by
  intro position
  rw [exact .whole [term] (by simpa [forestHeight] using bound)]
  constructor
  · rintro ⟨actual, found, same⟩
    have equal := StaticCheckedRanks.whole_eq actual term same
    simpa [equal] using found
  · intro found; exact ⟨term, found, rfl⟩

/-- Child callbacks only need correctness below the enclosing request height. -/
theorem children_exact_below (limit component : Nat) (operation : Finite Symbol) (arguments : List (Finite Symbol))
    (operationIndexed : FiniteIndex operation) (argumentsIndexed : ∀ argument ∈ arguments, FiniteIndex argument)
    (operationExact : ExactBelow limit operation) (argumentsExact : ∀ argument ∈ arguments, ExactBelow limit argument)
    (children : List (EngineTerm Symbol)) (bound : forestHeight children ≤ limit) (position : Position) :
    (position, true) ∈ childrenPositions component operation arguments children ↔
      selected component operation arguments position = some (.node .joinN children) :=
  children_exact_local component operation arguments operationIndexed argumentsIndexed children
    (fun term smaller => whole_below limit operation operationExact term (by omega))
    (fun argument member term smaller => whole_below limit argument (argumentsExact argument member) term (by omega)) position

/-- All source views preserve the restricted exactness needed for recursive induction. -/
theorem field_exact_below (limit component : Nat) (operation : Finite Symbol) (arguments : List (Finite Symbol))
    (operationIndexed : FiniteIndex operation) (argumentsIndexed : ∀ argument ∈ arguments, FiniteIndex argument)
    (operationExact : ExactBelow limit operation) (argumentsExact : ∀ argument ∈ arguments, ExactBelow limit argument) :
    ExactBelow limit (field component operation arguments) := by
  intro view wanted bound position
  constructor
  · intro member
    change (position, true) ∈ RecursiveJoinCallbacks.positions component operation arguments view wanted at member
    cases view with
    | labelled =>
        rw [RecursiveJoinCallbacks.positions, mem_sorted] at member
        exact ⟨.node .joinN wanted, (children_exact_below limit component operation arguments operationIndexed argumentsIndexed
          operationExact argumentsExact wanted bound position).mp member, rfl⟩
    | whole | spine =>
        simp only [RecursiveJoinCallbacks.positions] at member
        split at member
        · rename_i children
          simp only [mem_sorted] at member
          have childBound : forestHeight children ≤ limit := by
            simp only [forestHeight, Term.height, List.foldr_cons, List.foldr_nil, Nat.max_zero] at bound ⊢
            omega
          exact ⟨.node .joinN children, (children_exact_below limit component operation arguments operationIndexed argumentsIndexed
            operationExact argumentsExact children childBound position).mp member, by
              simp [project, spine, SupportTerms.applicationLeftChildren, SupportTerms.applicationTermChildren]⟩
        · simp at member
  · rintro ⟨term, found, rfl⟩
    change selected component operation arguments position = some term at found
    obtain ⟨payload, payloadFound, rfl⟩ := Option.map_eq_some_iff.mp found
    have selectedFound : selected component operation arguments position =
        some (SupportJoin.joinTerm component payload.1 payload.2) := by simp [selected, payloadFound]
    have childBound : forestHeight (.node .centerKeyed (payload.1 :: SupportJoin.keys component 0 payload.2.length) ::
        SupportJoin.arguments component 0 payload.2) ≤ limit := by
      cases view <;> simp only [SupportJoin.joinTerm, project, labelled, spine,
        SupportTerms.applicationLeftChildren, SupportTerms.applicationTermChildren, Option.getD_none,
        forestHeight, Term.height, List.foldr_cons, List.foldr_nil, Nat.max_zero] at bound ⊢ <;> omega
    have member := (children_exact_below limit component operation arguments operationIndexed argumentsIndexed
      operationExact argumentsExact _ childBound position).mpr selectedFound
    cases view <;> simpa [field, RecursiveJoinCallbacks.positions, SupportJoin.joinTerm, project, labelled, spine,
      SupportTerms.applicationLeftChildren, SupportTerms.applicationTermChildren, mem_sorted] using member

/-- The accumulated counts depend only on the operand count fields. -/
theorem accumulate_counts_same (left right : ValueIndex (Accumulated Symbol))
    (leftArguments rightArguments : List (Finite Symbol)) (same : left.counts = right.counts)
    (related : All₂ (fun a b => a.counts = b.counts) leftArguments rightArguments) :
    (accumulate left leftArguments).counts = (accumulate right rightArguments).counts := by
  induction related generalizing left right with
  | nil => exact same
  | @cons a b as bs head tail ih =>
      exact ih (extend left a) (extend right b) (by simp [extend, same, head])

/-- A callback fold reads only the count fields and the requested operand callbacks. -/
theorem requests_same (limit : Nat) (left right : ValueIndex (Accumulated Symbol))
    (leftArguments rightArguments : List (Finite Symbol)) (rows : List Checked)
    (same : left.counts = right.counts) (related : All₂ (Agree limit) leftArguments rightArguments)
    (terms : List (EngineTerm Symbol)) (bound : ∀ term ∈ terms, term.height ≤ limit) :
    (requests left rows (leftArguments.zip terms)).2 = (requests right rows (rightArguments.zip terms)).2 := by
  induction related generalizing left right rows terms with
  | nil => rfl
  | @cons a b as bs head tail ih =>
      cases terms with
      | nil => rfl
      | cons term terms =>
          have callback := head.2 .whole [term] (by simpa [forestHeight] using bound term (by simp))
          simp only [List.zip_cons_cons, requests, List.foldl_cons, requestStep]
          have next := ih (extend left a) (extend right b)
            (RecursiveCheckedRanks.productRows left.counts a.counts rows (a.positions .whole [term]))
            (by simp [extend, same, head.1]) terms (fun term member => bound term (by simp [member]))
          simpa only [requests, same, head.1, callback] using next

/-- Parsing and key masks make no extra callback observations. -/
theorem children_same (limit component : Nat) (left right : Finite Symbol)
    (leftArguments rightArguments : List (Finite Symbol)) (same : Agree limit left right)
    (related : All₂ (Agree limit) leftArguments rightArguments)
    (children : List (EngineTerm Symbol)) (bound : forestHeight children ≤ limit) :
    childrenPositions component left leftArguments children = childrenPositions component right rightArguments children := by
  have length := related.length_eq
  simp only [childrenPositions]
  split
  · rename_i operation keys nodes
    split
    · rfl
    · rename_i terms parsed
      rw [← length]
      split
      · have operationBound := operation_below operation keys nodes
        have callback := same.2 .whole [operation] (by simp only [forestHeight, List.foldr_cons, List.foldr_nil, Nat.max_zero]; omega)
        rw [callback]
        exact requests_same limit (start left) (start right) leftArguments rightArguments _ same.1 related terms
          (fun term member => by have small := argument_below operation keys nodes terms parsed term member; omega)
      · rfl
  · rfl

/-- Related local operands produce identical complete rows below the height bound. -/
theorem field_agree (limit component : Nat) (left right : Finite Symbol)
    (leftArguments rightArguments : List (Finite Symbol)) (same : Agree limit left right)
    (related : All₂ (Agree limit) leftArguments rightArguments) :
    Agree limit (field component left leftArguments) (field component right rightArguments) := by
  constructor
  · exact accumulate_counts_same (start left) (start right) leftArguments rightArguments same.1
      (related.imp (fun _ _ relation => relation.1))
  · intro view wanted bound
    cases view with
    | labelled =>
        simp only [field, RecursiveJoinCallbacks.positions]
        rw [children_same limit component left right leftArguments rightArguments same related wanted bound]
    | whole | spine =>
        simp only [field, RecursiveJoinCallbacks.positions]
        split
        · rename_i children
          have childBound : forestHeight children ≤ limit := by
            simp only [forestHeight, Term.height, List.foldr_cons, List.foldr_nil, Nat.max_zero] at bound ⊢
            omega
          rw [children_same limit component left right leftArguments rightArguments same related children childBound]
        · rfl

end MicroCFTA.RecursiveJoinLocal
