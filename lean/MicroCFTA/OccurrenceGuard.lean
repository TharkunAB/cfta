import MicroCFTA.RecursionProbe
import MicroCFTA.Decoder

/-!
# Recursive occurrence flags and zero-size contexts

The metadata follows `Ranked.Internal.Size`: pay guards size recursion but
does not add an engine term node; constructors guard both; products guard
one side only if the other side has no size-zero member. A product adds an
engine term node. Occurrence tokens remain separate under nested recursion.
-/

namespace MicroCFTA.OccurrenceGuard
open RecursionProbe MinimumSize

/-- The operations that affect occurrence flags and minimum sizes. -/
inductive Shape where
  | source (sizes : List Nat)
  | occurrence (token : Nat) (assumed : Option Nat)
  | map (inner : Shape)
  | pay (inner : Shape)
  | constructor (inner : Shape)
  | choice (left right : Shape)
  | product (left right : Shape)
  deriving Repr

/-- Finite size denotation of a probe shape under its current occurrence assumptions. -/
def sizes : Shape → List Nat
  | .source values => values
  | .occurrence _ assumed => assumed.toList
  | .map inner => sizes inner
  | .pay inner | .constructor inner => (sizes inner).map (· + 1)
  | .choice left right => sizes left ++ sizes right
  | .product left right => (sizes left).flatMap fun first => (sizes right).map (first + ·)

/-- Lists represent the source's finite token sets. -/
def union (left right : List Nat) : List Nat := (left ++ right).eraseDups

/-- The three independent token sets carried by a size index. -/
structure Summary where
  minimum : Option Nat
  unguarded : List Nat
  termless : List Nat
  used : List Nat
  deriving DecidableEq, Repr

/-- A sibling with minimum zero does not guard the recursive side. -/
def beside (other side : Summary) : List Nat :=
  if other.minimum = some 0 then side.unguarded else []

/-- Compute the source's metadata without reading any size counts or values. -/
def summary : Shape → Summary
  | .source values => ⟨values.min?, [], [], []⟩
  | .occurrence token assumed => ⟨assumed, [token], [token], [token]⟩
  | .map inner => summary inner
  | .pay inner => ⟨(summary inner).minimum.map (· + 1), [], (summary inner).termless, (summary inner).used⟩
  | .constructor inner => ⟨(summary inner).minimum.map (· + 1), [], [], (summary inner).used⟩
  | .choice left right => ⟨best (summary left).minimum (summary right).minimum,
      union (summary left).unguarded (summary right).unguarded,
      union (summary left).termless (summary right).termless,
      union (summary left).used (summary right).used⟩
  | .product left right => ⟨productMinimum (summary left).minimum (summary right).minimum,
      union (beside (summary right) (summary left)) (beside (summary left) (summary right)),
      [], union (summary left).used (summary right).used⟩

/-- Zero is the minimum of a finite natural-size list exactly when zero occurs. -/
theorem list_minimum_zero (values : List Nat) : values.min? = some 0 ↔ 0 ∈ values := by
  simp [List.min?_eq_some_iff]

/-- A choice has minimum zero exactly when one alternative has minimum zero. -/
theorem best_zero (left right : Option Nat) : best left right = some 0 ↔ left = some 0 ∨ right = some 0 := by
  cases left <;> cases right <;> simp [best] <;> omega

/-- A product has minimum zero exactly when both sides have minimum zero. -/
theorem product_zero (left right : Option Nat) :
    productMinimum left right = some 0 ↔ left = some 0 ∧ right = some 0 := by
  cases left <;> cases right <;> simp [productMinimum]

/-- The source's guard test reads exact size-zero membership of the sibling shape. -/
theorem minimum_zero (shape : Shape) : (summary shape).minimum = some 0 ↔ 0 ∈ sizes shape := by
  induction shape with
  | source values => exact list_minimum_zero values
  | occurrence token assumed => cases assumed <;> simp [summary, sizes, eq_comm]
  | map inner ih => exact ih
  | pay inner ih | constructor inner ih =>
      simp [summary, sizes, Option.map_eq_some_iff, List.mem_map]
  | choice left right ihl ihr => simp [summary, sizes, best_zero, ihl, ihr]
  | product left right ihl ihr =>
      simp [summary, sizes, product_zero, ihl, ihr, List.mem_flatMap, List.mem_map]

/-- A context exposes one recursive hole and records the extra size and engine term nodes around it. -/
structure Context where
  token : Nat
  size : Nat
  nodes : Nat
  deriving DecidableEq, Repr

/-- Independent context enumeration chooses sibling sizes and counts the constructors on the path. -/
def contexts : Shape → List Context
  | .source _ => []
  | .occurrence token _ => [⟨token, 0, 0⟩]
  | .map inner => contexts inner
  | .pay inner => (contexts inner).map fun context => {context with size := context.size + 1}
  | .constructor inner => (contexts inner).map fun context => {context with size := context.size + 1, nodes := context.nodes + 1}
  | .choice left right => contexts left ++ contexts right
  | .product left right =>
      ((contexts left).flatMap fun context => (sizes right).map fun size =>
        {context with size := context.size + size, nodes := context.nodes + 1}) ++
      ((contexts right).flatMap fun context => (sizes left).map fun size =>
        {context with size := size + context.size, nodes := context.nodes + 1})

/-- A zero-size recursive context can count a member without decreasing the recursive size. -/
def ZeroContext (token : Nat) (shape : Shape) : Prop :=
  ∃ context ∈ contexts shape, context.token = token ∧ context.size = 0

/-- A termless context can recur without adding an engine term node. -/
def TermlessContext (token : Nat) (shape : Shape) : Prop :=
  ∃ context ∈ contexts shape, context.token = token ∧ context.nodes = 0

/-- Product zero-size contexts come exactly from one unguarded side beside a size-zero sibling. -/
theorem product_zero_context (token : Nat) (left right : Shape) :
    ZeroContext token (.product left right) ↔
      (ZeroContext token left ∧ 0 ∈ sizes right) ∨ (0 ∈ sizes left ∧ ZeroContext token right) := by
  simp only [ZeroContext, contexts, List.mem_append, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨context, leftSide | rightSide, same, zero⟩
    · obtain ⟨original, member, size, found, rfl⟩ := leftSide
      exact Or.inl ⟨⟨original, member, same, by dsimp at zero; omega⟩, by simpa [show size = 0 by dsimp at zero; omega] using found⟩
    · obtain ⟨original, member, size, found, rfl⟩ := rightSide
      exact Or.inr ⟨by simpa [show size = 0 by dsimp at zero; omega] using found, ⟨original, member, same, by dsimp at zero; omega⟩⟩
  · rintro (⟨⟨original, member, same, zero⟩, sibling⟩ | ⟨sibling, ⟨original, member, same, zero⟩⟩)
    · refine ⟨{original with size := original.size + 0, nodes := original.nodes + 1},
        Or.inl ⟨original, member, 0, sibling, rfl⟩, same, ?_⟩
      simpa using zero
    · refine ⟨{original with size := 0 + original.size, nodes := original.nodes + 1},
        Or.inr ⟨original, member, 0, sibling, rfl⟩, same, ?_⟩
      simpa using zero

/-- The unguarded token set is exactly the independently defined zero-size context set. -/
theorem unguarded_exact (shape : Shape) (token : Nat) :
    token ∈ (summary shape).unguarded ↔ ZeroContext token shape := by
  induction shape with
  | source values => simp [summary, ZeroContext, contexts]
  | occurrence found assumed => simp [summary, ZeroContext, contexts, eq_comm]
  | map inner ih => exact ih
  | pay inner ih | constructor inner ih => simp [summary, ZeroContext, contexts, List.mem_map]
  | choice left right ihl ihr =>
      simp only [summary, union, List.mem_eraseDups, List.mem_append, ihl, ihr]
      simp [ZeroContext, contexts, or_and_right, exists_or]
  | product left right ihl ihr =>
      rw [product_zero_context]
      simp only [summary, union, List.mem_eraseDups, List.mem_append, beside]
      by_cases leftZero : (summary left).minimum = some 0 <;>
        by_cases rightZero : (summary right).minimum = some 0 <;>
          simp [leftZero, rightZero, ihl, ihr, ← minimum_zero]

/-- The termless token set is exactly the contexts that add no engine term node. -/
theorem termless_exact (shape : Shape) (token : Nat) :
    token ∈ (summary shape).termless ↔ TermlessContext token shape := by
  induction shape with
  | source values => simp [summary, TermlessContext, contexts]
  | occurrence found assumed => simp [summary, TermlessContext, contexts, eq_comm]
  | map inner ih => exact ih
  | pay inner ih =>
      change token ∈ (summary inner).termless ↔ _
      rw [ih]
      constructor
      · rintro ⟨context, present, same, zero⟩
        exact ⟨{context with size := context.size + 1}, List.mem_map.mpr ⟨context, present, rfl⟩, same, zero⟩
      · rintro ⟨context, present, same, zero⟩
        obtain ⟨original, member, rfl⟩ := List.mem_map.mp present
        exact ⟨original, member, same, zero⟩
  | constructor inner ih => simp [summary, TermlessContext, contexts, List.mem_map]
  | choice left right ihl ihr =>
      simp only [summary, union, List.mem_eraseDups, List.mem_append, ihl, ihr]
      simp [TermlessContext, contexts, or_and_right, exists_or]
  | product left right ihl ihr =>
      change token ∈ ([] : List Nat) ↔ _
      constructor
      · intro impossible; simp at impossible
      · rintro ⟨context, present, _, zero⟩
        rcases List.mem_append.mp present with leftSide | rightSide
        · obtain ⟨original, _, member⟩ := List.mem_flatMap.mp leftSide
          obtain ⟨size, _, rfl⟩ := List.mem_map.mp member
          simp at zero
        · obtain ⟨original, _, member⟩ := List.mem_flatMap.mp rightSide
          obtain ⟨size, _, rfl⟩ := List.mem_map.mp member
          simp at zero

/-- The public check rejects either size-unguarded or termless recursion. -/
def isUnguarded (token : Nat) (shape : Shape) : Bool :=
  decide (token ∈ (summary shape).unguarded) || decide (token ∈ (summary shape).termless)

/-- Accepted occurrence metadata proves strict growth of size and engine term nodes in every context. -/
theorem guarded_context_growth (shape : Shape) (token : Nat) (guarded : isUnguarded token shape = false)
    (context : Context) (present : context ∈ contexts shape) (same : context.token = token)
    (holeSize holeNodes : Nat) : holeSize < holeSize + context.size ∧ holeNodes < holeNodes + context.nodes := by
  have noZero : ¬ ZeroContext token shape := by
    intro zero
    have member := (unguarded_exact shape token).mpr zero
    simp [isUnguarded, member] at guarded
  have noTermless : ¬ TermlessContext token shape := by
    intro termless
    have member := (termless_exact shape token).mpr termless
    simp [isUnguarded, member] at guarded
  have positiveSize : context.size ≠ 0 := fun zero => noZero ⟨context, present, same, zero⟩
  have positiveNodes : context.nodes ≠ 0 := fun zero => noTermless ⟨context, present, same, zero⟩
  omega

/-- A size-zero sibling never guards the recursive occurrence. -/
theorem zero_sibling_rejected (token : Nat) (assumed : Option Nat) :
    isUnguarded token (.product (.source [0]) (.occurrence token assumed)) = true := by
  simp [isUnguarded, summary, beside, union]

/-- A pay alone changes size but leaves the term unchanged, so the source still rejects it. -/
theorem pay_only_rejected (token : Nat) (assumed : Option Nat) :
    isUnguarded token (.pay (.occurrence token assumed)) = true := by
  simp [isUnguarded, summary]

/-- A constructor guards both required forms of recursive growth. -/
theorem constructor_guarded (token : Nat) (assumed : Option Nat) :
    isUnguarded token (.constructor (.occurrence token assumed)) = false := by
  simp [isUnguarded, summary]

/-- Enumerate syntactic occurrence tokens independently of size productivity. -/
def occurrences : Shape → List Nat
  | .source _ => []
  | .occurrence token _ => [token]
  | .map inner | .pay inner | .constructor inner => occurrences inner
  | .choice left right | .product left right => occurrences left ++ occurrences right

/-- The source retains every reached token even when a product has no current finite member. -/
theorem used_exact (shape : Shape) (token : Nat) : token ∈ (summary shape).used ↔ token ∈ occurrences shape := by
  induction shape with
  | source values | occurrence found assumed => rfl
  | map inner ih | pay inner ih | constructor inner ih => exact ih
  | choice left right ihl ihr | product left right ihl ihr =>
      simp [summary, union, occurrences, ihl, ihr]

/-- A closed recursive occurrence retains its minimum and clears its own probe flags. -/
def closedProbe (minimum : Option Nat) : Summary := ⟨minimum, [], [], []⟩

/-- A grouped recursive member retains flags for enclosing recursions. -/
def closedWith (flags : Summary) (minimum : Option Nat) : Summary :=
  ⟨minimum, flags.unguarded, flags.termless, flags.used⟩

/-- Closing one recursion does not lose any enclosing occurrence token supplied by its body. -/
theorem closedWith_tokens (flags : Summary) (minimum : Option Nat) (token : Nat) :
    (token ∈ (closedWith flags minimum).unguarded ↔ token ∈ flags.unguarded) ∧
    (token ∈ (closedWith flags minimum).termless ↔ token ∈ flags.termless) ∧
    (token ∈ (closedWith flags minimum).used ↔ token ∈ flags.used) := ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

/-- The pure fields whose metadata `withKnotMetadata` replaces. -/
structure Index (α : Type) where
  count : Nat → Nat
  select : Nat → Nat → Option α
  selectInt : Nat → Nat → Option α
  metadata : Summary

/-- Build a fresh record with closed metadata and the live knot's count/decoder fields. -/
def withKnotMetadata (minimum : Option Nat) (closed : Summary) (index : Index α) : Index α :=
  ⟨index.count, index.select, index.selectInt, closedWith closed minimum⟩

/-- Replacing probe metadata leaves both decoder paths and all class counts unchanged. -/
theorem knot_fields (minimum : Option Nat) (closed : Summary) (index : Index α) :
    (withKnotMetadata minimum closed index).count = index.count ∧
    (withKnotMetadata minimum closed index).select = index.select ∧
    (withKnotMetadata minimum closed index).selectInt = index.selectInt := ⟨rfl, rfl, rfl⟩

end MicroCFTA.OccurrenceGuard
