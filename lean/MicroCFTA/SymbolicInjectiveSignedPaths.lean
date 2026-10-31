import MicroCFTA.SymbolicSignedPaths
import MicroCFTA.SourceSizedPrefixEqualSizes
import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Sublist

set_option autoImplicit false

/-!
# Injective bounded signed path encoding

Valid child positions stay fixed. Invalid positions stay distinct above the bound.
The numeric lookup law chooses the bound from the actual parts length.
The full signed guard, normalization, Set, and Haskell adapters remain separate.
-/
namespace MicroCFTA.SymbolicInjectiveSignedPaths
open Language
open SymbolicSignedPaths (Path ArityBound lookup)
variable {Symbol α : Type}

/-- Retain valid positions and reserve disjoint even and odd invalid positions. -/
def encodeIndex (bound : Nat) (index : Int) : Nat :=
  if index < 0 then bound + 2 * (-index).toNat + 1
  else if index < (bound : Int) then index.toNat else bound + 2 * index.toNat

/-- Distinct signed indexes remain distinct, including every invalid index. -/
theorem encodeIndex_injective (bound : Nat) : Function.Injective (encodeIndex bound) := by
  intro first second same
  by_cases firstNegative : first < 0
  · by_cases secondNegative : second < 0
    · simp only [encodeIndex, firstNegative, secondNegative, ↓reduceIte] at same; omega
    · by_cases secondInside : second < (bound : Int)
      · simp only [encodeIndex, firstNegative, secondNegative, secondInside, ↓reduceIte] at same; omega
      · simp only [encodeIndex, firstNegative, secondNegative, secondInside, ↓reduceIte] at same; omega
  · by_cases firstInside : first < (bound : Int)
    · by_cases secondNegative : second < 0
      · simp only [encodeIndex, firstNegative, firstInside, secondNegative, ↓reduceIte] at same; omega
      · by_cases secondInside : second < (bound : Int)
        · simp only [encodeIndex, firstNegative, firstInside, secondNegative, secondInside, ↓reduceIte] at same; omega
        · simp only [encodeIndex, firstNegative, firstInside, secondNegative, secondInside, ↓reduceIte] at same; omega
    · by_cases secondNegative : second < 0
      · simp only [encodeIndex, firstNegative, firstInside, secondNegative, ↓reduceIte] at same; omega
      · by_cases secondInside : second < (bound : Int)
        · simp only [encodeIndex, firstNegative, firstInside, secondNegative, secondInside, ↓reduceIte] at same; omega
        · simp only [encodeIndex, firstNegative, firstInside, secondNegative, secondInside, ↓reduceIte] at same; omega

/-- The codec preserves actual signed lookup in every list within the bound. -/
theorem index_lookup (bound : Nat) (parts : List α) (bounded : parts.length ≤ bound) (index : Int) :
    parts[encodeIndex bound index]? = if index < 0 then none else parts[index.toNat]? := by
  by_cases negative : index < 0
  · have outside : parts.length ≤ encodeIndex bound index := by
      simp only [encodeIndex, negative, ↓reduceIte]; omega
    simp only [negative, ↓reduceIte, List.getElem?_eq_none outside]
  · by_cases inside : index < (bound : Int)
    · simp only [encodeIndex, negative, inside, ↓reduceIte]
    · have originalOutside : parts.length ≤ index.toNat := by omega
      have encodedOutside : parts.length ≤ encodeIndex bound index := by
        simp only [encodeIndex, negative, inside, ↓reduceIte]; omega
      simp only [negative, ↓reduceIte, List.getElem?_eq_none originalOutside, List.getElem?_eq_none encodedOutside]

/-- Encode the existing signed path type without changing its length. -/
def encode (bound : Nat) (path : Path) : List Nat := path.map (encodeIndex bound)

/-- Path equality is preserved in both directions. -/
theorem encode_injective (bound : Nat) : Function.Injective (encode bound) := by
  intro first second same
  induction first generalizing second with
  | nil => cases second <;> first | rfl | cases same
  | cons first rest ih =>
      cases second with
      | nil => cases same
      | cons second tail =>
          have heads := encodeIndex_injective bound (List.cons.inj same).1
          have tails := ih (List.cons.inj same).2
          cases heads
          cases tails
          rfl

/-- The original prefix relation is retained, including invalid signed segments. -/
theorem encode_prefix (bound : Nat) (first second : Path) :
    List.IsPrefix (encode bound first) (encode bound second) ↔ List.IsPrefix first second := by
  change List.IsPrefix (first.map (encodeIndex bound)) (second.map (encodeIndex bound)) ↔ _
  rw [List.prefix_map_iff]
  constructor
  · rintro ⟨middle, isPrefix, same⟩
    have identical := encode_injective bound same
    cases identical
    exact isPrefix
  · intro isPrefix; exact ⟨first, isPrefix, rfl⟩

/-- The existing finite-term arity predicate supplies exact full-path lookup. -/
theorem encode_lookup (bound : Nat) (term : Term Symbol) (bounded : ArityBound bound term) (path : Path) :
    term.atPath (encode bound path) = lookup term path := by
  induction path generalizing term with
  | nil => rfl
  | cons index rest ih =>
      cases bounded with
      | node symbol children arity childBounds =>
          simp only [encode, List.map_cons, Term.atPath, lookup]
          rw [index_lookup bound children arity index]
          by_cases negative : index < 0
          · simp [negative]
          · simp only [negative, ↓reduceIte]
            cases found : children[index.toNat]? with
            | none => rfl
            | some child => exact ih child (childBounds child (List.mem_of_getElem? found))

/-- The actual numeric lookup needs no supplied bound or nonnegative-index premise. -/
theorem sizeOf_encode (parts : List α) (index : Int) :
    SourceSizedPrefixEqualSizes.sizeOf parts (encodeIndex parts.length index : Int) =
      SourceSizedPrefixEqualSizes.sizeOf parts index := by
  have nonnegative : 0 ≤ (encodeIndex parts.length index : Int) := by omega
  simp only [SourceSizedPrefixEqualSizes.sizeOf, ite_eq_left nonnegative, List.head?_drop]
  change parts[encodeIndex parts.length index]? = if 0 ≤ index then parts[index.toNat]? else none
  rw [index_lookup parts.length parts (by omega) index]
  by_cases negative : index < 0
  · simp only [negative, show ¬0 ≤ index by omega, ↓reduceIte]
  · simp only [negative, show 0 ≤ index by omega, ↓reduceIte]

end MicroCFTA.SymbolicInjectiveSignedPaths
