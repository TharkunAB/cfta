import MicroCFTA.DecoderDispatch
import MicroCFTA.Sampler

/-!
# Checked machine arithmetic for rank decoders

The word width is one sign bit plus `bits` magnitude bits. Casts and word
arithmetic use the actual power-of-two modulus. Signed reads use two's
complement. Valid selected products derive bounds on both factors. A zero
product needs no bound on its unused factor.
-/
namespace MicroCFTA.DecoderMachineBounds
open DecoderDispatch

/-- The positive half of a signed word's residue range. -/
def half (bits : Nat) : Nat := 2 ^ bits

/-- The modulus for a word with one sign bit and bits magnitude bits. -/
def modulus (bits : Nat) : Nat := 2 * half bits

/-- The largest nonnegative signed value. -/
def maximum (bits : Nat) : Nat := half bits - 1

/-- Convert an arbitrary natural count to its stored word bits. -/
def cast (bits value : Nat) : Nat := value % modulus bits

/-- Read a stored word as a signed two's-complement integer. -/
def signed (bits word : Nat) : Int :=
  let value := cast bits word
  if value < half bits then (value : Int) else (value : Int) - (modulus bits : Int)

/-- The source Integer-to-Int narrowing conversion. -/
def narrow (bits value : Nat) : Int := signed bits (cast bits value)

/-- Machine addition wraps at the word modulus. -/
def add (bits left right : Nat) : Nat := cast bits (left + right)

/-- Machine multiplication wraps at the word modulus. -/
def multiply (bits left right : Nat) : Nat := cast bits (left * right)

/-- Subtract two stored words, retaining their modular representation. -/
def subtract (bits left right : Nat) : Nat := cast bits (left + modulus bits - right)

/-- The chosen width has a nonempty positive half range. -/
theorem half_positive (bits : Nat) : 0 < half bits := Nat.two_pow_pos bits

/-- The signed maximum supplies the exact modulus used by checked sampler casts. -/
theorem maximum_succ (bits : Nat) : maximum bits + 1 = half bits := by
  have positive := half_positive bits
  simp only [maximum]
  omega

/-- A checked nonnegative count retains all of its bits. -/
theorem cast_exact (bits value : Nat) (fits : value ≤ maximum bits) : cast bits value = value := by
  have positive := half_positive bits
  unfold cast modulus maximum at *
  exact Nat.mod_eq_of_lt (by omega)

/-- A checked nonnegative count also retains its signed interpretation. -/
theorem signed_exact (bits value : Nat) (fits : value ≤ maximum bits) : signed bits value = (value : Int) := by
  have positive := half_positive bits
  rw [signed, cast_exact bits value fits]
  have below : value < half bits := by unfold maximum at fits; omega
  simp [below]

/-- Narrowing a checked count is exact, including at maxBound. -/
theorem narrow_exact (bits value : Nat) (fits : value ≤ maximum bits) : narrow bits value = (value : Int) := by
  rw [narrow, cast_exact bits value fits, signed_exact bits value fits]

/-- The existing checked-rank theorem discharges both modular and signed rank conversion. -/
theorem checked_rank (bits bound rank : Nat) (fits : bound ≤ maximum bits) (valid : rank < bound) :
    cast bits rank = rank ∧ narrow bits rank = (rank : Int) := by
  have checked := Sampler.checked_machine_rank (maximum bits) bound rank fits valid
  have modulo : modulus bits = 2 * (maximum bits + 1) := by rw [maximum_succ]; rfl
  exact ⟨by simpa only [cast, modulo] using checked.1, narrow_exact bits rank (by omega)⟩

/-- Addition of converted counts has the same wrapped result as converting their sum. -/
theorem add_cast (bits left right : Nat) :
    add bits (cast bits left) (cast bits right) = cast bits (left + right) := by
  simp only [add, cast, Nat.add_mod, Nat.mod_mod]

/-- Multiplication of converted factors has the same wrapped result as converting their product. -/
theorem multiply_cast (bits left right : Nat) :
    multiply bits (cast bits left) (cast bits right) = cast bits (left * right) := by
  simp only [multiply, cast, Nat.mul_mod, Nat.mod_mod]

/-- A checked sum has the exact signed result after machine addition. -/
theorem add_exact (bits left right : Nat) (fits : left + right ≤ maximum bits) :
    signed bits (add bits (cast bits left) (cast bits right)) = ((left + right : Nat) : Int) := by
  rw [add_cast]
  exact narrow_exact bits _ fits

/-- A checked product is exact even if an unused zero-product factor does not fit. -/
theorem multiply_exact (bits left right : Nat) (fits : left * right ≤ maximum bits) :
    signed bits (multiply bits (cast bits left) (cast bits right)) = ((left * right : Nat) : Int) := by
  rw [multiply_cast]
  exact narrow_exact bits _ fits

/-- Zero-width blocks remain zero for arbitrary unused factors. -/
theorem zero_product (bits factor : Nat) :
    signed bits (multiply bits (cast bits factor) (cast bits 0)) = 0 ∧
      signed bits (multiply bits (cast bits 0) (cast bits factor)) = 0 := by
  constructor
  · simpa using multiply_exact bits factor 0 (by simp)
  · simpa using multiply_exact bits 0 factor (by simp)

/-- Checked subtraction returns the exact stored nonnegative difference. -/
theorem subtract_cast (bits left right : Nat) (fits : left ≤ maximum bits) (ordered : right ≤ left) :
    subtract bits (cast bits left) (cast bits right) = cast bits (left - right) := by
  rw [cast_exact bits left fits, cast_exact bits right (Nat.le_trans ordered fits)]
  have same : left + modulus bits - right = (left - right) + modulus bits := by omega
  simp only [subtract, same, cast, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]

/-- A selected product block has two positive factors, each bounded by the checked total. -/
theorem product_bounds (bits left right rank : Nat)
    (fits : left * right ≤ maximum bits) (valid : rank < left * right) :
    0 < left ∧ 0 < right ∧ left ≤ maximum bits ∧ right ≤ maximum bits ∧
      rank / right < left ∧ rank % right < right := by
  have leftPositive : 0 < left := by cases left <;> simp_all
  have rightPositive : 0 < right := by cases right <;> simp_all
  have leftBound := Nat.le_trans (Nat.le_mul_of_pos_right left rightPositive) fits
  have rightBound := Nat.le_trans (Nat.le_mul_of_pos_left right leftPositive) fits
  have ranks := Probability.split_lt valid
  exact ⟨leftPositive, rightPositive, leftBound, rightBound, ranks⟩

/-- Mathematical signed quotRem. Source calls must have a nonzero divisor. -/
def quotRem (bits position radix : Nat) : Int × Int :=
  (Int.tdiv (signed bits position) (signed bits radix), Int.tmod (signed bits position) (signed bits radix))

/-- Positive checked operands make signed quotRem exactly the natural quotient and remainder. -/
theorem quotRem_exact (bits position radix : Nat) (positionFits : position ≤ maximum bits)
    (radixFits : radix ≤ maximum bits) (_positive : 0 < radix) :
    quotRem bits (cast bits position) (cast bits radix) = (((position / radix : Nat) : Int), ((position % radix : Nat) : Int)) := by
  unfold quotRem
  change (Int.tdiv (narrow bits position) (narrow bits radix), Int.tmod (narrow bits position) (narrow bits radix)) = _
  rw [narrow_exact bits position positionFits, narrow_exact bits radix radixFits]
  rfl

/-- A selected product needs no factor-range premise beyond its checked block size. -/
theorem selected_product (bits left right rank : Nat)
    (fits : left * right ≤ maximum bits) (valid : rank < left * right) :
    quotRem bits (cast bits rank) (cast bits right) = (((rank / right : Nat) : Int), ((rank % right : Nat) : Int)) ∧
      rank / right < left ∧ rank % right < right := by
  obtain ⟨_, positive, _, rightFits, quotient, remainder⟩ := product_bounds bits left right rank fits valid
  exact ⟨quotRem_exact bits rank right (by omega) rightFits positive, quotient, remainder⟩

/-- The local compiler narrows only after its own cardinality passes the range guard. -/
def localRank (bits count rank : Nat) : Int :=
  if count ≤ maximum bits then narrow bits rank else (rank : Int)

/-- Both branches of compileLocalRank preserve every valid local rank. -/
theorem localRank_exact (bits count rank : Nat) (valid : rank < count) : localRank bits count rank = (rank : Int) := by
  unfold localRank
  split
  · next fits => exact (checked_rank bits count rank fits valid).2
  · rfl

/-- A wide outer product can still narrow a checked argument-local remainder. -/
theorem wide_product_local (bits left right rank : Nat) (valid : rank < left * right) :
    localRank bits left (rank / right) = ((rank / right : Nat) : Int) ∧
      localRank bits right (rank % right) = ((rank % right : Nat) : Int) := by
  have ranks := Probability.split_lt valid
  exact ⟨localRank_exact bits left _ ranks.1, localRank_exact bits right _ ranks.2⟩

/-- Execute offsetParts with stored word offsets and machine addition. -/
def offsetWords (bits offset : Nat) : List (Nat × Payload) → List (Nat × Payload)
  | [] => []
  | (count, payload) :: rest =>
      if 0 < count then (offset, payload) :: offsetWords bits (add bits offset (cast bits count)) rest
      else offsetWords bits offset rest

/-- Every intermediate machine offset is the modular image of its exact cumulative offset. -/
theorem offsetWords_cast (bits offset : Nat) (parts : List (Nat × Payload)) :
    offsetWords bits (cast bits offset) parts =
      (offsetParts offset parts).map (fun entry => (cast bits entry.1, entry.2)) := by
  induction parts generalizing offset with
  | nil => simp [offsetWords, offsetParts]
  | cons first rest ih =>
      rcases first with ⟨count, payload⟩
      by_cases positive : 0 < count <;> simp [offsetWords, offsetParts, positive, add_cast, ih]

/-- A checked cumulative total makes every stored offset's signed read exact. -/
theorem offsets_signed_exact (bits offset : Nat) (parts : List (Nat × Payload))
    (fits : offset + total parts ≤ maximum bits) :
    (offsetWords bits (cast bits offset) parts).map (fun entry => (signed bits entry.1, entry.2)) =
      (offsetParts offset parts).map (fun entry => ((entry.1 : Int), entry.2)) := by
  rw [offsetWords_cast, List.map_map]
  apply List.map_congr_left
  intro entry member
  have upper := offsets_upper parts offset entry member
  have exact := narrow_exact bits entry.1 (by omega)
  simpa only [Function.comp_apply, narrow] using congrArg (fun value => (value, entry.2)) exact

/-- One product size split retains both exact factor counts and its source payload. -/
structure ProductPart (Payload : Type) where
  functions : Nat
  arguments : Nat
  payload : Payload

/-- The checked class cardinality is the sum of its exact product block widths. -/
def productTotal (parts : List (ProductPart Payload)) : Nat :=
  (parts.map (fun part => part.functions * part.arguments)).sum

/-- The source arbitrary-precision productSplit scan. -/
def productSplit : List (ProductPart Payload) → Nat → Option (Payload × (Nat × Nat))
  | [], _ => none
  | part :: rest, position =>
      let block := part.functions * part.arguments
      if position < block then some (part.payload, position / part.arguments, position % part.arguments)
      else productSplit rest (position - block)

/-- The source productSplitInt scan casts both factors before multiplication. -/
def productSplitWord (bits : Nat) : List (ProductPart Payload) → Nat → Option (Payload × (Int × Int))
  | [], _ => none
  | part :: rest, position =>
      let argument := cast bits part.arguments
      let block := multiply bits (cast bits part.functions) argument
      if signed bits position < signed bits block then some (part.payload, quotRem bits position argument)
      else productSplitWord bits rest (subtract bits position block)

/-- A checked complete product class gives the same selected block and component ranks in Int arithmetic. -/
theorem productSplitWord_exact (bits : Nat) (parts : List (ProductPart Payload)) (rank : Nat)
    (fits : productTotal parts ≤ maximum bits) (valid : rank < productTotal parts) :
    productSplitWord bits parts (cast bits rank) =
      (productSplit parts rank).map (fun result => (result.1, (result.2.1 : Int), (result.2.2 : Int))) := by
  induction parts generalizing rank with
  | nil => simp [productTotal] at valid
  | cons part rest ih =>
      have totalEq : productTotal (part :: rest) = part.functions * part.arguments + productTotal rest := by simp [productTotal]
      rw [totalEq] at fits valid
      have blockFits : part.functions * part.arguments ≤ maximum bits := by omega
      have rankFits : rank ≤ maximum bits := by omega
      have blockEq := multiply_exact bits part.functions part.arguments blockFits
      have rankEq := narrow_exact bits rank rankFits
      change signed bits (cast bits rank) = (rank : Int) at rankEq
      simp only [productSplitWord, rankEq, blockEq]
      by_cases here : rank < part.functions * part.arguments
      · have hereInt : (rank : Int) < (part.functions * part.arguments : Nat) := by omega
        have selected := (selected_product bits part.functions part.arguments rank blockFits here).1
        simp only [hereInt, ↓reduceIte, selected, productSplit, here, Option.map_some]
      · have later : ¬ (rank : Int) < (part.functions * part.arguments : Nat) := by omega
        have ordered : part.functions * part.arguments ≤ rank := by omega
        simp only [later, ↓reduceIte, multiply_cast, subtract_cast bits rank _ rankFits ordered]
        have exact := ih (rank - part.functions * part.arguments) (by omega) (by omega)
        simpa only [productSplit, here, ↓reduceIte] using exact

/-- Every valid class rank selects a positive block and two in-range component ranks. -/
theorem productSplit_total (parts : List (ProductPart Payload)) (rank : Nat) (valid : rank < productTotal parts) :
    ∃ part ∈ parts, ∃ functionRank argumentRank : Nat,
      productSplit parts rank = some (part.payload, functionRank, argumentRank) ∧
      functionRank < part.functions ∧ argumentRank < part.arguments := by
  induction parts generalizing rank with
  | nil => simp [productTotal] at valid
  | cons part rest ih =>
      by_cases here : rank < part.functions * part.arguments
      · have bounds := Probability.split_lt here
        exact ⟨part, by simp, rank / part.arguments, rank % part.arguments,
          by simp [productSplit, here], bounds⟩
      · have restValid : rank - part.functions * part.arguments < productTotal rest := by
          change rank < part.functions * part.arguments + productTotal rest at valid
          omega
        obtain ⟨selected, member, functionRank, argumentRank, found, bounds⟩ := ih _ restValid
        exact ⟨selected, by simp [member], functionRank, argumentRank,
          by simpa only [productSplit, here, ↓reduceIte] using found, bounds⟩

/-- The checked machine scan cannot reach the source's exhausted-list error. -/
theorem productSplitWord_total (bits : Nat) (parts : List (ProductPart Payload)) (rank : Nat)
    (fits : productTotal parts ≤ maximum bits) (valid : rank < productTotal parts) :
    ∃ part ∈ parts, ∃ functionRank argumentRank : Nat,
      productSplitWord bits parts (cast bits rank) =
        some (part.payload, (functionRank : Int), (argumentRank : Int)) ∧
      functionRank < part.functions ∧ argumentRank < part.arguments := by
  obtain ⟨part, member, functionRank, argumentRank, found, bounds⟩ := productSplit_total parts rank valid
  refine ⟨part, member, functionRank, argumentRank, ?_, bounds⟩
  rw [productSplitWord_exact bits parts rank fits valid, found]
  rfl

/-- Execute the general fused binary application's two signed quotRem operations. -/
def fusedRanks (bits argumentsLeft argumentsRight rank : Nat) : Int × (Int × Int) :=
  let outer := quotRem bits (cast bits rank) (cast bits argumentsRight)
  let inner := quotRem bits (cast bits outer.1.toNat) (cast bits argumentsLeft)
  (inner.1, inner.2, outer.2)

/-- A checked fused product derives exact machine coordinates and every local rank bound. -/
theorem fusedRanks_exact (bits functions left right rank : Nat)
    (fits : functions * left * right ≤ maximum bits) (valid : rank < functions * left * right) :
    fusedRanks bits left right rank =
      (((rank / right / left : Nat) : Int), ((rank / right % left : Nat) : Int), ((rank % right : Nat) : Int)) ∧
      rank / right / left < functions ∧ rank / right % left < left ∧ rank % right < right := by
  obtain ⟨_, rightPositive, pairFits, rightFits, pairRank, rightRank⟩ := product_bounds bits (functions * left) right rank fits valid
  obtain ⟨_, leftPositive, _, leftFits, functionRank, leftRank⟩ := product_bounds bits functions left (rank / right) pairFits pairRank
  refine ⟨?_, functionRank, leftRank, rightRank⟩
  rw [fusedRanks, quotRem_exact bits rank right (by omega) rightFits rightPositive]
  simp only [Int.toNat_natCast]
  rw [quotRem_exact bits (rank / right) left (by omega) leftFits leftPositive]

/-- The fused machine coordinates preserve the complete applicative decoder value. -/
theorem fused_decode (bits : Nat) (functions : Decoder.Plan (α → β → γ))
    (left : Decoder.Plan α) (right : Decoder.Plan β) (rank : Nat)
    (fits : Decoder.count functions * Decoder.count left * Decoder.count right ≤ maximum bits)
    (valid : rank < Decoder.count functions * Decoder.count left * Decoder.count right) :
    let coordinates := fusedRanks bits (Decoder.count left) (Decoder.count right) rank
    (Decoder.decode functions coordinates.1.toNat).bind (fun operation =>
      (Decoder.decode left coordinates.2.1.toNat).bind (fun first =>
        (Decoder.decode right coordinates.2.2.toNat).map (operation first))) =
      Decoder.decode (.ap (.ap functions left) right) rank := by
  dsimp only
  rw [(fusedRanks_exact bits _ _ _ rank fits valid).1]
  simp only [Int.toNat_natCast]
  exact (Decoder.decode_binary_fusion functions left right rank valid).symm

/-- The single-function fused branch needs only the outer signed quotRem operation. -/
theorem fused_single_function_decode (bits : Nat) (functions : Decoder.Plan (α → β → γ))
    (left : Decoder.Plan α) (right : Decoder.Plan β) (rank : Nat)
    (single : Decoder.count functions = 1)
    (fits : Decoder.count left * Decoder.count right ≤ maximum bits)
    (valid : rank < Decoder.count left * Decoder.count right) :
    let coordinates := quotRem bits (cast bits rank) (cast bits (Decoder.count right))
    (Decoder.decode functions 0).bind (fun operation =>
      (Decoder.decode left coordinates.1.toNat).bind (fun first =>
        (Decoder.decode right coordinates.2.toNat).map (operation first))) =
      Decoder.decode (.ap (.ap functions left) right) rank := by
  dsimp only
  rw [(selected_product bits (Decoder.count left) (Decoder.count right) rank fits valid).1]
  simp only [Int.toNat_natCast]
  exact (Decoder.decode_binary_single_function functions left right single rank valid).symm

end MicroCFTA.DecoderMachineBounds
