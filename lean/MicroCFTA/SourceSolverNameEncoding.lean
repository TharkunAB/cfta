import Std.Data.String.ToNat
import Init.Data.List.SplitOn.Lemmas
import Init.Data.String.Lemmas.Intercalate

/-!
# Historical decimal Unicode names for the Liquid Fixpoint adapter

Each Unicode scalar becomes its decimal code point and an underscore.
A fixed ASCII prefix supplies a safe alphabetic first character.
The proof splits the suffix at actual underscores and recovers every scalar.
The current two-form adapter is in SourceSolverNameFastEncoding.
-/
namespace MicroCFTA.SourceSolverNameEncoding

/-- The reserved adapter namespace starts with an ASCII letter. -/
def namePrefix : String := "microcfta_name_"

/-- One source Unicode scalar becomes its unsigned decimal code point. -/
def digits (character : Char) : List Char := (Nat.repr character.toNat).toList

/-- Append one underscore after every code point, including the final one. -/
def body : List Char → List Char
  | [] => []
  | character :: rest => digits character ++ '_' :: body rest

/-- The former nameSymbol payload before Fixpoint.symbol processes it. -/
def encode (name : String) : String := namePrefix ++ String.ofList (body name.toList)

/-- The list worker is the source concatMap of decimal tokens and separators. -/
theorem body_concatMap (characters : List Char) :
    body characters = characters.flatMap (fun character => (Nat.repr character.toNat).toList ++ ['_']) := by
  induction characters with
  | nil => rfl
  | cons character rest ih => simp [body, digits, ih]

/-- The historical encoder has the exact decimal-token concatenation used by the former nameSymbol. -/
theorem encode_source (name : String) :
    encode name = namePrefix ++ String.join (name.toList.map (fun character => Nat.repr character.toNat ++ "_")) := by
  unfold encode
  congr 1
  apply String.toList_injective
  simp [String.toList_join, List.flatMap_map, body_concatMap]

/-- Decimal code-point text contains only ASCII decimal digits. -/
theorem digits_digit (character digit : Char) (present : digit ∈ digits character) : digit.isDigit = true := by
  apply Nat.isDigit_of_mem_toDigits (b := 10) (n := character.toNat) (by decide) (by decide)
  simpa [digits] using present

/-- The decimal representation cannot contain the separator. -/
theorem digits_no_separator (character digit : Char) (present : digit ∈ digits character) : (digit == '_') = false := by
  have decimal := digits_digit character digit present
  cases same : digit == '_' with
  | false => rfl
  | true =>
    have equal : digit = '_' := beq_iff_eq.mp same
    subst digit
    contradiction

/-- Splitting the complete suffix recovers one decimal token for each source scalar. -/
theorem split_body (characters : List Char) :
    (body characters).splitOnP (· == '_') = characters.map digits ++ [[]] := by
  induction characters with
  | nil => rfl
  | cons character rest ih =>
    rw [body, List.splitOnP_append_cons_of_forall_mem (digits_no_separator character) '_' (by decide), ih]
    rfl

/-- Decimal code points identify their original Unicode scalar. -/
theorem digits_injective {first second : Char} (same : digits first = digits second) : first = second := by
  apply Char.toNat_inj.mp
  apply Nat.repr_injective
  exact String.toList_injective same

/-- The separator keeps the concatenated decimal code-point sequence injective. -/
theorem body_injective {first second : List Char} (same : body first = body second) : first = second := by
  have tokens := congrArg (fun characters => characters.splitOnP (· == '_')) same
  rw [split_body, split_body] at tokens
  have mapped : first.map digits = second.map digits := List.append_cancel_right tokens
  exact (List.map_inj_right (fun _ _ equal => digits_injective equal)).mp mapped

/-- Distinct raw names always produce distinct safe solver names. -/
theorem encode_injective {first second : String} (same : encode first = encode second) : first = second := by
  apply String.toList_injective
  apply body_injective
  have suffix := (String.append_right_inj namePrefix).mp same
  simpa using congrArg String.toList suffix

/-- The encoded suffix uses only decimal digits and underscores. -/
theorem body_safe (characters : List Char) (character : Char) (present : character ∈ body characters) :
    character.isDigit = true ∨ character = '_' := by
  induction characters with
  | nil => simp [body] at present
  | cons first rest ih =>
    rcases List.mem_append.mp present with digit | tail
    · exact Or.inl (digits_digit first character digit)
    · rcases List.mem_cons.mp tail with equal | tail
      · exact Or.inr equal
      · exact ih tail

end MicroCFTA.SourceSolverNameEncoding
