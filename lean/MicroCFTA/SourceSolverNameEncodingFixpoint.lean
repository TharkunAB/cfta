import MicroCFTA.SourceSolverNameEncoding

/-!
# Fixpoint serialization of the decimal namespace

This model copies Names.encode, prefixAlpha, encodeUnsafe, and its pad step.
The ASCII character sets and keyword list come from the inspected library.
The proof concerns this source model. It does not verify the external
Haskell HashSet, Text, Array, symbol interning, or SMT process implementations.
-/
namespace MicroCFTA.SourceSolverNameEncoding

/-- Fixpoint alphaChars contains exactly the ASCII letters. -/
def alpha (character : Char) : Bool :=
  decide (65 ≤ character.toNat ∧ character.toNat ≤ 90) ||
    decide (97 ≤ character.toNat ∧ character.toNat ≤ 122)

/-- Fixpoint safeChars adds decimal digits, underscore, and period. -/
def safe (character : Char) : Bool :=
  alpha character || character.isDigit || character == '_' || character == '.'

/-- The actual Array lookup guard uses one plus the largest safe code point. -/
def isUnsafe (character : Char) : Bool := decide (123 ≤ character.toNat) || !safe character

/-- The exact reserved keywords in the inspected Fixpoint Names module. -/
def keywords : List String :=
  ["env", "id", "tag", "qualif", "constant", "cut", "bind", "constraint", "lhs", "rhs", "NaN", "min", "map"]

/-- Prefix an empty or nonalphabetic raw name as Fixpoint.prefixAlpha does. -/
def prefixAlpha (characters : List Char) : List Char :=
  if characters.head?.any alpha then characters else "fix$".toList ++ characters

/-- Escape each unsafe code point between two dollar characters. -/
def escape : List Char → List Char
  | [] => []
  | character :: rest =>
    if isUnsafe character then '$' :: digits character ++ '$' :: escape rest
    else character :: escape rest

/-- Retain the source pad branch for an escaped name that starts with a dollar. -/
def pad : List Char → List Char
  | '$' :: rest => 'z' :: '$' :: '$' :: rest
  | other => other

/-- The inspected Fixpoint Names.encode control flow. -/
def serializer (name : String) : String :=
  if keywords.contains name then "key$" ++ name
  else String.ofList (pad (escape (prefixAlpha name.toList)))

/-- Every safe code point is inside the actual safe-character array. -/
theorem safe_bound (character : Char) (found : safe character = true) : character.toNat < 123 := by
  simp only [safe, Bool.or_eq_true, alpha, decide_eq_true_eq, beq_iff_eq] at found
  rcases found with (((upper | lower) | digit) | equal) | equal
  · omega
  · omega
  · have bounds := Char.isDigit_iff_toNat.mp digit
    change 48 ≤ character.toNat ∧ character.toNat ≤ 57 at bounds
    omega
  · subst character; decide
  · subst character; decide

/-- Safe characters take the unescaped source branch. -/
theorem safe_not_unsafe (character : Char) (found : safe character = true) : isUnsafe character = false := by
  have bound := safe_bound character found
  simp [isUnsafe, found, show ¬123 ≤ character.toNat by omega]

/-- Every encoded character is in the source safe ASCII alphabet. -/
theorem encode_safe (name : String) (character : Char) (present : character ∈ (encode name).toList) :
    safe character = true := by
  simp only [encode, String.toList_append, String.toList_ofList] at present
  rcases List.mem_append.mp present with header | suffix
  · exact List.all_eq_true.mp (show namePrefix.toList.all safe = true from by decide) character header
  · rcases body_safe name.toList character suffix with decimal | separator
    · simp [safe, decimal]
    · subst character; decide

/-- The fixed namespace is longer than every source reserved keyword. -/
theorem keyword_short (name : String) (present : name ∈ keywords) : name.toList.length < namePrefix.toList.length := by
  exact of_decide_eq_true (List.all_eq_true.mp
    (show keywords.all (fun key => decide (key.toList.length < namePrefix.toList.length)) = true from by decide)
    name present)

/-- No encoded name takes Fixpoint's reserved-keyword branch. -/
theorem encode_not_keyword (name : String) : keywords.contains (encode name) = false := by
  cases found : keywords.contains (encode name) with
  | false => rfl
  | true =>
    have member : encode name ∈ keywords := by simpa using found
    have short := keyword_short (encode name) member
    simp only [encode, String.toList_append, String.toList_ofList, List.length_append] at short
    omega

/-- The fixed first ASCII letter prevents automatic fix$ prefixing. -/
theorem encode_alpha (name : String) : ((encode name).toList.head?.any alpha) = true := by
  simp [encode, namePrefix, String.toList_append, alpha]

/-- Escaping a safe character list preserves every character and its order. -/
theorem escape_safe (characters : List Char) (found : ∀ character ∈ characters, safe character = true) :
    escape characters = characters := by
  induction characters with
  | nil => rfl
  | cons character rest ih =>
    rw [escape, safe_not_unsafe character (found character (by simp))]
    simp only [Bool.false_eq_true, ↓reduceIte, List.cons.injEq, true_and]
    exact ih (fun character member => found character (List.mem_cons_of_mem _ member))

/-- The concrete decimal namespace passes through actual serializer control unchanged. -/
theorem serializer_encode (name : String) : serializer (encode name) = encode name := by
  rw [serializer, encode_not_keyword]
  simp only [Bool.false_eq_true, ↓reduceIte, prefixAlpha, encode_alpha, ↓reduceIte]
  rw [escape_safe _ (encode_safe name)]
  have unchanged : pad (encode name).toList = (encode name).toList := by
    simp [encode, namePrefix, String.toList_append, pad]
  rw [unchanged, String.ofList_toList]

/-- The entire raw-name to serialized-name path is injective. -/
theorem serialized_injective {first second : String}
    (same : serializer (encode first) = serializer (encode second)) : first = second := by
  rw [serializer_encode, serializer_encode] at same
  exact encode_injective same

/-- The old unsafe name serializes to the concrete spelling seen in the native query. -/
theorem historical_spelling : serializer "1" = "fix$36$1" := by decide +kernel

/-- The historical nonalphabetic-prefix collision is present in the exact serializer model. -/
theorem historical_collision : serializer "1" = serializer "fix$1" := by decide +kernel

/-- The repaired path separates the two names from the historical quantified-query defect. -/
theorem repaired_collision_separated : serializer (encode "1") ≠ serializer (encode "fix$1") := by
  intro same
  have impossible := serialized_injective same
  contradiction

end MicroCFTA.SourceSolverNameEncoding
