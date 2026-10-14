import MicroCFTA.SourceSolverNameEncodingFixpoint

/-!
# The current two-form solver name encoding

ASCII letters, digits, and underscores keep their text after m_.
Other names use decimal Unicode tokens after mx. The two prefix tags
are disjoint. The existing decimal-token and Fixpoint serializer proofs
remain as the historical codec and reusable character-level results.
-/
namespace MicroCFTA.SourceSolverNameFastEncoding
open SourceSolverNameEncoding (digits body body_concatMap body_injective body_safe alpha safe
  keywords serializer prefixAlpha escape pad escape_safe)

/-- The source ASCII guard admits only alphanumeric characters and underscore. -/
def plain (character : Char) : Bool :=
  (decide (character.toNat < 128) && (alpha character || character.isDigit)) || character == '_'

/-- The current nameSymbol keeps plain names and encodes every other Unicode scalar. -/
def encode (name : String) : String :=
  if name.toList.all plain then "m_" ++ name else "mx" ++ String.ofList (body name.toList)

/-- The fallback is exactly the source concatMap of decimal code points and underscores. -/
theorem encode_source (name : String) :
    encode name = if name.toList.all plain then "m_" ++ name
      else "mx" ++ String.join (name.toList.map (fun character => Nat.repr character.toNat ++ "_")) := by
  unfold encode
  split
  · rfl
  · congr 1
    apply String.toList_injective
    simp [String.toList_join, List.flatMap_map, body_concatMap]

/-- Every name accepted by the plain branch is already safe for Fixpoint. -/
theorem plain_safe (character : Char) (found : plain character = true) : safe character = true := by
  simp only [plain, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at found
  rcases found with ⟨_, letter | digit⟩ | underscore
  · simp [safe, letter]
  · simp [safe, digit]
  · subst character; decide

/-- The two disjoint prefix tags retain injectivity for both complete source branches. -/
theorem encode_injective {first second : String} (same : encode first = encode second) : first = second := by
  by_cases left : first.toList.all plain = true
  · by_cases right : second.toList.all plain = true
    · simpa only [encode, left, right, ↓reduceIte, String.append_right_inj] using same
    · have chars := congrArg String.toList same
      simp [encode, left, right, String.toList_append] at chars
  · by_cases right : second.toList.all plain = true
    · have chars := congrArg String.toList same
      simp [encode, left, right, String.toList_append] at chars
    · have suffix : String.ofList (body first.toList) = String.ofList (body second.toList) := by
        simpa only [encode, left, right, Bool.false_eq_true, ↓reduceIte, String.append_right_inj] using same
      exact String.toList_injective (body_injective (by simpa using congrArg String.toList suffix))

/-- Every encoded name begins with exactly one of the two source prefix tags. -/
theorem encode_tag (name : String) :
    (encode name).toList.take 2 = ['m', '_'] ∨ (encode name).toList.take 2 = ['m', 'x'] := by
  unfold encode
  split <;> simp [String.toList_append]

/-- Every encoded character belongs to the unchanged Fixpoint safe ASCII alphabet. -/
theorem encode_safe (name : String) (character : Char) (present : character ∈ (encode name).toList) :
    safe character = true := by
  by_cases simple : name.toList.all plain = true
  · simp only [encode, simple, ↓reduceIte, String.toList_append] at present
    rcases List.mem_append.mp present with header | suffix
    · exact List.all_eq_true.mp (show "m_".toList.all safe = true from by decide) character header
    · exact plain_safe character (List.all_eq_true.mp simple character suffix)
  · simp only [encode, simple, Bool.false_eq_true, ↓reduceIte, String.toList_append, String.toList_ofList] at present
    rcases List.mem_append.mp present with header | suffix
    · exact List.all_eq_true.mp (show "mx".toList.all safe = true from by decide) character header
    · rcases body_safe name.toList character suffix with decimal | separator
      · simp [safe, decimal]
      · subst character; decide

/-- Neither actual prefix tag occurs at the start of a Fixpoint keyword. -/
theorem keyword_tags (name : String) (present : name ∈ keywords) :
    name.toList.take 2 ≠ ['m', '_'] ∧ name.toList.take 2 ≠ ['m', 'x'] := by
  exact of_decide_eq_true (List.all_eq_true.mp
    (show keywords.all (fun keyword => decide
      (keyword.toList.take 2 ≠ ['m', '_'] ∧ keyword.toList.take 2 ≠ ['m', 'x'])) = true from by decide)
    name present)

/-- No encoded name takes the source serializer's keyword branch. -/
theorem encode_not_keyword (name : String) : keywords.contains (encode name) = false := by
  cases found : keywords.contains (encode name) with
  | false => rfl
  | true =>
    have member : encode name ∈ keywords := by simpa using found
    have excluded := keyword_tags (encode name) member
    rcases encode_tag name with first | second
    · exact False.elim (excluded.1 first)
    · exact False.elim (excluded.2 second)

/-- Both source branches start with the fixed ASCII letter m. -/
theorem encode_alpha (name : String) : ((encode name).toList.head?.any alpha) = true := by
  unfold encode
  split <;> simp [String.toList_append, alpha]

/-- Current encoded names pass through every actual serializer control branch unchanged. -/
theorem serializer_encode (name : String) : serializer (encode name) = encode name := by
  rw [serializer, encode_not_keyword]
  simp only [Bool.false_eq_true, ↓reduceIte, prefixAlpha, encode_alpha, ↓reduceIte]
  rw [escape_safe _ (encode_safe name)]
  have unchanged : pad (encode name).toList = (encode name).toList := by
    unfold encode
    split <;> simp [String.toList_append, pad]
  rw [unchanged, String.ofList_toList]

/-- The complete current raw-name to serialized-name path is injective. -/
theorem serialized_injective {first second : String}
    (same : serializer (encode first) = serializer (encode second)) : first = second := by
  rw [serializer_encode, serializer_encode] at same
  exact encode_injective same

/-- Plain numeric names use the short branch even though raw Fixpoint encoding would prefix them. -/
theorem numeric_name : encode "1" = "m_1" := by decide +kernel

/-- The former colliding spelling takes the decimal fallback and remains distinct. -/
theorem historical_separated : serializer (encode "1") ≠ serializer (encode "fix$1") := by
  intro same
  have impossible := serialized_injective same
  contradiction

end MicroCFTA.SourceSolverNameFastEncoding
