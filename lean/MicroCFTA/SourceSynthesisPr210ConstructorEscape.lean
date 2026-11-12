import MicroCFTA.SourceSynthesisGeneralizeSyntax

/-!
# Constructor names in the PR 210 candidate encoding

This rule follows candidate head 79f74df2c3c9d3c864e57a960cb64c8c28883ec9.
The PR is open and unmerged at the recorded source snapshot.
These laws concern constructor names and a proof-only inverse.
They do not change the historical source encoders.
-/
namespace MicroCFTA.SourceSynthesisPr210ConstructorEscape
open SourceSynthesisTypeSyntax (variableSymbol)
open SourceSynthesisGeneralizeSyntax (isVariableSymbol variableSymbol_recognized)

/-- Prefix each name reserved by the candidate constructor encoding. -/
def escapeConstructor (name : String) : String :=
  if ((decide (name ∈ ["var1", "var2", "var3", "var4", "->", "(->)"]) ||
      name.startsWith "var_") || name.startsWith "con:") then
    "con:" ++ name
  else name

/-- Remove one candidate escape prefix for the name roundtrip proof. -/
def decodeConstructor (name : String) : String :=
  if name.startsWith "con:" then String.ofList (name.toList.drop 4) else name

private theorem prefixed_ne (name tag : String)
    (different : tag.toList.head? ≠ some 'c') : "con:" ++ name ≠ tag := by
  intro same
  have first := congrArg (fun value : String => value.toList.head?) same
  rw [String.toList_append] at first
  change some 'c' = tag.toList.head? at first
  exact different first.symm

private theorem prefixed_separate (name : String) :
    isVariableSymbol ("con:" ++ name) = false ∧
      "con:" ++ name ≠ "->" ∧ "con:" ++ name ≠ "(->)" := by
  have noPrefix : ("con:" ++ name).startsWith "var_" = false := by
    apply String.startsWith_string_eq_false_iff.mpr
    rw [String.toList_append]
    change ¬ (['v', 'a', 'r', '_'] <+: ['c', 'o', 'n', ':'] ++ name.toList)
    rintro ⟨rest, same⟩
    have first := congrArg (fun values : List Char => values.head?) same
    change (some 'v' : Option Char) = some 'c' at first
    exact (by decide : (some 'v' : Option Char) ≠ some 'c') first
  have one := prefixed_ne name "var1" (by decide)
  have two := prefixed_ne name "var2" (by decide)
  have three := prefixed_ne name "var3" (by decide)
  have four := prefixed_ne name "var4" (by decide)
  refine ⟨?_, prefixed_ne name "->" (by decide), prefixed_ne name "(->)" (by decide)⟩
  simp [isVariableSymbol, noPrefix, one, two, three, four]

/-- Decoding recovers every raw constructor name from its candidate symbol. -/
theorem decode_escapeConstructor (name : String) :
    decodeConstructor (escapeConstructor name) = name := by
  unfold escapeConstructor
  split
  · have prefixed : ("con:" ++ name).startsWith "con:" = true := by
      apply String.startsWith_string_iff.mpr
      exact ⟨name.toList, by simp⟩
    simp only [decodeConstructor, prefixed, ↓reduceIte]
    rw [String.toList_append]
    change String.ofList name.toList = name
    exact String.ofList_toList
  · rename_i ordinary
    have noPrefix : name.startsWith "con:" = false := by
      apply Bool.eq_false_iff.mpr
      intro prefixed
      apply ordinary
      simp only [prefixed, Bool.or_true]
    simp [decodeConstructor, noPrefix]

/-- Distinct raw constructor names have distinct candidate symbols. -/
theorem escapeConstructor_injective : Function.Injective escapeConstructor := by
  intro first second same
  have decoded := congrArg decodeConstructor same
  simpa only [decode_escapeConstructor] using decoded

/-- Candidate constructor symbols are separate from variable and arrow tags. -/
theorem escapeConstructor_separate (name : String) :
    isVariableSymbol (escapeConstructor name) = false ∧
      escapeConstructor name ≠ "->" ∧ escapeConstructor name ≠ "(->)" := by
  unfold escapeConstructor
  split
  · exact prefixed_separate name
  · rename_i ordinary
    have allFalse := Bool.eq_false_iff.mpr ordinary
    obtain ⟨baseFalse, _constructorPrefix⟩ := Bool.or_eq_false_iff.mp allFalse
    obtain ⟨membersFalse, variablePrefix⟩ := Bool.or_eq_false_iff.mp baseFalse
    have noReserved : name ∉ ["var1", "var2", "var3", "var4", "->", "(->)"] :=
      of_decide_eq_false membersFalse
    have separated : name ≠ "var1" ∧ name ≠ "var2" ∧ name ≠ "var3" ∧
        name ≠ "var4" ∧ name ≠ "->" ∧ name ≠ "(->)" := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false, not_or] using noReserved
    obtain ⟨one, two, three, four, arrow, marker⟩ := separated
    refine ⟨?_, arrow, marker⟩
    simp [isVariableSymbol, variablePrefix, one, two, three, four]

/-- No candidate constructor symbol is the symbol of any actual raw variable. -/
theorem escapeConstructor_not_variableSymbol (name rawName : String) :
    escapeConstructor name ≠ variableSymbol rawName := by
  intro same
  have separated := (escapeConstructor_separate name).1
  rw [same, variableSymbol_recognized] at separated
  cases separated

end MicroCFTA.SourceSynthesisPr210ConstructorEscape
