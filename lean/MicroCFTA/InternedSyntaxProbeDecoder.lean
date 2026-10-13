import MicroCFTA.InternedProfileEquivalence

/-!
# The complete syntax model has a probe-determined smart result

The proof derives the callback form from the original syntax. The two
normalized pure probe profiles determine the smart binder profile for
arbitrary nesting and arbitrary captured profiles.
-/
namespace MicroCFTA.InternedSyntaxProbeDecoder
open InternedNestedConstruction InternedProfileSemantics InternedProfileCallbackForm
open InternedRootProfile InternedProbeDecoder InternedProfileEquivalence
open InternedBinderProtocol (Reference)

/-- Two distinct normalized probes determine the complete pure smart-binder interpretation. -/
theorem evaluate_decoded (body : Syntax Symbol Guard) (environment : List Profile)
    (first second : Reference) (different : first ≠ second) :
    Equivalent
      (decode first second (normalize first (evaluate body (some [first] :: environment)))
        (normalize second (evaluate body (some [second] :: environment))))
      (evaluate (.binder true body) environment) := by
  cases computed : symbolic body environment with
  | none =>
      have left := opaque_form body environment computed first
      have right := opaque_form body environment computed second
      rw [left, right]
      have result : evaluate (.binder true body) environment = none := by
        rw [evaluate]
        change lower (symbolic body environment) = none
        rw [computed]
        rfl
      rw [result]
      exact refl _
  | some names =>
      have left := normalize_same first (pure_form body environment names computed first)
      have right := normalize_same second (pure_form body environment names computed second)
      have decoded := trans (decode_same first second left right)
        (decode_probes (captures names) (usesArgument names) first second different)
      have result : evaluate (.binder true body) environment = some (captures names) := by
        rw [evaluate]
        change lower (symbolic body environment) = some (captures names)
        rw [computed]
        simp only [lower, captures]
        congr 1
        apply congrArg (fun function => names.filterMap function)
        funext name
        cases name <;> rfl
      rw [result]
      exact decoded

/-- The exact source depth and ordinary sentinel names meet the decoder's distinctness condition. -/
theorem source_evaluate_decoded (body : Syntax Symbol Guard) (environment : List Profile) (level : Nat) :
    Equivalent
      (decode .depth (.uninterned level) (normalize .depth (evaluate body (some [.depth] :: environment)))
        (normalize (.uninterned level) (evaluate body (some [.uninterned level] :: environment))))
      (evaluate (.binder true body) environment) :=
  evaluate_decoded body environment .depth (.uninterned level) (by simp)

end MicroCFTA.InternedSyntaxProbeDecoder
