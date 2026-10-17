import MicroCFTA.SourceCurrentNativeCallbackErasure
import MicroCFTA.SourceCurrentNativeStrippedFilter

/-!
# Pure erasure laws for normalized source callbacks

Bare-self erasure changes no deep names. It also changes no alternatives
after the selected reference has been stripped. Local normal form identifies
smart cleanup with this erasure when the local has no deep occurrence.
-/
namespace MicroCFTA.SourceCurrentNativeNormalizedErasure
open Cache InternedConstructorTemplates InternedDeepFreeDepth
open InternedNestedConstruction (finish)
open InternedRootAlternativeLists (remove)
open SourceCurrentNativeCallbackErasure (eraseSelf)
open SourceCurrentNativeStrippedAlternatives (stripMany)
open SourceCurrentNativeStrippedFilter (strip_remove)
open InternedBinderProtocol (Reference NodeKey)

/-- Erasing a selected bare reference does not change the final stripped alternatives. -/
theorem strip_eraseSelf (names : List Reference) (own : Reference)
    (value : Value Symbol Guard) (selected : own ∈ names) :
    stripMany names (unionMembers (eraseSelf own value)) = stripMany names (unionMembers value) := by
  unfold eraseSelf
  split
  · rename_i same
    have bare := (referenceOf_self_iff own value).mp same
    rw [bare]
    simpa [unionMembers, remove, Value.referenceOf] using strip_remove names own selected [.reference own]
  · rfl

/-- Local normal form makes unused smart cleanup equal literal bare-self erasure. -/
theorem finish_true_eq_erase (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (localNormal : InternedDeepLocalNormal.Local (.interned entry.identity) body)
    (unused : .interned entry.identity ∉ deepNames body) :
    finish true (.mu entry body depth ordinary) = eraseSelf (.interned entry.identity) body := by
  by_cases free : .interned entry.identity ∈ body.free
  · rcases localNormal free with impossible | bare
    · exact False.elim (unused impossible)
    · subst body
      simp [finish, cleanup, eraseSelf, Value.free, Value.referenceOf]
  · have nonbare : body.referenceOf ≠ .ref (.interned entry.identity) := by
      intro same
      have bare := (referenceOf_self_iff (.interned entry.identity) body).mp same
      simp [bare, Value.free] at free
    simp [finish, cleanup, free, eraseSelf, nonbare]

/-- Bare-self erasure preserves the exact ordered deep-name list. -/
theorem eraseSelf_deep (own : Reference) (value : Value Symbol Guard) :
    deepNames (eraseSelf own value) = deepNames value := by
  unfold eraseSelf
  split
  · rename_i same
    have bare := (referenceOf_self_iff own value).mp same
    simp [bare, deepNames]
  · rfl

end MicroCFTA.SourceCurrentNativeNormalizedErasure
