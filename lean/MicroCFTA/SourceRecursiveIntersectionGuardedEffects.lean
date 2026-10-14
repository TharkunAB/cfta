import MicroCFTA.SourceRecursiveIntersectionSemanticHeap
import MicroCFTA.InternedGuardedStoredExecution

/-!
# Independent guarded meaning of actual intersection binders

The source optional binder denotes the least language of its body at the
actual repeated-pair reference. The unused branch has the same language.
Both branches retain the independently derived probe-language heap.
-/
namespace MicroCFTA.SourceRecursiveIntersectionGuardedEffects
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedStoredSubstitution (leaves encode leaves_available)
open InternedGuardedLanguage
open InternedGuardedStoredPlan (resolve resolve_cons resolve_nil encode_language)
open InternedGuardedRequest (Checked done_checked)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open InternedBinderProtocol (Reference)

/-- Actual optional binders have their independent least language and retain the semantic probe heap. -/
theorem optionalBinder_checked [DecidableEq (EdgeKey Symbol Guard)] (pair : Nat × Nat) (body : Value Symbol Guard)
    (state : State Symbol Guard) (semantic : SemanticHeap state) (heap : InternedGuardedProbeHeap.Heap state)
    (available : Available state body) :
    Checked (SourceRecursiveIntersectionMaybeMu.maybeMu pair body state) (fun value => ∀ holds ambient,
      meaning holds ambient value = BinderLanguage.least (fun candidate =>
        meaning holds (bind ambient (.intersection pair.1 pair.2) candidate) body)) := by
  let name := Reference.intersection pair.1 pair.2
  have context := SourceRecursiveIntersectionSemanticHeap.context state semantic (leaves body)
    (leaves_available body state available)
  rw [SourceRecursiveIntersectionMaybeMu.maybeMu_eq pair body state state semantic.1.normal.facts available]
  split
  · have built := InternedGuardedExecution.build_language (.binder true (encode (leaves body) [name] body))
      (leaves body) state context heap
    refine ⟨built.heap, ?_⟩
    intro value after done holds ambient
    have observed := built.result value after done holds ambient
    rw [InternedGuardedSyntax.evaluate] at observed
    apply observed.trans
    apply BinderLanguage.least_congr
    intro candidate term
    apply iff_of_eq
    apply congrFun
    have compiled := encode_language holds (leaves body) [name] [candidate] ambient body state semantic.1.normal.facts.coherent
      (leaves_available body state available) available (fun _ member => member) rfl
    simpa only [List.singleton_append, resolve_cons, resolve_nil] using compiled
  · rename_i unused
    apply done_checked _ _ _ heap
    intro holds ambient
    apply Eq.symm
    apply Eq.trans (b := BinderLanguage.least (fun _ => meaning holds ambient body))
    · apply BinderLanguage.least_congr
      intro candidate term
      apply iff_of_eq
      apply congrFun
      apply meaning_free holds body state semantic.1.normal.facts.coherent available
      intro other member
      have different : other ≠ .intersection pair.1 pair.2 := fun same => unused (same ▸ member)
      simp only [InternedGuardedLanguage.bind, different, ↓reduceIte]
    · exact BinderLanguage.least_constant _

/-- Actual optional binders preserve the independent probe-language invariant at every outcome. -/
theorem optionalBinder [DecidableEq (EdgeKey Symbol Guard)] (pair : Nat × Nat) (body : Value Symbol Guard)
    (state : State Symbol Guard) (semantic : SemanticHeap state) (heap : InternedGuardedProbeHeap.Heap state)
    (available : Available state body) :
    InternedGuardedProbeHeap.Heap (SourceRecursiveIntersectionMaybeMu.maybeMu pair body state).state :=
  (optionalBinder_checked pair body state semantic heap available).heap

end MicroCFTA.SourceRecursiveIntersectionGuardedEffects
