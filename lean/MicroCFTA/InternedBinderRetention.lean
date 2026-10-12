import MicroCFTA.InternedHeadReference

/-!
# Retention through current source binder normalization

Bare self-reference removal cannot remove an actual Mu operand. Smart
binder cleanup cannot erase a body that retains an actual Mu. When a root
union retains both an outer binder and a deeper binder containing it, the
source identity normalizer cannot return a singleton after the root filter.
-/
namespace MicroCFTA.InternedBinderRetention
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedUnionSeparation InternedUnionRetention
open InternedBinderProtocol (Reference NodeKey)

/-- A bare reference has no stored recursive-node descendant. -/
theorem no_mu_under_reference (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (name : Reference) : ¬Retains (.mu entry body depth ordinary) (.reference name) := by
  intro retained
  cases retained with
  | step member _ => simp [semanticChildren] at member

/-- Source cleanup retains every actual Mu already present in its body. -/
theorem cleanup_retains_mu (outer : Interned NodeKey) (outerBody outerDepth outerOrdinary : Value Symbol Guard)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (retained : Retains (.mu outer outerBody outerDepth outerOrdinary) body) :
    Retains (.mu outer outerBody outerDepth outerOrdinary) (cleanup (.mu entry body depth ordinary)) := by
  simp only [cleanup]
  split
  · exact retained
  · split
    · rename_i bare
      have same := (referenceOf_self_iff (.interned entry.identity) body).mp bare
      exact False.elim (no_mu_under_reference outer outerBody outerDepth outerOrdinary _ (same ▸ retained))
    · exact .step (by simp [semanticChildren]) retained

/-- A root Mu operand survives the current self-reference filter and its
source union reconstruction, including a resulting singleton. -/
theorem filter_retains_mu [DecidableEq (EdgeKey Symbol Guard)]
    (state : State Symbol Guard) (coherent : Coherent state) (cached : Cached state)
    (name : Reference) (unionEntry : Interned NodeKey) (members : List (Value Symbol Guard))
    (unionDepth : Nat) (unionFree : List Reference)
    (available : Available state (.union unionEntry members unionDepth unionFree))
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (member : Value.mu entry body depth ordinary ∈ members) :
    Retains (.mu entry body depth ordinary)
      (run (withoutSelfReference name (.union unionEntry members unionDepth unionFree)) state).1 := by
  simp only [withoutSelfReference]
  split
  · apply makeUnion_retains_mu state coherent cached _
      (fun value included => available.children value (List.mem_filter.mp included).1) entry body depth ordinary
    apply List.mem_flatMap.mpr
    refine ⟨.mu entry body depth ordinary, ?_, by simp [unionMembers]⟩
    exact (withoutSelfReference_members name members _).mpr ⟨member, by simp⟩
  · exact .step (by simpa only [run, semanticChildren] using member) .here

/-- Root self-reference removal cannot collapse a union of an outer Mu and
a rebuilt Mu that retains it. The distinct identities follow from source
cached depths and actual resident payloads. -/
theorem filter_separated_rank [DecidableEq (EdgeKey Symbol Guard)]
    (state : State Symbol Guard) (coherent : Coherent state)
    (name : Reference) (unionEntry : Interned NodeKey) (members : List (Value Symbol Guard))
    (unionDepth : Nat) (unionFree : List Reference)
    (available : Available state (.union unionEntry members unionDepth unionFree))
    (outerEntry : Interned NodeKey) (outerBody outerDepth outerOrdinary : Value Symbol Guard)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (left : Value.mu outerEntry outerBody outerDepth outerOrdinary ∈ members)
    (right : Value.mu entry body depth ordinary ∈ members)
    (retained : Retains (.mu outerEntry outerBody outerDepth outerOrdinary) body) :
    InternedGateRank.headRank
      (run (withoutSelfReference name (.union unionEntry members unionDepth unionFree)) state).1 = 0 := by
  simp only [withoutSelfReference]
  split
  · apply retained_union_rank state coherent _ (.mu outerEntry outerBody outerDepth outerOrdinary)
      entry body depth ordinary (available.children _ left) (available.children _ right) retained
    · apply List.mem_flatMap.mpr
      refine ⟨.mu outerEntry outerBody outerDepth outerOrdinary, ?_, by simp [unionMembers]⟩
      exact (withoutSelfReference_members name members _).mpr ⟨left, by simp⟩
    · apply List.mem_flatMap.mpr
      refine ⟨.mu entry body depth ordinary, ?_, by simp [unionMembers]⟩
      exact (withoutSelfReference_members name members _).mpr ⟨right, by simp⟩
  · rfl

end MicroCFTA.InternedBinderRetention
