import MicroCFTA.InternedGuardedConstructors

/-!
# Actual root-self filtering preserves the independent Mu language

The callback normalizer removes only bare self alternatives at the root.
Its actual union reconstruction retains all other guarded alternatives.
Deleted alternatives contribute only the candidate recursive language, so
the normalized and original bodies have the same closed candidates.
-/
namespace MicroCFTA.InternedGuardedLanguage
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedNestedProvenance Language
open InternedBinderProtocol (Reference NodeKey)
open BinderLanguage (Included least)

/-- Actual root-self filtering has exactly the same closed candidate languages as its original body. -/
theorem filter_closed [DecidableEq (EdgeKey Symbol Guard)] (holds : Guard → Term Symbol → Bool) (environment : Env Symbol) (name : Reference)
    (body : Value Symbol Guard) (state : State Symbol Guard) (facts : Facts state) (available : Available state body)
    (candidate : BinderLanguage.Lang Symbol) :
    Included (meaning holds (bind environment name candidate) (run (withoutSelfReference name body) state).1) candidate ↔
      Included (meaning holds (bind environment name candidate) body) candidate := by
  cases body with
  | empty | reference | node | mu => rfl
  | union entry members depth free =>
      by_cases selected : members.any (fun member => member.referenceOf == .ref name) = true
      · simp only [withoutSelfReference, selected, ↓reduceIte]
        have inputs : Values state (members.filter (fun member => member.referenceOf != .ref name)) := by
          intro member present
          exact available.children member (List.mem_filter.mp present).1
        have normalized := makeUnion_exact state facts holds (bind environment name candidate) _ inputs
        constructor
        · intro closed term accepted
          obtain ⟨member, present, accepted⟩ := ((laws holds (bind environment name candidate)).union entry members depth free term).mp accepted
          by_cases same : member.referenceOf = .ref name
          · have literal := (referenceOf_self_iff name member).mp same
            subst member
            simpa only [meaning, bind, ↓reduceIte] using accepted
          · apply closed term
            apply (normalized term).mpr
            exact ⟨member, List.mem_filter.mpr ⟨present, by simpa using same⟩, accepted⟩
        · intro closed term accepted
          obtain ⟨member, present, accepted⟩ := (normalized term).mp accepted
          exact closed term (((laws holds (bind environment name candidate)).union entry members depth free term).mpr
            ⟨member, (List.mem_filter.mp present).1, accepted⟩)
      · simp only [withoutSelfReference, selected]
        exact Iff.rfl

/-- Actual callback filtering preserves the complete independent least language, including open bodies. -/
theorem filter_least [DecidableEq (EdgeKey Symbol Guard)] (holds : Guard → Term Symbol → Bool) (environment : Env Symbol) (name : Reference)
    (body : Value Symbol Guard) (state : State Symbol Guard) (facts : Facts state) (available : Available state body) :
    least (fun candidate => meaning holds (bind environment name candidate) (run (withoutSelfReference name body) state).1) =
      least (fun candidate => meaning holds (bind environment name candidate) body) := by
  funext term
  apply propext
  constructor
  · intro accepted candidate closed
    exact accepted candidate ((filter_closed holds environment name body state facts available candidate).mpr closed)
  · intro accepted candidate closed
    exact accepted candidate ((filter_closed holds environment name body state facts available candidate).mp closed)

/-- The actual normalized callback body and its original body give the same independent stored Mu language. -/
theorem filter_mu [DecidableEq (EdgeKey Symbol Guard)] (holds : Guard → Term Symbol → Bool) (environment : Env Symbol)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (available : Available state body) :
    meaning holds environment (.mu entry (run (withoutSelfReference (.interned entry.identity) body) state).1 depth ordinary) =
      meaning holds environment (.mu entry body depth ordinary) := by
  rw [meaning, meaning]
  exact filter_least holds environment (.interned entry.identity) body state facts available

end MicroCFTA.InternedGuardedLanguage
