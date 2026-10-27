import MicroCFTA.SourcePruningEnumerationPendingWriteLanguage
import MicroCFTA.SourcePruningEnumerationAssimilationLanguage
import MicroCFTA.SourcePruningEnumerationNativeLanguage
import MicroCFTA.EnumerationFrame

/-!
# Assignment semantics with one protected pending payload removed

These lemmas use the actual stored values and actual update equations.
They do not run an action on a modified enumeration state.
The native heaps, language predicates and assignments remain unchanged.
-/
namespace MicroCFTA.SourcePruningEnumerationNeutralLanguage
open Language Fragments EnumerationState EnumerationCorrectness EnumerationFrame
open EnumerationCompressionFrame

section Pure
variable {Symbol EnumGuard : Type}

/-- A complete read frame remains a frame after removal of one payload. -/
theorem neutralize_frame
    (held : Nat) (before after : State Symbol EnumGuard) (frame : Frame before after) :
    Frame (neutralize held before) (neutralize held after) := by
  refine ⟨frame.counter, ?_, frame.obligations, frame.recursionAncestry,
    frame.expansionAncestry, frame.reaches⟩
  change after.values.set held (.unenumerated none []) = before.values.set held (.unenumerated none [])
  rw [frame.values]

/-- A complete read frame preserves assignments with the same payload removed. -/
theorem satisfies_neutral_frame
    (language : NodeLanguage Symbol) (meaning : EnumGuard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (held : Nat)
    (before after : State Symbol EnumGuard) (frame : Frame before after) :
    Satisfies language meaning assignment (neutralize held after) ↔
      Satisfies language meaning assignment (neutralize held before) := by
  have classes (left right : Nat) :
      UnionFind.SameClass after.representatives left right ↔
        UnionFind.SameClass before.representatives left right := by
    constructor
    · rintro ⟨root, size, leftPath, rightPath⟩
      exact ⟨root, size, (frame.reaches left root size).mp leftPath,
        (frame.reaches right root size).mp rightPath⟩
    · rintro ⟨root, size, leftPath, rightPath⟩
      exact ⟨root, size, (frame.reaches left root size).mpr leftPath,
        (frame.reaches right root size).mpr rightPath⟩
  have forestSame : UnionFind.Satisfies after.representatives assignment ↔
      UnionFind.Satisfies before.representatives assignment := by
    constructor
    · intro satisfied left right related
      exact satisfied left right ((classes left right).mpr related)
    · intro satisfied left right related
      exact satisfied left right ((classes left right).mp related)
  simp only [neutralize, Satisfies, Fragments.stateSatisfies, frame.values, frame.obligations, forestSame]

/-- An unrelated pending write adds its exact domain and bucket after payload removal. -/
theorem pending_write_neutral
    (language : NodeLanguage Symbol) (meaning : EnumGuard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (before after : State Symbol EnumGuard)
    (held uv newHandle : Nat) (oldNode : Option Nat) (oldScs incomingScs : List Suspended)
    (incomingDomain : Term Symbol → Prop)
    (stored : before.values[uv]? = some (.unenumerated oldNode oldScs))
    (different : uv ≠ held)
    (representatives : after.representatives = before.representatives)
    (values : after.values = before.values.set uv (.unenumerated (some newHandle) (incomingScs ++ oldScs)))
    (obligations : after.obligations = before.obligations)
    (replacement : ∀ term, language newHandle term ↔
      incomingDomain term ∧ permits (oldNode.map language) term) :
    Satisfies language meaning assignment (neutralize held after) ↔
      Satisfies language meaning assignment (neutralize held before) ∧ incomingDomain (assignment uv) ∧
        ∀ sc ∈ incomingScs, Suspended.Holds assignment (assignment uv) sc := by
  have oldStored : (neutralize held before).values[uv]? = some (.unenumerated oldNode oldScs) := by
    rw [neutralize_read held uv before different]
    exact stored
  have write : (neutralize held after).values =
      (neutralize held before).values.set uv (.unenumerated (some newHandle) (incomingScs ++ oldScs)) := by
    change after.values.set held (.unenumerated none []) =
      (before.values.set held (.unenumerated none [])).set uv _
    rw [values]
    exact congrArg (fun state : State Symbol EnumGuard => state.values)
      (neutralize_set held uv before (.unenumerated (some newHandle) (incomingScs ++ oldScs)) different)
  exact SourcePruningEnumerationPendingWriteLanguage.pending_write language meaning assignment
    (neutralize held before) (neutralize held after) uv newHandle oldNode oldScs incomingScs incomingDomain
    oldStored representatives write obligations replacement

/-- Actual assimilation commutes with removal of a different source and target payload. -/
theorem neutralize_assimilated
    (held source target : Nat) (before : State Symbol EnumGuard) (merged : UVarValue Symbol)
    (sourceOther : source ≠ held) (targetOther : target ≠ held) :
    neutralize held (assimilated before target source merged) =
      assimilated (neutralize held before) target source merged := by
  unfold neutralize assimilated
  congr 1
  dsimp only
  rw [List.set_comm (UVarValue.eliminated : UVarValue Symbol) (.unenumerated none []) sourceOther,
    List.set_comm merged (.unenumerated none []) targetOther]

/-- An actual distinct-slot assimilation preserves assignments with a separate payload removed. -/
theorem assimilated_neutral
    (language : NodeLanguage Symbol) (meaning : EnumGuard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (before : State Symbol EnumGuard)
    (held source target : Nat) (sourceNode targetNode merged : Option Nat)
    (sourceScs targetScs : List Suspended)
    (sourceStored : before.values[source]? = some (.unenumerated sourceNode sourceScs))
    (targetStored : before.values[target]? = some (.unenumerated targetNode targetScs))
    (different : source ≠ target)
    (sourceOther : source ≠ held) (targetOther : target ≠ held)
    (sameClass : UnionFind.SameClass before.representatives source target)
    (replacement : ∀ term, permits (merged.map language) term ↔
      permits (sourceNode.map language) term ∧ permits (targetNode.map language) term) :
    Satisfies language meaning assignment
      (neutralize held (assimilated before target source (.unenumerated merged (sourceScs ++ targetScs)))) ↔
      Satisfies language meaning assignment (neutralize held before) := by
  rw [neutralize_assimilated held source target before _ sourceOther targetOther]
  apply SourcePruningEnumerationAssimilationLanguage.assimilated_semantics language meaning assignment
    (neutralize held before) source target sourceNode targetNode merged sourceScs targetScs
  · rw [neutralize_read held source before sourceOther]
    exact sourceStored
  · rw [neutralize_read held target before targetOther]
    exact targetStored
  · exact different
  · exact sameClass
  · exact replacement

end Pure

section Native
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- Removing a pending payload retains every actual native handle readback needed by other slots. -/
theorem neutralize_realized
    (held : Nat) (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (state : State Symbol EnumGuard)
    (realized : SourcePruningEnumerationObservation.PendingRealized heap state) :
    SourcePruningEnumerationObservation.PendingRealized heap (neutralize held state) := by
  intro uv node scs stored
  by_cases same : uv = held
  · subst uv
    by_cases inside : held < state.values.length
    · simp [neutralize, List.getElem?_set, inside] at stored
    · simp [neutralize, List.getElem?_set, inside] at stored
  · apply realized uv node scs
    rwa [neutralize_read held uv state same] at stored

/-- Actual native heap growth preserves assignments with one pending payload removed. -/
theorem satisfies_neutral_keeps
    (holds : NativeGuard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (beforeHeap afterHeap : InternedConstructorTemplates.State Symbol NativeGuard)
    (state : State Symbol EnumGuard) (held : Nat)
    (meaning : EnumGuard → Term Symbol → Prop) (assignment : Nat → Term Symbol)
    (realized : SourcePruningEnumerationObservation.PendingRealized beforeHeap state)
    (kept : SourceEqualityRequiredCache.Keeps beforeHeap afterHeap) :
    Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient afterHeap)
        meaning assignment (neutralize held state) ↔
      Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient beforeHeap)
        meaning assignment (neutralize held state) :=
  SourcePruningEnumerationNativeLanguage.satisfies_keeps holds ambient beforeHeap afterHeap
    (neutralize held state) meaning assignment (neutralize_realized held beforeHeap state realized) kept

/-- An actual native heap growth and complete read frame preserve the neutral assignment language. -/
theorem satisfies_neutral_keeps_frame
    (holds : NativeGuard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (beforeHeap afterHeap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before after : State Symbol EnumGuard) (held : Nat)
    (meaning : EnumGuard → Term Symbol → Prop) (assignment : Nat → Term Symbol)
    (realized : SourcePruningEnumerationObservation.PendingRealized beforeHeap before)
    (frame : Frame before after)
    (kept : SourceEqualityRequiredCache.Keeps beforeHeap afterHeap) :
    Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient afterHeap)
        meaning assignment (neutralize held after) ↔
      Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient beforeHeap)
        meaning assignment (neutralize held before) :=
  (satisfies_neutral_frame (SourcePruningEnumerationNativeLanguage.handles holds ambient afterHeap)
    meaning assignment held before after frame).trans
    (satisfies_neutral_keeps holds ambient beforeHeap afterHeap before held meaning assignment realized kept)

end Native
end MicroCFTA.SourcePruningEnumerationNeutralLanguage
