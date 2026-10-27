import MicroCFTA.SourcePruningOuterNarrow
import MicroCFTA.MergedFreshOrdinaryGuardedSoundness
import MicroCFTA.InternedGuardedConstructors

/-!
# Independent meaning of actual native narrowing

The actual reader supplies the filtered edges. The actual node constructor
preserves their meaning. Each accepted result term belongs to the input.
The independent probe-language heap is an explicit current-state premise.
This module does not assign meaning to a repeated-recursion marker.
-/
namespace MicroCFTA.SourcePruningNativeView
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedGuardedLanguage
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {Guard Key : Type}

/-- An actual narrowing result denotes exactly its accepted filtered source edges. -/
theorem narrowAt_edges [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol)
    (fits : Key → Symbol → Bool) (admits : Key → Value Symbol Guard → Bool)
    (key : Key) (fuel : Nat) (value : Value Symbol Guard)
    (before : State Symbol Guard) (result : Value Symbol Guard)
    (after : State Symbol Guard)
    (ready : SourceEqualityRequiredCache.Ready before)
    (available : Available before value) (closed : value.free = [])
    (actual : narrowAt fits admits fuel key value before = .done result after) :
    ∃ rows middle,
      MergedFreshOrdinaryExposure.nodeEdges fuel value before = .done rows middle ∧
      run (makeNode (rows.filter (keeps fits admits key))) middle = (result, after) ∧
      ∀ term, meaning holds ambient result term ↔
        ∃ edge ∈ rows, keeps fits admits key edge = true ∧ edgeMeaning holds ambient edge term := by
  unfold narrowAt at actual
  cases exposed : MergedFreshOrdinaryExposure.nodeEdges fuel value before with
  | unresolved | pending | exhausted =>
      simp only [exposed] at actual
      cases actual
  | done rows middle =>
      have built : run (makeNode (rows.filter (keeps fits admits key))) middle = (result, after) := by
        exact Prod.ext
          (MergedSourceComparison.Result.done.inj (by simpa only [exposed] using actual)).1
          (MergedSourceComparison.Result.done.inj (by simpa only [exposed] using actual)).2
      have checked := MergedFreshOrdinaryColdEffects.nodeEdges_verified fuel value before
        ready.semantic ready.covered available closed
      have semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap middle := by
        simpa only [exposed, MergedSourceExposure.Result.state] using checked.semantic
      have resident : InternedNestedProvenance.Edges middle (rows.filter (keeps fits admits key)) :=
        fun edge member => checked.edges rows middle exposed edge (List.mem_filter.mp member).1
      refine ⟨rows, middle, rfl, built, ?_⟩
      intro term
      have constructed : meaning holds ambient result term ↔
          ∃ edge ∈ rows.filter (keeps fits admits key),
            MergedColdInterpretation.EdgeMeaning (meaning holds ambient) holds edge term := by
        simpa only [built] using makeNode_exact middle semantic.1.normal.facts
          holds ambient (rows.filter (keeps fits admits key)) resident term
      constructor
      · intro accepted
        obtain ⟨edge, member, accepted⟩ := constructed.mp accepted
        obtain ⟨member, kept⟩ := List.mem_filter.mp member
        exact ⟨edge, member, kept, (edgeMeaning_all holds ambient edge term).mpr accepted⟩
      · rintro ⟨edge, member, kept, accepted⟩
        exact constructed.mpr ⟨edge, List.mem_filter.mpr ⟨member, kept⟩,
          (edgeMeaning_all holds ambient edge term).mp accepted⟩

/-- An accepted actual narrowing result is accepted by the original independent value. -/
theorem narrowAt_sound [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol)
    (fits : Key → Symbol → Bool) (admits : Key → Value Symbol Guard → Bool)
    (key : Key) (fuel : Nat) (value : Value Symbol Guard)
    (before : State Symbol Guard) (result : Value Symbol Guard)
    (after : State Symbol Guard)
    (ready : SourceEqualityRequiredCache.Ready before)
    (guarded : InternedGuardedProbeHeap.Heap before)
    (available : Available before value) (closed : value.free = [])
    (actual : narrowAt fits admits fuel key value before = .done result after)
    (term : Term Symbol) (accepted : meaning holds ambient result term) :
    meaning holds ambient value term := by
  obtain ⟨rows, middle, exposed, _built, exactRows⟩ :=
    narrowAt_edges holds ambient fits admits key fuel value before result after ready available closed actual
  obtain ⟨edge, member, _kept, accepted⟩ := (exactRows term).mp accepted
  exact MergedFreshOrdinaryGuardedSoundness.nodeEdges_sound holds ambient fuel value before
    ready.semantic ready.covered guarded available closed rows middle exposed edge member term accepted

end MicroCFTA.SourcePruningNativeView

namespace MicroCFTA.SourcePruningOuterNarrow
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedGuardedLanguage
open SourcePruningRecordTypes (Metadata)
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {Guard Typing Key : Type}

/-- Mu and type skips or actual filtering return only terms of the original value. -/
theorem narrow_sound [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → Value Symbol Guard → Bool) (metadata : Metadata Typing)
    (fuel uv : Nat) (value : Value Symbol Guard) (before : State Symbol Guard)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (ready : SourceEqualityRequiredCache.Ready before)
    (guarded : InternedGuardedProbeHeap.Heap before)
    (available : Available before value) (closed : value.free = [])
    (actual : narrow holeKey fits admits metadata fuel uv value before = .done result after)
    (term : Term Symbol) (accepted : meaning holds ambient result term) :
    meaning holds ambient value term := by
  have skipped (same : result = value ∧ after = before) : meaning holds ambient value term := by
    obtain ⟨rfl, rfl⟩ := same
    exact accepted
  by_cases typed : uv ∈ metadata.types
  · have pureDone := narrow_type holeKey fits admits metadata fuel uv value before typed
    have parts := MergedSourceComparison.Result.done.inj (pureDone.symm.trans actual)
    exact skipped ⟨parts.1.symm, parts.2.symm⟩
  · cases value with
    | mu =>
        have parts := MergedSourceComparison.Result.done.inj actual
        exact skipped ⟨parts.1.symm, parts.2.symm⟩
    | empty | reference | node | union =>
        have narrowed := actual
        simp [narrow, typed] at narrowed
        exact SourcePruningNativeView.narrowAt_sound holds ambient fits admits
          (holeKey metadata.typing uv) fuel _ before result after ready guarded
          available closed narrowed term accepted

end MicroCFTA.SourcePruningOuterNarrow
