import MicroCFTA.SourceCurrentNativeMuPublication
import MicroCFTA.SourceRecursiveIntersectionSemanticHeap

/-!
# Actual native optional-binder publication histories

The native callback and constructor equal the repaired source executor.
Their histories include every actual stopping outcome. An unused pair
returns the original state and needs no publication step.
-/
namespace MicroCFTA.SourceCurrentNativeMuHistory
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedStoredSubstitution
open InternedBinderProtocol (Reference)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceCurrentNativeMuPublication (History)

private theorem context (body : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticHeap before) (available : Available before body) :
    SourceCurrentConstrainedCapSourceHistory.Context before (leaves body) :=
  ⟨SourceRecursiveIntersectionSemanticHeap.context before semantic (leaves body)
    (leaves_available body before available), semantic.2⟩

/-- The actual native callback produces its complete publication history through root filtering. -/
theorem callback [DecidableEq (EdgeKey Symbol Guard)] (old marker : Reference)
    (body : Value Symbol Guard) (before : State Symbol Guard) (semantic : SemanticHeap before)
    (available : Available before body) (argument : Available before (.reference marker)) :
    Nonempty (History before (SourceRecursiveIntersectionMaybeMu.callback old body marker before).state) := by
  rw [SourceRecursiveIntersectionMaybeMu.callback_eq old body marker before before
    semantic.1.normal.facts available]
  unfold InternedFreshOrdinaryFacts.callback
  obtain ⟨history⟩ := SourceCurrentNativeMuPublication.build_history (encode (leaves body) [old] body)
    (.reference marker :: leaves body) before ((context body before semantic available).local marker argument)
  cases actual : InternedFreshOrdinaryConstruction.build (encode (leaves body) [old] body)
      (.reference marker :: leaves body) before with
  | pending key after =>
      exact ⟨by simpa only [actual, Outcome.bind, Outcome.state] using history⟩
  | done value after =>
      have raw : History before after := by simpa only [actual, Outcome.state] using history
      refine ⟨?_⟩
      simpa only [actual, Outcome.bind, InternedNestedConstruction.work, Outcome.state] using
        History.trans raw (.retain after _ (InternedStoredMuOrigins.filter_noNewMu marker value after))

/-- Exact native construction produces the source history for both probes and publication. -/
theorem construct [DecidableEq (EdgeKey Symbol Guard)] (old : Reference) (body : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticHeap before) (available : Available before body) :
    Nonempty (History before (SourceRecursiveIntersectionMaybeMu.construct old body before).state) := by
  rw [SourceRecursiveIntersectionMaybeMu.construct_eq old body before before semantic.1.normal.facts available]
  exact SourceCurrentNativeMuPublication.build_history (.binder true (encode (leaves body) [old] body))
    (leaves body) before (context body before semantic available)

/-- Every native optional-binder outcome has its actual source publication history. -/
theorem maybeMu [DecidableEq (EdgeKey Symbol Guard)] (pair : Nat × Nat) (body : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticHeap before) (available : Available before body) :
    Nonempty (History before (SourceRecursiveIntersectionMaybeMu.maybeMu pair body before).state) := by
  unfold SourceRecursiveIntersectionMaybeMu.maybeMu
  split
  · exact construct _ body before semantic available
  · exact ⟨.refl before⟩

end MicroCFTA.SourceCurrentNativeMuHistory
