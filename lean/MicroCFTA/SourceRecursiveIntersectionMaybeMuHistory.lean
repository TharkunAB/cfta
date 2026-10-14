import MicroCFTA.SourceRecursiveIntersectionMaybeMuActiveEncounter
import MicroCFTA.InternedFreshOrdinaryRootEncounter
import MicroCFTA.InternedStoredLeavesOrdinary

/-!
# Actual source capture histories for pending optional binders

The stored body's exact lexical plan supplies the original source root.
An ordinary capture in the active ancestor is free in the original body
or comes from an actual earlier callback with a shorter captured prefix.
The initial alternative is excluded only when the body has no such name.
-/
namespace MicroCFTA.SourceRecursiveIntersectionMaybeMu
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedStoredSubstitution
open InternedFreshOrdinaryActiveOrigins (Origin)
open InternedFreshOrdinaryActiveSite (Site)
open InternedFreshOrdinarySourceHistory
open InternedBinderProtocol (NodeKey)

/-- Actual pending optional-binder execution retains every enclosing pending callback at the exact mismatch origin. -/
theorem stopped_pending_mismatch [DecidableEq (EdgeKey Symbol Guard)] (pair : Nat × Nat) (body : Value Symbol Guard)
    (state final : State Symbol Guard) (key : NodeKey)
    (context : InternedFreshOrdinaryContext.Context state environment) (available : Available state body)
    (covered : Covered [] state) (stopped : maybeMu pair body state = .pending key final) :
    ∃ origin : Origin Symbol Guard key,
      StoppedRooted (.binder true (encode (leaves body) [.intersection pair.1 pair.2] body)) (leaves body) key final origin ∧
      ∃ site : Site origin final, InternedFreshOrdinaryJointMismatch.Mismatch site := by
  have leavesContext : InternedFreshOrdinaryContext.Context state (leaves body) :=
    ⟨context.normal, leaves_available body state available, context.profiles, context.freeNames⟩
  rw [maybeMu_eq pair body state state context.normal.facts available] at stopped
  split at stopped
  · exact InternedFreshOrdinaryRootEncounter.complete_stopped_mismatch _ (leaves body) state leavesContext covered key final stopped
  · cases stopped

/-- Actual pending optional-binder execution derives the original source path and live mismatch at the same origin. -/
theorem rooted_pending_mismatch [DecidableEq (EdgeKey Symbol Guard)] (pair : Nat × Nat) (body : Value Symbol Guard)
    (state final : State Symbol Guard) (key : NodeKey)
    (context : InternedFreshOrdinaryContext.Context state environment) (available : Available state body)
    (covered : Covered [] state) (stopped : maybeMu pair body state = .pending key final) :
    ∃ origin : Origin Symbol Guard key,
      Rooted (.binder true (encode (leaves body) [.intersection pair.1 pair.2] body)) (leaves body) origin ∧
      ∃ site : Site origin final, InternedFreshOrdinaryJointMismatch.Mismatch site := by
  obtain ⟨origin, rooted, site, mismatch⟩ := stopped_pending_mismatch pair body state final key context available covered stopped
  exact ⟨origin, StoppedReached.reached rooted, site, mismatch⟩

/-- Each old ordinary capture comes from the original body or a shorter producer with its actual pending callback. -/
theorem pending_callback_history [DecidableEq (EdgeKey Symbol Guard)] (pair : Nat × Nat) (body : Value Symbol Guard)
    (state final : State Symbol Guard) (key : NodeKey)
    (context : InternedFreshOrdinaryContext.Context state environment) (available : Available state body)
    (covered : Covered [] state) (stopped : maybeMu pair body state = .pending key final) :
    ∃ origin : Origin Symbol Guard key, ∃ site : Site origin final,
      InternedFreshOrdinaryJointMismatch.Mismatch site ∧
      ∀ level, .uninterned level ∈ origin.depth.free →
        .uninterned level ∈ body.free ∨ PendingProducedAt key final (.binder origin.smart origin.body) origin.environment origin.before level := by
  obtain ⟨origin, rooted, site, mismatch⟩ := stopped_pending_mismatch pair body state final key context available covered stopped
  refine ⟨origin, site, mismatch, ?_⟩
  intro level member
  rcases StoppedRooted.ordinary_capture rooted level member with ⟨leaf, supplied, captured⟩ | produced
  · exact Or.inl (InternedStoredLeavesOrdinary.leaves_ordinary body state context.normal.facts.coherent
      available leaf supplied level captured)
  · exact Or.inr produced

/-- Each old ordinary capture retains its initial-body or completed-probe history. -/
theorem pending_capture_history [DecidableEq (EdgeKey Symbol Guard)] (pair : Nat × Nat) (body : Value Symbol Guard)
    (state final : State Symbol Guard) (key : NodeKey)
    (context : InternedFreshOrdinaryContext.Context state environment) (available : Available state body)
    (covered : Covered [] state) (stopped : maybeMu pair body state = .pending key final) :
    ∃ origin : Origin Symbol Guard key, ∃ site : Site origin final,
      InternedFreshOrdinaryJointMismatch.Mismatch site ∧
      ∀ level, .uninterned level ∈ origin.depth.free →
        .uninterned level ∈ body.free ∨ ProducedAt (.binder origin.smart origin.body) origin.environment origin.before level := by
  obtain ⟨origin, site, mismatch, histories⟩ := pending_callback_history pair body state final key context available covered stopped
  refine ⟨origin, site, mismatch, ?_⟩
  intro level member
  exact (histories level member).imp id PendingProducedAt.produced

/-- A body with no ordinary free names derives actual stopped shorter producers at the same blocked key and cache. -/
theorem pending_mismatch_callbacks [DecidableEq (EdgeKey Symbol Guard)] (pair : Nat × Nat) (body : Value Symbol Guard)
    (state final : State Symbol Guard) (key : NodeKey)
    (context : InternedFreshOrdinaryContext.Context state environment) (available : Available state body)
    (covered : Covered [] state) (ordinaryAbsent : ∀ level, .uninterned level ∉ body.free)
    (stopped : maybeMu pair body state = .pending key final) :
    ∃ origin : Origin Symbol Guard key, ∃ site : Site origin final,
      InternedFreshOrdinaryJointMismatch.Mismatch site ∧
      ∀ level, .uninterned level ∈ origin.depth.free →
        PendingProducedAt key final (.binder origin.smart origin.body) origin.environment origin.before level := by
  obtain ⟨origin, site, mismatch, histories⟩ := pending_callback_history pair body state final key context available covered stopped
  refine ⟨origin, site, mismatch, ?_⟩
  intro level member
  rcases histories level member with original | produced
  · exact False.elim (ordinaryAbsent level original)
  · exact produced

/-- A body with no ordinary free names derives actual shorter producers without an initial-capture alternative. -/
theorem pending_mismatch_producers [DecidableEq (EdgeKey Symbol Guard)] (pair : Nat × Nat) (body : Value Symbol Guard)
    (state final : State Symbol Guard) (key : NodeKey)
    (context : InternedFreshOrdinaryContext.Context state environment) (available : Available state body)
    (covered : Covered [] state) (ordinaryAbsent : ∀ level, .uninterned level ∉ body.free)
    (stopped : maybeMu pair body state = .pending key final) :
    ∃ origin : Origin Symbol Guard key, ∃ site : Site origin final,
      InternedFreshOrdinaryJointMismatch.Mismatch site ∧
      ∀ level, .uninterned level ∈ origin.depth.free → ProducedAt (.binder origin.smart origin.body) origin.environment origin.before level := by
  obtain ⟨origin, site, mismatch, histories⟩ := pending_mismatch_callbacks pair body state final key context available covered ordinaryAbsent stopped
  exact ⟨origin, site, mismatch, fun level member => PendingProducedAt.produced (histories level member)⟩

end MicroCFTA.SourceRecursiveIntersectionMaybeMu
