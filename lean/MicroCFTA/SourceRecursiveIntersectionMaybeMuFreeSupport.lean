import MicroCFTA.SourceRecursiveIntersectionMaybeMuCompletion
import MicroCFTA.InternedStoredPlanFreeSupport

/-!
# Free-name support after actual optional-binder construction

The exact stored plan and used lexical positions determine result support.
Every returned free name belongs to the original body and differs from
the selected intersection name. Normalization can remove more names.
-/
namespace MicroCFTA.SourceRecursiveIntersectionMaybeMu
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedStoredSubstitution InternedFreshOrdinaryContext
open InternedFreeNameIndexedOrigins
open InternedBinderProtocol (Reference)

/-- Actual optional binders retain only original free names and remove their selected intersection name. -/
theorem free_support [DecidableEq (EdgeKey Symbol Guard)] (pair : Nat × Nat) (body : Value Symbol Guard)
    (state : State Symbol Guard) (context : Context state environment) (available : Available state body)
    (value : Value Symbol Guard) (after : State Symbol Guard) (done : maybeMu pair body state = .done value after)
    (name : Reference) (member : name ∈ value.free) : name ∈ body.free ∧ name ≠ .intersection pair.1 pair.2 := by
  rw [maybeMu_eq pair body state state context.normal.facts available] at done
  split at done
  · have leavesContext : Context state (leaves body) :=
      ⟨context.normal, leaves_available body state available, context.profiles, context.freeNames⟩
    obtain ⟨index, leaf, used, found, named⟩ := source_indexed _ (leaves body) state leavesContext value after done name member
    have supported := InternedStoredPlanFreeSupport.encode_free (leaves body) [.intersection pair.1 pair.2] body state
      context.normal.facts.coherent leavesContext.inputs available (fun _ member => member) index leaf found name named
      (by simpa only [Uses, List.length_singleton, Nat.add_comm] using used)
    exact ⟨supported.1, fun same => supported.2 (by simp [same])⟩
  · rename_i absent
    cases done
    exact ⟨member, fun same => absent (same ▸ member)⟩

/-- The exact optional-binder result has no remaining occurrence of its selected intersection name. -/
theorem pair_absent [DecidableEq (EdgeKey Symbol Guard)] (pair : Nat × Nat) (body : Value Symbol Guard)
    (state : State Symbol Guard) (context : Context state environment) (available : Available state body)
    (value : Value Symbol Guard) (after : State Symbol Guard) (done : maybeMu pair body state = .done value after) :
    .intersection pair.1 pair.2 ∉ value.free := by
  intro member
  exact (free_support pair body state context available value after done _ member).2 rfl

end MicroCFTA.SourceRecursiveIntersectionMaybeMu
