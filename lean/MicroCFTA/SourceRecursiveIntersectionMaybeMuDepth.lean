import MicroCFTA.SourceRecursiveIntersectionMaybeMu
import MicroCFTA.InternedOpenDepthExecution
import MicroCFTA.InternedStoredLeafShape
import MicroCFTA.InternedMuDepthInventory

/-!
# Open binder depth of an actual optional-binder result

The actual repaired constructor adds at most one open binder level.
Closed captures and literal references have zero open depth.
The result uses the actual body and completed constructor observation.
-/
namespace MicroCFTA.SourceRecursiveIntersectionMaybeMu
open InternedConstructorTemplates InternedProbeProvenance
open InternedStoredSubstitution InternedStoredPlanBinderDepth

variable {Symbol Guard : Type}

/-- An actual completed optional binder adds at most one open binder level. -/
theorem result_le [DecidableEq (EdgeKey Symbol Guard)] (key : Nat × Nat)
    (body : Value Symbol Guard) (state : State Symbol Guard)
    (context : InternedFreshOrdinaryContext.Context state [])
    (cached : InternedFreshOrdinaryDepthHeap.Heap state)
    (opened : InternedOpenDepthReadback.Heap state)
    (available : Available state body) (value : Value Symbol Guard)
    (after : State Symbol Guard) (done : maybeMu key body state = .done value after) :
    valueDepth value ≤ valueDepth body + 1 := by
  have inputs := leaves_available body state available
  have captured : InternedFreshOrdinaryContext.Context state (leaves body) :=
    ⟨context.normal, inputs, context.profiles, context.freeNames⟩
  have zero : ∀ leaf ∈ leaves body, valueDepth leaf ≤ 0 := by
    intro leaf member
    rcases InternedStoredLeafShape.leaves_shape body leaf member with closed | ⟨name, rfl⟩
    · rw [valueDepth.eq_def]
      simp only [closed, List.isEmpty_nil, ↓reduceIte, Nat.le_refl]
    · simp [valueDepth]
  rw [maybeMu_eq key body state state context.normal.facts available] at done
  split at done
  · have bound := InternedOpenDepthExecution.build_bound
      (.binder true (encode (leaves body) [.intersection key.1 key.2] body))
      (leaves body) state captured cached opened 0 zero value after done
    simp only [syntaxDepth, encode_depth, Nat.add_zero] at bound
    omega
  · cases done
    omega

/-- Every new Mu body is below the actual optional-binder plan bound. -/
theorem lower [DecidableEq (EdgeKey Symbol Guard)] (key : Nat × Nat)
    (body : Value Symbol Guard) (state : State Symbol Guard)
    (context : InternedFreshOrdinaryContext.Context state [])
    (cached : InternedFreshOrdinaryDepthHeap.Heap state)
    (opened : InternedOpenDepthReadback.Heap state)
    (available : Available state body) :
    InternedStoredPlanBinderDepthProgress.Lower state (valueDepth body + 1)
      (maybeMu key body state).state := by
  have captured : InternedFreshOrdinaryContext.Context state (leaves body) :=
    ⟨context.normal, leaves_available body state available, context.profiles, context.freeNames⟩
  have zero : ∀ leaf ∈ leaves body, valueDepth leaf = 0 := by
    intro leaf member
    rcases InternedStoredLeafShape.leaves_shape body leaf member with closed | ⟨name, rfl⟩
    · rw [valueDepth.eq_def]
      simp only [closed, List.isEmpty_nil, ↓reduceIte]
    · simp [valueDepth]
  rw [maybeMu_eq key body state state context.normal.facts available]
  split
  · exact InternedStoredPlanBinderDepthProgress.build_lower _ _ state captured cached opened
      (InternedStoredPlanBinderDepthProgress.lower_refl state _) zero
      (by simp only [syntaxDepth, encode_depth]; omega)
  · exact InternedStoredPlanBinderDepthProgress.lower_refl state _

/-- A body below the current ceiling preserves that ceiling through every actual outcome. -/
theorem bounded_outcome [DecidableEq (EdgeKey Symbol Guard)] (key : Nat × Nat)
    (body : Value Symbol Guard) (state : State Symbol Guard)
    (context : InternedFreshOrdinaryContext.Context state [])
    (cached : InternedFreshOrdinaryDepthHeap.Heap state)
    (opened : InternedOpenDepthReadback.Heap state)
    (available : Available state body) (limit : Nat)
    (bounded : InternedMuDepthInventory.Bounded state limit)
    (inside : valueDepth body < limit) :
    InternedMuDepthInventory.Bounded (maybeMu key body state).state limit := by
  intro name entry stored depth ordinary present
  rcases lower key body state context cached opened available name entry stored depth ordinary present with
    old | small
  · exact bounded name entry stored depth ordinary old
  · omega

end MicroCFTA.SourceRecursiveIntersectionMaybeMu
