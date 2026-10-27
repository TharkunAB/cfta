import MicroCFTA.SourcePruningEnumerationNativeReferences
import MicroCFTA.SourcePruningEnumerationNativeLanguage
import MicroCFTA.SourcePruningEnumerationSelection
import MicroCFTA.SourcePruningEnumerationRendering

/-!
# Empty pending roots with no incoming suspended references

This certificate concerns the actual core and its suspended references.
A separate native read and boundary fact make the root unselectable.
The certificate does not imply safety or semantic validity of removed constraints.
-/
namespace MicroCFTA.EnumerationDischargeHistory
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationReferences
open EnumerationCompressionFrame
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard : Type}

/-- One root keeps a native handle and has no suspended constraints or incoming suspended reference. -/
structure IsolatedPending (held handle : Nat) (state : State Symbol EnumGuard) : Prop where
  /-- The slot is a representative of its class. -/
  root : IsRoot state.representatives held
  /-- The actual pending payload retains its native handle. -/
  stored : state.values[held]? = some (.unenumerated (some handle) [])
  /-- Every stored suspended reference avoids this class. -/
  incoming : IncomingAvoid held state

/-- An isolated native pending slot contradicts full structural discharge. -/
theorem IsolatedPending.not_discharged
    (isolated : IsolatedPending held handle state) :
    ¬SourcePruningEnumerationRendering.Discharged state := by
  intro discharged
  have impossible := (discharged held (some handle) [] isolated.stored).1
  cases impossible

/-- Actual compression retains the complete isolated pending certificate. -/
theorem IsolatedPending.through_frame
    (isolated : IsolatedPending held handle before) (frame : Frame before after) :
    IsolatedPending held handle after := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨isolated.root.choose,
      (frame.reaches held held isolated.root.choose).mpr isolated.root.choose_spec⟩
  · rw [frame.values]
    exact isolated.stored
  · intro value member sc listed same
    have oldMember : value ∈ before.values := by simpa only [frame.values] using member
    exact isolated.incoming value oldMember sc listed
      ((SourcePruningEnumerationNativeLanguage.frame_sameClass before after frame held sc.var).mp same)

/-- Actual root protection and allowed-reference effects retain the certificate. -/
theorem IsolatedPending.through_protected
    (isolated : IsolatedPending held handle before)
    (protectedRoot : EnumerationDriver.Protected held before after)
    (scs : List Suspended) (inputs : Avoids before.representatives held scs)
    (effects : ∀ allowed, ReferencesAllowed allowed before → InputsAllowed allowed scs →
      ReferencesAllowed allowed after) : IsolatedPending held handle after := by
  exact ⟨protectedRoot.root, protectedRoot.value.trans isolated.stored,
    SourcePruningEnumerationNativeReferences.incoming_preserved before after held scs isolated.incoming
      inputs protectedRoot.classes effects⟩

/-- A fresh empty allocation has no incoming suspended reference under current storage bounds. -/
theorem allocated_isolated (before : State Symbol EnumGuard) (handle : Nat) (safe : Safe before) :
    IsolatedPending before.counter handle (allocated (some handle) before) := by
  refine ⟨⟨1, .root ?_⟩, allocated_slot (some handle) before safe.1.aligned, ?_⟩
  · simp [allocated, UnionFind.read, outside_forest before.representatives before.counter before.counter
      safe.1.forest (Nat.le_refl _)]
  · intro value member sc listed same
    change value ∈ before.values ++ [.unenumerated (some handle) []] at member
    change UnionFind.SameClass before.representatives before.counter sc.var at same
    rcases List.mem_append.mp member with old | fresh
    · cases value with
      | eliminated | enumerated _ => simp [references] at listed
      | unenumerated node bucket =>
          have bound : sc.var < before.counter := safe.1.values _ old sc listed
          have equal := outside_class before.representatives before.counter before.counter sc.var
            safe.1.forest (Nat.le_refl _) same
          omega
    · have sameValue : value = .unenumerated (some handle) [] := by simpa using fresh
      subst value
      simp [references] at listed

end MicroCFTA.EnumerationDischargeHistory
