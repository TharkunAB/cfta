import MicroCFTA.SourceCurrentSecondaryTrace
import MicroCFTA.SourceCurrentSecondaryProjectionSupport
import MicroCFTA.SourceSecondaryGateEndpointClosed

/-!
# Closed original endpoints of the current secondary gate

The current constrained-Mu endpoint can return false when it is closed.
Open ordinary Mu unfolding retains every original external free name.
Thus every completed false empty-path trace still proves original
closedness. The original weighted gate invariant remains explicit.
-/
namespace MicroCFTA.SourceCurrentSecondaryEndpointClosed
open InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentSecondaryTrace
open InternedFreshOrdinaryMemoGateTrace (Ready)

private def EndpointClosed (path : EqualityNormalize.Path) (value : Value Symbol Guard)
    (before : State Symbol Guard) (answer : Bool) : Prop :=
  path = [] → answer = false → Ready before → Available before value → value.free = []

private theorem node_closed [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool)
    {path : EqualityNormalize.Path} {value : Value Symbol Guard} {before : State Symbol Guard}
    {answer : Bool} {after : State Symbol Guard}
    (trace : NodeTrace unconstrained path value before answer after) :
    EndpointClosed path value before answer := by
  induction trace using NodeTrace.rec
      (motive_2 := fun _ _ _ _ _ _ _ => True)
      (motive_3 := fun _ _ _ _ _ _ _ => True) with
  | empty => intro _ _ _ _; rfl
  | reference => intro _ impossible; cases impossible
  | union => intro _ impossible; cases impossible
  | finite fast =>
      intro _ _ _ _
      simpa only [Value.free, List.isEmpty_iff] using (Bool.and_eq_true_iff.mp fast).2
  | endpoint slow =>
      intro _ cleared _ _
      simpa only [Value.free, Bool.not_eq_false', List.isEmpty_iff] using cleared
  | branches slow trace ih => intro impossible; cases impossible
  | constrained blocked =>
      intro atEndpoint cleared _ _
      rw [atEndpoint] at cleared
      simpa only [Bool.not_eq_false', List.isEmpty_iff] using cleared
  | closed plain closed => intro _ _ _ _; exact List.isEmpty_iff.mp closed
  | @unfold entry body depth ordinary before next middle path answer final plain opened actual trace ih =>
      intro atEndpoint cleared ready available
      have openFree : (Value.mu entry body depth ordinary).free ≠ [] := by
        intro empty
        simp only [empty, List.isEmpty_nil] at opened
        cases opened
      have retained := SourceSecondaryGateEndpointClosed.unfold_retains_free entry body depth ordinary
        before next middle ready available openFree actual
      have nextClosed := ih atEndpoint cleared retained.1 retained.2.1
      apply Classical.byContradiction
      intro notClosed
      obtain ⟨name, member⟩ := List.exists_mem_of_ne_nil _ notClosed
      have survives := retained.2.2 name member
      simp only [nextClosed, List.not_mem_nil] at survives
  | missing => trivial
  | present => trivial
  | nil => trivial
  | stop => trivial
  | next => trivial

/-- The complete current false endpoint trace derives original closedness. -/
theorem endpoint_closed [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool)
    {value : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : NodeTrace unconstrained [] value before false after)
    (ready : Ready before) (available : Available before value) : value.free = [] :=
  node_closed unconstrained trace rfl rfl ready available

/-- Closed values and actual anchored false endpoint certificates both imply closedness. -/
theorem support_closed [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (ready : Ready anchor) (value : Value Symbol Guard)
    (support : SourceCurrentSecondaryProjectionSupport.Support unconstrained anchor [] value) : value.free = [] := by
  rcases support with closed | ⟨available, trace⟩
  · exact closed
  · exact endpoint_closed unconstrained trace ready available

end MicroCFTA.SourceCurrentSecondaryEndpointClosed
