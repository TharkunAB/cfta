import MicroCFTA.SourceRecursiveIntersectionNativeColdObservation

/-!
# Native memo states between complete source calls

An idle state has no evaluating node or edge cell. Suspended and returned
cells are permitted. Completed body code and constructor-cache growth retain
this property. Every idle state satisfies all active-request lower bounds.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode

/-- Neither native memo family has an evaluating cell between calls. -/
def Idle (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) : Prop :=
  (∀ handle request, state.nodes.cells handle ≠ some ⟨request, .evaluating⟩) ∧
  (∀ handle request, state.edges.cells handle ≠ some ⟨request, .evaluating⟩)

/-- Empty memo tables are idle. -/
theorem idle_initial (machine : Machine Symbol Guard) : Idle (initial width machine) := by
  constructor <;> intro handle request impossible <;> cases impossible

/-- A state with no new running cells remains idle. -/
theorem Idle.retained {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (idle : Idle before) (retained : Retains after before) : Idle after :=
  ⟨fun handle request running => idle.1 handle request (retained.1 handle request running),
    fun handle request running => idle.2 handle request (retained.2 handle request running)⟩

/-- Constructor and domain cache effects do not change idle memo cells. -/
theorem Idle.advance (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (after : Machine Symbol Guard) (idle : Idle state) : Idle (advance state after) := idle

/-- Idle memo tables satisfy every active-request bound, including after earlier complete calls. -/
theorem Idle.active [DecidableEq Symbol] (view : IntersectSchedule.View Symbol)
    (holds : Guard → Language.Term Symbol → Bool) (bound : Nat)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) (idle : Idle state) : ActiveAbove view holds bound state :=
  ⟨fun handle request running => False.elim (idle.1 handle request running),
    fun handle request running => False.elim (idle.2 handle request running)⟩

/-- Actual completed body code returns an idle state from an idle source state. -/
theorem done_idle [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (code : Code Symbol Guard A) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (value : A)
    (clean : BodyCode code) (shape : Shape state) (idle : Idle state)
    (done : execute emptyGuard conjoin fuel code state = .done value after) : Idle after :=
  idle.retained ((evaluation_of_done emptyGuard conjoin fuel code state after value done).running_before clean shape)

end MicroCFTA.SourceRecursiveIntersectionNative
