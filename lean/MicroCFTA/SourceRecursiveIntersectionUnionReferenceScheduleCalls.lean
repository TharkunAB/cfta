import MicroCFTA.SourceRecursiveIntersectionScheduleCalls
import MicroCFTA.SourceRecursiveIntersectionUnionSchedule

/-!
# Actual union and reference branches from recursive correspondence

Ordered union requests retain every source member occurrence. Reference
lookup selects the original available Mu of the semantic domain. These
branches use the same fixed final cache as the recursive induction.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache Language Binding InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionCode (NodeScope OriginalBindings)
open SourceRecursiveIntersectionInputView (view inputOf Original)
open SourceRecursiveIntersectionScheduleConstructors (Corresponds)
open SourceRecursiveIntersectionScheduleEnvironment (Ordered)

/-- Ordered actual union calls retain the complete semantic member walk under recursive correspondence. -/
theorem union_schedule_calls [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (replay : Replays call) (state : Machine Symbol Guard) (valid : Valid state)
    (holds : Guard → Term Symbol → Bool) (fuel : Nat) (correct : ScheduleCalls call state holds fuel)
    (domain : Interned DomainKey) (known : Domain state domain) (ordered : Ordered domain.key.seen)
    (members : List (Value Symbol Guard)) (other : Value Symbol Guard) (left : Bool)
    (membersOriginal : ∀ member ∈ members, Original member) (otherOriginal : Original other)
    (membersAvailable : ∀ member ∈ members, Available state.heap member) (otherAvailable : Available state.heap other)
    (bindings : OriginalBindings state.heap domain.key) (value : Value Symbol Guard)
    (done : (walk (fun member => if left then call domain member other else call domain other member) members state).bind
      (fun values current => work (makeUnion values) current) = .done value state) :
    ∃ shapes, IntersectSchedule.walk (fun member => if left then
      IntersectSchedule.run (view state.heap holds) (fuel + 1) (SourceRecursiveIntersectionSchedule.domain domain.key) (inputOf member) (inputOf other)
      else IntersectSchedule.run (view state.heap holds) (fuel + 1) (SourceRecursiveIntersectionSchedule.domain domain.key) (inputOf other) (inputOf member))
      members = .ok shapes ∧ Corresponds holds value (.alternatives shapes) := by
  apply union_schedule_body call calls replay domain members other left state state valid valid known
    otherAvailable membersAvailable value state done (.refl _) holds
  intro member present result completed
  have later := correct.larger call state holds fuel (fuel + 1) (by omega)
  cases left
  · exact later domain other member known
      ⟨otherOriginal, membersOriginal member present, otherAvailable, membersAvailable member present, bindings⟩ ordered result completed
  · exact later domain member other known
      ⟨membersOriginal member present, otherOriginal, membersAvailable member present, otherAvailable, bindings⟩ ordered result completed

/-- Actual reference resolution retains the complete semantic lookup action under recursive correspondence. -/
theorem reference_schedule_calls [DecidableEq Symbol]
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (state : Machine Symbol Guard) (valid : Valid state) (holds : Guard → Term Symbol → Bool)
    (fuel : Nat) (correct : ScheduleCalls call state holds fuel)
    (domain : Interned DomainKey) (known : Domain state domain) (ordered : Ordered domain.key.seen)
    (name : Nat) (other : Value Symbol Guard) (left : Bool) (otherOriginal : Original other)
    (otherAvailable : Available state.heap other) (bindings : OriginalBindings state.heap domain.key)
    (value : Value Symbol Guard) (done : reference call domain name other left state = .done value state) :
    ∃ shape, (match IntersectSchedule.lookup (SourceRecursiveIntersectionSchedule.domain domain.key) name with
      | none => Except.error (IntersectSchedule.Error.missingBinder name)
      | some binder => if left then
          IntersectSchedule.run (view state.heap holds) (fuel + 1) (SourceRecursiveIntersectionSchedule.domain domain.key) binder (inputOf other)
        else IntersectSchedule.run (view state.heap holds) (fuel + 1) (SourceRecursiveIntersectionSchedule.domain domain.key) (inputOf other) binder) =
      .ok shape ∧ Corresponds holds value shape := by
  by_cases bound : name ∈ SourceRecursiveIntersectionDomain.names domain.key
  · obtain ⟨binder, found, original, available, encoded⟩ := bindings.read state.heap state.heap valid.1
      (grows_refl _) (extends_refl _) domain.key name bound
    simp only [reference, bound, ↓reduceIte, found] at done
    have later := correct.larger call state holds fuel (fuel + 1) (by omega)
    cases left
    · obtain ⟨shape, completed, meaning⟩ := later domain other binder known
        ⟨otherOriginal, original, otherAvailable, available, bindings⟩ ordered value done
      refine ⟨shape, ?_, meaning⟩
      simpa only [SourceRecursiveIntersectionSchedule.lookup_domain, bound, Bool.false_eq_true, ↓reduceIte, encoded] using completed
    · obtain ⟨shape, completed, meaning⟩ := later domain binder other known
        ⟨original, otherOriginal, available, otherAvailable, bindings⟩ ordered value done
      refine ⟨shape, ?_, meaning⟩
      simpa only [SourceRecursiveIntersectionSchedule.lookup_domain, bound, ↓reduceIte, encoded] using completed
  · simp only [reference, bound, ↓reduceIte] at done
    cases done

end MicroCFTA.SourceRecursiveIntersectionKernel
