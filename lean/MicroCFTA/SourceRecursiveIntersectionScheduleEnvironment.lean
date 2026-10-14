import MicroCFTA.SourceRecursiveIntersectionGuardedInput
import MicroCFTA.SourceRecursiveIntersectionResultScope
import MicroCFTA.SourceRecursiveIntersectionGuardedEffects

/-!
# Recursive pair environments for the semantic schedule

The schedule encodes a canonical identity pair as a natural binder name.
Actual values retain the complete pair reference. Ordered pairs make this
encoding injective on every free name that a recursive result can read.
-/
namespace MicroCFTA.SourceRecursiveIntersectionScheduleEnvironment
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol (Reference)
open SourceRecursiveIntersectionResultScope (Scope)
open Std
attribute [local instance] lexOrd

/-- Interpret actual repeated-pair references by their schedule binder names. -/
def environment (ambient : BinderLanguage.Env Symbol) : InternedGuardedLanguage.Env Symbol
  | .intersection first second => ambient (IntersectSchedule.pairName (first, second))
  | _ => fun _ => False

/-- Every pair in the incoming recursive domain has canonical operand order. -/
def Ordered (pairs : List (Nat × Nat)) : Prop := ∀ pair ∈ pairs, pair.1 ≤ pair.2

/-- The initial empty recursive domain has canonical operand order. -/
theorem ordered_empty : Ordered [] := by intro pair member; cases member

/-- Actual source operand pairing always has canonical operand order. -/
theorem ordered_pair (first second : Nat) :
    (SourceRecursiveIntersectionControl.pair first second).1 ≤
      (SourceRecursiveIntersectionControl.pair first second).2 := by
  simp only [SourceRecursiveIntersectionControl.pair]
  omega

/-- Canonical domain extension retains operand order for every seen pair. -/
theorem ordered_extend (domain : IntersectionFlatMemoKeyDomain.DomainKey) (bindings : List Nat)
    (pair : Nat × Nat) (before : Ordered domain.seen) (ordered : pair.1 ≤ pair.2) :
    Ordered (SourceRecursiveIntersectionDomain.extend domain bindings pair).seen := by
  intro other member
  change other ∈ CanonicalClasses.sortedSet (pair :: domain.seen) at member
  have included := (CanonicalClasses.mem_sortedSet _ other).mp member
  rcases List.mem_cons.mp included with same | old
  · simpa only [same] using ordered
  · exact before other old

/-- A local pair override has exactly the schedule override on each permitted free name. -/
theorem bind_on_scope (pairs : List (Nat × Nat)) (ordered : Ordered pairs)
    (pair : Nat × Nat) (pairOrdered : pair.1 ≤ pair.2)
    (ambient : BinderLanguage.Env Symbol) (candidate : BinderLanguage.Lang Symbol)
    (name : Reference) (named : ∃ other ∈ pairs, name = .intersection other.1 other.2) :
    InternedGuardedLanguage.bind (environment ambient) (.intersection pair.1 pair.2) candidate name =
      environment (BinderLanguage.bind ambient (IntersectSchedule.pairName pair) candidate) name := by
  obtain ⟨other, member, rfl⟩ := named
  have exactName : IntersectSchedule.pairName other = IntersectSchedule.pairName pair ↔ other = pair := by
    constructor
    · exact IntersectSchedule.pairName_injective other pair (ordered other member) pairOrdered
    · intro same; rw [same]
  have exactReference : Reference.intersection other.1 other.2 = .intersection pair.1 pair.2 ↔ other = pair := by
    simp only [Reference.intersection.injEq, Prod.ext_iff]
  simp only [InternedGuardedLanguage.bind, environment, BinderLanguage.bind, exactReference, exactName]

/-- Coherent result scope transports the complete guarded body through a schedule binder override. -/
theorem meaning_bind (holds : Guard → Term Symbol → Bool) (value : Value Symbol Guard)
    (state : State Symbol Guard) (facts : Facts state) (available : Available state value)
    (pairs : List (Nat × Nat)) (ordered : Ordered pairs) (scope : Scope pairs value)
    (pair : Nat × Nat) (pairOrdered : pair.1 ≤ pair.2)
    (ambient : BinderLanguage.Env Symbol) (candidate : BinderLanguage.Lang Symbol) :
    InternedGuardedLanguage.meaning holds
        (InternedGuardedLanguage.bind (environment ambient) (.intersection pair.1 pair.2) candidate) value =
      InternedGuardedLanguage.meaning holds
        (environment (BinderLanguage.bind ambient (IntersectSchedule.pairName pair) candidate)) value := by
  apply InternedGuardedLanguage.meaning_free holds value state facts.coherent available
  intro name member
  exact bind_on_scope pairs ordered pair pairOrdered ambient candidate name (scope name member)

/-- An actual optional binder and the schedule binder preserve the same body correspondence. -/
theorem optionalBinder [DecidableEq (EdgeKey Symbol Guard)] (pair : Nat × Nat) (pairOrdered : pair.1 ≤ pair.2)
    (body : Value Symbol Guard) (shape : Binding.Shape (BinderLanguage.Payload Symbol))
    (state : State Symbol Guard) (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap state)
    (heap : InternedGuardedProbeHeap.Heap state) (available : Available state body)
    (pairs : List (Nat × Nat)) (ordered : Ordered pairs) (scope : Scope pairs body)
    (holds : Guard → Term Symbol → Bool)
    (bodyMeaning : ∀ ambient, InternedGuardedLanguage.meaning holds (environment ambient) body =
      BinderLanguage.meaning ambient shape)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (done : SourceRecursiveIntersectionMaybeMu.maybeMu pair body state = .done value after)
    (ambient : BinderLanguage.Env Symbol) :
    InternedGuardedLanguage.meaning holds (environment ambient) value =
      BinderLanguage.meaning ambient (IntersectSchedule.maybeMu pair shape) := by
  have actual := (SourceRecursiveIntersectionGuardedEffects.optionalBinder_checked pair body state
    semantic heap available).result value after done holds (environment ambient)
  rw [actual, IntersectSchedule.maybeMu, BinderLanguage.cleanup_exact, BinderLanguage.meaning]
  apply BinderLanguage.least_congr
  intro candidate term
  rw [meaning_bind holds body state semantic.1.normal.facts available pairs ordered scope pair pairOrdered,
    bodyMeaning]

end MicroCFTA.SourceRecursiveIntersectionScheduleEnvironment
