import MicroCFTA.SourceCurrentReaderReplacementSlots
import MicroCFTA.SourceCurrentUsedBinderAliasTransport
import MicroCFTA.InternedFreshOrdinaryDependencies

/-!
# One replacement map for actual publication callbacks

Actual filtered callbacks exclude each other's local name. One sparse map
can therefore retain both original stored computations. The same map pairs
the two local input lists under any supplied reflexive relation.
The result does not compare completed binder outputs or change the reader.
-/
namespace MicroCFTA.SourceCurrentPublicationSharedReplacements
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedBinderProtocol (Reference)
open InternedStoredSubstitution (Environment)
open InternedFreshOrdinaryConstruction (ordinaryLevel)
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentStoredMuBinderChildLineage (bind)
open SourceCurrentReaderReplacementSlots (Slot Paired)

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- One sparse map binds both actual local names and retains the outer map elsewhere. -/
def shared (event : Publication (Symbol := Symbol) (Guard := Guard))
    (firstValue secondValue : Value Symbol Guard) (environment : Environment Symbol Guard) :
    Environment Symbol Guard :=
  bind (.interned event.entry.identity) firstValue
    (bind (.uninterned (ordinaryLevel event.depth)) secondValue environment)

/-- Each actual filtered callback excludes the other callback's local name. -/
theorem cross_absence (event : Publication (Symbol := Symbol) (Guard := Guard)) :
    .uninterned (ordinaryLevel event.depth) ∉ event.body.free ∧
      .interned event.entry.identity ∉ event.ordinary.free := by
  obtain ⟨forward,backward⟩ := SourceCurrentUsedBinderAliasTransport.publication_filtered event
  constructor
  · intro member
    obtain ⟨name,_,paired⟩ := backward _ member
    rcases paired with ⟨_,impossible⟩ | ⟨same,different,_⟩
    · cases impossible
    · exact different same
  · intro member
    obtain ⟨name,_,paired⟩ := forward _ member
    rcases paired with ⟨impossible,_⟩ | ⟨same,_,different⟩
    · cases impossible
    · exact different same.symm

/-- Both original sparse substitutions have the exact outcome of the shared map at the same heap. -/
theorem substitutions (event : Publication (Symbol := Symbol) (Guard := Guard))
    (firstValue secondValue : Value Symbol Guard) (environment : Environment Symbol Guard)
    (current : State Symbol Guard) (coherent : Coherent current)
    (bodyAvailable : Available current event.body) (ordinaryAvailable : Available current event.ordinary) :
    execute event.body (bind (.interned event.entry.identity) firstValue environment) current =
      execute event.body (shared event firstValue secondValue environment) current ∧
    execute event.ordinary (bind (.uninterned (ordinaryLevel event.depth)) secondValue environment) current =
      execute event.ordinary (shared event firstValue secondValue environment) current := by
  have absent := cross_absence event
  constructor
  · apply InternedFreshOrdinaryStoredSubstitution.execute_congr _ _ _ current coherent bodyAvailable
    intro name member
    have different : name ≠ .uninterned (ordinaryLevel event.depth) :=
      fun same => absent.1 (same ▸ member)
    simp only [shared,bind,different,ite_false]
  · apply InternedFreshOrdinaryStoredSubstitution.execute_congr _ _ _ current coherent ordinaryAvailable
    intro name member
    have different : name ≠ .interned event.entry.identity := fun same => absent.2 (same ▸ member)
    simp only [shared,bind,different,ite_false]

/-- Both actual local input lists are paired under the shared map and the supplied relation. -/
theorem paired (event : Publication (Symbol := Symbol) (Guard := Guard))
    (relation : Value Symbol Guard → Value Symbol Guard → Prop)
    (reflexive : ∀ value, relation value value)
    (firstValue secondValue : Value Symbol Guard) (environment : Environment Symbol Guard)
    (related : relation firstValue secondValue) :
    Paired relation (shared event firstValue secondValue environment)
      (shared event firstValue secondValue environment)
      (.reference (.interned event.entry.identity) :: event.environment)
      (.reference (.uninterned (ordinaryLevel event.depth)) :: event.environment) := by
  refine .cons ?_ ?_
  · simpa only [Slot,shared,bind,ite_true,Reference.uninterned.injEq,
      reduceCtorEq,ite_false,Option.getD_some] using related
  · have fixed (values : List (Value Symbol Guard)) :
        All₂ (Slot relation (shared event firstValue secondValue environment)
          (shared event firstValue secondValue environment)) values values := by
      induction values with
      | nil => exact .nil
      | cons value rest ih =>
          refine .cons ?_ ih
          cases value with
          | reference name => exact reflexive _
          | empty | node | union | mu => exact ⟨rfl,fun _ _ => rfl⟩
    exact fixed event.environment

end MicroCFTA.SourceCurrentPublicationSharedReplacements
