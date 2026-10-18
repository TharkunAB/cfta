import MicroCFTA.SourceCurrentStoredRootDeletionFilter
import MicroCFTA.SourceCurrentStoredMuProfileContract
import MicroCFTA.SourceCurrentStoredRootDeletionConstruction
import MicroCFTA.SourceCurrentPublicationHeapInduction

/-!
# Original root observations for a stored recursive payload

The contract compares deletion of original root references under arbitrary
assignments. Each side tags its own local reference separately from external
names. It also retains the exact standalone-reference tag. General source
publication must still derive this contract.
-/
namespace MicroCFTA.SourceCurrentStoredMuRootContract
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedBinderProtocol (Reference NodeKey)
open InternedRootProfile (Profile Equivalent)
open InternedStoredMuOrigins (Normal)
open InternedFreshOrdinaryConstruction (ordinaryLevel)
open SourceCurrentStoredProfileFunction (denote)
open SourceCurrentStoredRootDeletion (deleted)
open SourceCurrentStoredMuProfileContract (shadow)

/-- None identifies the local reference. Some retains an external name. -/
def tag (own name : Reference) : Option Reference := if name = own then none else some name

/-- A standalone reference retains its exact local or external tag. -/
def bare (own : Reference) : Value Symbol Guard → Option (Option Reference)
  | .reference name => some (tag own name)
  | _ => none

/-- The payload retains all original root deletions and its exact bare-root tag. -/
def Correct (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) : Prop :=
  (∀ (assignment : Reference → Profile) (replacement : Profile) (cuts : Option Reference → Bool),
    Equivalent
      (deleted (fun name => cuts (tag (.interned entry.identity) name)) body
        (shadow (.interned entry.identity) replacement assignment))
      (deleted (fun name => cuts (tag (.uninterned (ordinaryLevel depth)) name)) ordinary
        (shadow (.uninterned (ordinaryLevel depth)) replacement assignment))) ∧
  bare (.interned entry.identity) body = bare (.uninterned (ordinaryLevel depth)) ordinary

/-- Tagging preserves the distinction between every pair of concrete names. -/
theorem tag_injective (own : Reference) : Function.Injective (tag own) := by
  intro first second same
  by_cases one : first = own <;> by_cases two : second = own <;> simp_all [tag]

private theorem tagged_bare (own name : Reference) (value : Value Symbol Guard) :
    bare own value = some (tag own name) ↔ value = .reference name := by
  cases value with
  | reference selected =>
      simp only [bare,Option.some.injEq,Value.reference.injEq]
      exact ⟨fun same => tag_injective own same,fun same => congrArg (tag own) same⟩
  | empty | node | union | mu => simp [bare]

private theorem singleton_cut (own selected : Reference) :
    (fun name => tag own name == tag own selected) = (fun name => name == selected) := by
  funext name
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  exact ⟨fun same => tag_injective own same,fun same => congrArg (tag own) same⟩

/-- With resident normalized inputs, the root contract supplies the prior full profile contract. -/
theorem profiles (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (correct : Correct entry body depth ordinary) (state : State Symbol Guard)
    (normal : Normal state) (bodyAvailable : Available state body) (ordinaryAvailable : Available state ordinary) :
    SourceCurrentStoredMuProfileContract.Correct entry body depth ordinary := by
  intro assignment replacement
  have matched := correct.1 assignment replacement (fun _ => false)
  change Equivalent (deleted (fun _ => false) body _)
    (deleted (fun _ => false) ordinary _) at matched
  rw [SourceCurrentStoredRootDeletion.uncut body _ state normal bodyAvailable,
    SourceCurrentStoredRootDeletion.uncut ordinary _ state normal ordinaryAvailable] at matched
  exact matched

/-- Aligned local or external filters preserve the complete assigned profile comparison. -/
theorem filtered_profiles (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (correct : Correct entry body depth ordinary) (state : State Symbol Guard)
    (normal : Normal state) (bodyAvailable : Available state body) (ordinaryAvailable : Available state ordinary)
    (firstName secondName : Reference)
    (aligned : tag (.interned entry.identity) firstName = tag (.uninterned (ordinaryLevel depth)) secondName)
    (assignment : Reference → Profile) (replacement : Profile) :
    Equivalent
      (SourceCurrentStoredFilteredProfile.filtered firstName body
        (shadow (.interned entry.identity) replacement assignment))
      (SourceCurrentStoredFilteredProfile.filtered secondName ordinary
        (shadow (.uninterned (ordinaryLevel depth)) replacement assignment)) := by
  let firstOwn := Reference.interned entry.identity
  let secondOwn := Reference.uninterned (ordinaryLevel depth)
  have sameBare : body = .reference firstName ↔ ordinary = .reference secondName := by
    rw [← tagged_bare firstOwn firstName body,correct.2,aligned]
    exact tagged_bare secondOwn secondName ordinary
  have sameTest : (body.referenceOf == .ref firstName) = (ordinary.referenceOf == .ref secondName) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [beq_iff_eq,referenceOf_self_iff] using sameBare
  have cut := correct.1 assignment replacement (fun label => label == tag firstOwn firstName)
  change Equivalent (deleted (fun name => tag firstOwn name == tag firstOwn firstName) body _)
    (deleted (fun name => tag secondOwn name == tag firstOwn firstName) ordinary _) at cut
  rw [singleton_cut firstOwn firstName,aligned,singleton_cut secondOwn secondName] at cut
  rw [SourceCurrentStoredRootDeletionFilter.singleton firstName body _ state normal bodyAvailable,
    SourceCurrentStoredRootDeletionFilter.singleton secondName ordinary _ state normal ordinaryAvailable,← sameTest]
  cases chosen : body.referenceOf == .ref firstName with
  | false => simpa only [chosen,Bool.false_eq_true,ite_false] using cut
  | true =>
      have firstBare := (referenceOf_self_iff firstName body).mp (eq_of_beq chosen)
      have secondBare := sameBare.mp firstBare
      have complete := profiles entry body depth ordinary correct state normal bodyAvailable ordinaryAvailable assignment replacement
      rw [firstBare,secondBare,SourceCurrentStoredProfileFunction.reference,
        SourceCurrentStoredProfileFunction.reference] at complete
      simpa only [chosen,ite_true] using complete

/-- A normalized root-contract heap supplies all prior parametric profile contracts. -/
theorem heap_profiles (state : State Symbol Guard) (normal : Normal state)
    (heap : SourceCurrentPublicationHeapInduction.Heap Correct state) :
    SourceCurrentPublicationHeapInduction.Heap SourceCurrentStoredMuProfileContract.Correct state := by
  intro key entry body depth ordinary present
  have available := normal.facts.cached.nodes key _ present
  exact profiles entry body depth ordinary (heap key entry body depth ordinary present) state normal
    (available.children body (by simp [children])) (available.children ordinary (by simp [children]))

/-- Actual root filters preserve aligned observations without a recursive readiness premise. -/
theorem actual_filtered_profiles [DecidableEq (EdgeKey Symbol Guard)]
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (correct : Correct entry body depth ordinary) (state : State Symbol Guard)
    (normal : Normal state) (bodyAvailable : Available state body) (ordinaryAvailable : Available state ordinary)
    (firstName secondName : Reference)
    (aligned : tag (.interned entry.identity) firstName = tag (.uninterned (ordinaryLevel depth)) secondName)
    (assignment : Reference → Profile) (replacement : Profile) :
    Equivalent
      (denote (run (withoutSelfReference firstName body) state).1
        (shadow (.interned entry.identity) replacement assignment))
      (denote (run (withoutSelfReference secondName ordinary) state).1
        (shadow (.uninterned (ordinaryLevel depth)) replacement assignment)) := by
  have first := SourceCurrentStoredRootDeletionConstruction.filter_profile firstName body
    (shadow (.interned entry.identity) replacement assignment) state normal bodyAvailable
  have second := SourceCurrentStoredRootDeletionConstruction.filter_profile secondName ordinary
    (shadow (.uninterned (ordinaryLevel depth)) replacement assignment) state normal ordinaryAvailable
  rw [← SourceCurrentStoredRootDeletionFilter.singleton firstName body _ state normal bodyAvailable] at first
  rw [← SourceCurrentStoredRootDeletionFilter.singleton secondName ordinary _ state normal ordinaryAvailable] at second
  have middle := filtered_profiles entry body depth ordinary correct state normal bodyAvailable ordinaryAvailable
    firstName secondName aligned assignment replacement
  exact ⟨first.1.trans (middle.1.trans second.1.symm),
    fun name => (first.2 name).trans ((middle.2 name).trans (second.2 name).symm)⟩

end MicroCFTA.SourceCurrentStoredMuRootContract
