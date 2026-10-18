import MicroCFTA.SourceCurrentStoredProfileFunction
import MicroCFTA.SourceCurrentPublicationHeapInduction
import MicroCFTA.SourceCurrentStoredMuBinderChildLineage

/-!
# Parametric root profiles for a stored recursive payload

The contract compares the stored body and its ordinary probe under one
arbitrary outer assignment. Each side binds its own local reference to
the same profile. Actual substitution transfers this contract to two
completed executions. General source publication must still prove it.
-/
namespace MicroCFTA.SourceCurrentStoredMuProfileContract
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedBinderProtocol (Reference NodeKey)
open InternedRootProfile (Profile profile Equivalent)
open InternedStoredSubstitution (Environment Replacements)
open InternedFreshOrdinaryConstruction (ordinaryLevel)
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceCurrentStoredMuBinderChildLineage (bind)
open SourceEqualityRequiredCache (Ready)

/-- The local profile shadows the outer assignment at one exact reference. -/
def shadow (name : Reference) (local : Profile) (assignment : Reference → Profile) : Reference → Profile :=
  fun queried => if queried = name then local else assignment queried

/-- Stored body and ordinary probe agree under every common outer and local assignment. -/
def Correct (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) : Prop :=
  ∀ assignment local,
    Equivalent
      (SourceCurrentStoredProfileFunction.denote body (shadow (.interned entry.identity) local assignment))
      (SourceCurrentStoredProfileFunction.denote ordinary (shadow (.uninterned (ordinaryLevel depth)) local assignment))

private theorem bound_replacements (name : Reference) (local : Value Symbol Guard)
    (environment : Environment Symbol Guard) (state : State Symbol Guard)
    (available : Available state local) (replacements : Replacements state environment) :
    Replacements state (bind name local environment) := by
  intro queried value found
  dsimp only [bind] at found
  split at found
  · cases found
    exact available
  · exact replacements queried value found

private theorem bound_profile (name : Reference) (local : Value Symbol Guard)
    (environment : Environment Symbol Guard) :
    (fun queried => profile (((bind name local environment) queried).getD (.reference queried))) =
      shadow name (profile local) (fun queried => profile ((environment queried).getD (.reference queried))) := by
  funext queried
  simp only [bind,shadow]
  split <;> rfl

/-- The payload contract compares actual completed calls in independently ready readers. -/
theorem execute [DecidableEq (EdgeKey Symbol Guard)]
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (correct : Correct entry body depth ordinary) (environment : Environment Symbol Guard)
    (local : Value Symbol Guard) (first second : State Symbol Guard)
    (firstReady : Ready first) (secondReady : Ready second)
    (bodyAvailable : Available first body) (ordinaryAvailable : Available second ordinary)
    (firstLocal : Available first local) (secondLocal : Available second local)
    (firstReplacements : Replacements first environment) (secondReplacements : Replacements second environment)
    (left right : Value Symbol Guard) (afterLeft afterRight : State Symbol Guard)
    (bodyDone : InternedFreshOrdinaryStoredSubstitution.execute body
      (bind (.interned entry.identity) local environment) first = .done left afterLeft)
    (ordinaryDone : InternedFreshOrdinaryStoredSubstitution.execute ordinary
      (bind (.uninterned (ordinaryLevel depth)) local environment) second = .done right afterRight) :
    Equivalent (profile left) (profile right) := by
  have leftProfile := SourceCurrentStoredProfileFunction.execute body _ first firstReady bodyAvailable
    (bound_replacements _ local environment first firstLocal firstReplacements) left afterLeft bodyDone
  have rightProfile := SourceCurrentStoredProfileFunction.execute ordinary _ second secondReady ordinaryAvailable
    (bound_replacements _ local environment second secondLocal secondReplacements) right afterRight ordinaryDone
  rw [bound_profile] at leftProfile rightProfile
  have middle := correct (fun queried => profile ((environment queried).getD (.reference queried))) (profile local)
  exact ⟨leftProfile.1.trans (middle.1.trans rightProfile.1.symm),
    fun name => (leftProfile.2 name).trans ((middle.2 name).trans (rightProfile.2 name).symm)⟩

end MicroCFTA.SourceCurrentStoredMuProfileContract
