import MicroCFTA.SourceCurrentCausalHistoryProfiles
import MicroCFTA.SourceCurrentStoredReconstruction

/-!
# Complete readback of a causal selected Mu payload

Actual reader history proves the selected payload's profile contract.
Both reconstructions use one arbitrary outer map and local replacement.
The producer retains their exact sequential calls and physical effects.
Empty replacements are allowed. Deeper guarded observations are separate.
-/
namespace MicroCFTA.SourceCurrentCausalStoredMuReadback
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (Reference NodeKey)
open InternedRootProfile (profile Equivalent)
open InternedStoredSubstitution (Environment Replacements)
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceCurrentStoredMuBinderChildLineage (bind)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentNativeMuPublication (History)

private theorem bound_replacements (name : Reference) (replacement : Value Symbol Guard)
    (environment : Environment Symbol Guard) (state : State Symbol Guard)
    (available : Available state replacement) (replacements : Replacements state environment) :
    Replacements state (bind name replacement environment) := by
  intro queried value found
  dsimp only [SourceCurrentStoredMuBinderChildLineage.bind] at found
  split at found
  · cases found
    exact available
  · exact replacements queried value found

/-- Initial causal reader facts construct both payload calls and derive their profile and Empty agreement. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)]
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (reader : State Symbol Guard) (ready : Ready reader) (history : History empty reader)
    (present : reader.nodeRecords key = some (.mu entry body depth ordinary))
    (environment : Environment Symbol Guard) (replacements : Replacements reader environment)
    (replacement : Value Symbol Guard) (localAvailable : Available reader replacement) :
    ∃ left middle right after,
      execute body (bind (.interned entry.identity) replacement environment) reader = .done left middle ∧
      execute ordinary (bind (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) replacement environment)
        middle = .done right after ∧
      Keeps reader middle ∧ Keeps middle after ∧ Available after left ∧ Available after right ∧
      Nonempty (History reader middle) ∧ Nonempty (History middle after) ∧
      middle.nodeRecords key = some (.mu entry body depth ordinary) ∧
      after.nodeRecords key = some (.mu entry body depth ordinary) ∧
      Equivalent (profile left) (profile right) ∧
      (left.referenceOf == .empty) = (right.referenceOf == .empty) := by
  have correct := SourceCurrentCausalHistoryProfiles.heap reader history key entry body depth ordinary present
  have selected := ready.semantic.1.normal.facts.cached.nodes key _ present
  have bodyAvailable := selected.children body (by simp [children])
  have ordinaryAvailable := selected.children ordinary (by simp [children])
  obtain ⟨left,middle,firstDone,first,leftAvailable,firstHistory⟩ :=
    SourceCurrentStoredReconstruction.execute body (bind (.interned entry.identity) replacement environment)
      reader ready bodyAvailable (bound_replacements _ replacement environment reader localAvailable replacements)
  have middleReplacements : Replacements middle environment := by
    intro name value found
    exact first.available value (replacements name value found)
  obtain ⟨right,after,secondDone,second,rightAvailable,secondHistory⟩ :=
    SourceCurrentStoredReconstruction.execute ordinary
      (bind (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) replacement environment)
      middle first.ready (first.available ordinary ordinaryAvailable)
      (bound_replacements _ replacement environment middle (first.available replacement localAvailable) middleReplacements)
  have compared := SourceCurrentStoredMuProfileContract.execute entry body depth ordinary correct environment replacement
    reader middle ready first.ready bodyAvailable (first.available ordinary ordinaryAvailable)
    localAvailable (first.available replacement localAvailable) replacements middleReplacements
    left right middle after firstDone secondDone
  have leftAfter := second.available left leftAvailable
  have equal := InternedProfileComposition.isEmpty_same compared
  rw [InternedRootProfileNode.isEmpty_profile left after second.ready.semantic.1.normal.proper leftAfter,
    InternedRootProfileNode.isEmpty_profile right after second.ready.semantic.1.normal.proper rightAvailable] at equal
  exact ⟨left,middle,right,after,firstDone,secondDone,first,second,leftAfter,rightAvailable,
    firstHistory,secondHistory,first.growth.nodeRecords key _ present,
    second.growth.nodeRecords key _ (first.growth.nodeRecords key _ present),compared,equal⟩

end MicroCFTA.SourceCurrentCausalStoredMuReadback
