import MicroCFTA.SourceCurrentStoredMuProfileContract
import MicroCFTA.SourceCurrentStoredReconstruction
namespace MicroCFTA.ProfileContractIntegrationKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build ordinaryLevel)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedStoredSubstitution (Environment Replacements)
open InternedBinderProtocol (Reference)
open InternedRootProfile (profile Equivalent)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentStoredMuBinderChildLineage (bind)
open SourceCurrentStoredMuProfileContract (Correct shadow)
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

private def source : Syntax Nat Bool := .binder false (.binder true (.node [.mk 7 false [.var 1]]))
private def actual := build source [] empty
private def root : Value Nat Bool := match actual with | .done value _ => value | .pending .. => .empty
private def reader := actual.state
private def body := match root with | .mu _ body _ _ => body | _ => .empty
private def outerName : Reference := match root with | .mu entry _ _ _ => .interned entry.identity | _ => .depth
private def stored := (reader.nodeRecords (muKey body body)).getD .empty
private def entry : Interned InternedBinderProtocol.NodeKey :=
  match stored with | .mu entry _ _ _ => entry | _ => ⟨0,.node []⟩
private def environment : Environment Nat Bool := fun name =>
  if name = outerName then some (.reference (.uninterned 30))
  else if name = .uninterned 99 then some (.reference (.uninterned 88)) else none
private def used : Value Nat Bool → Prop
  | .mu entry body _ _ => .interned entry.identity ∈ body.free
  | _ => False
private theorem actual_done : build source [] empty = .done root reader := by cbv
private theorem ready : Ready reader := SourceEqualityRequiredCache.constructed source root reader actual_done
private theorem root_available : Available reader root :=
  (InternedFreshOrdinaryFacts.build_verified source [] empty InternedNestedFacts.empty_facts
    (by intro value impossible; cases impossible)).result root reader actual_done
private theorem body_available : Available reader body :=
  root_available.children body (by cbv; exact List.mem_cons_self)
private theorem installed : reader.nodeRecords (muKey body body) = some (.mu entry body body body) := by cbv
private theorem body_free : body.free = [outerName] := by cbv
private theorem inner_different : outerName ≠ .interned entry.identity := by cbv; intro impossible; cases impossible
private theorem ordinary_different : outerName ≠ .uninterned (ordinaryLevel body) := by cbv; intro impossible; cases impossible
private theorem correct : Correct entry body body body := by
  intro assignment replacement
  have same := SourceCurrentStoredProfileFunction.congr body reader ready.semantic.1.normal.facts.coherent body_available
    (shadow (.interned entry.identity) replacement assignment)
    (shadow (.uninterned (ordinaryLevel body)) replacement assignment) (by
      intro name member
      rw [body_free] at member
      obtain rfl := List.mem_singleton.mp member
      change (if outerName = .interned entry.identity then replacement else assignment outerName) =
        (if outerName = .uninterned (ordinaryLevel body) then replacement else assignment outerName)
      rw [ite_eq_right inner_different,ite_eq_right ordinary_different])
  rw [same]
  exact InternedProfileEquivalence.refl _
private theorem replacements : Replacements reader environment := by
  intro name value found
  dsimp only [environment] at found
  split at found
  · cases found
    exact InternedNestedProvenance.ordinary_available _ 30
  · split at found
    · cases found
      exact InternedNestedProvenance.ordinary_available _ 88
    · cases found
private theorem bound_replacements (name : Reference) (state : State Nat Bool)
    (rootAvailable : Available state root) (prior : Replacements state environment) :
    Replacements state (bind name root environment) := by
  intro queried value found
  dsimp only [SourceCurrentStoredMuBinderChildLineage.bind] at found
  split at found
  · cases found
    exact rootAvailable
  · exact prior queried value found
private theorem checked_witness :
    build source [] empty = .done root reader ∧ Ready reader ∧ Available reader root ∧ used root ∧
    root.free = [] ∧ root.referenceOf ≠ .empty ∧
    reader.nodeRecords (muKey body body) = some (.mu entry body body body) ∧
    body.free = [outerName] ∧ outerName ≠ .interned entry.identity ∧
    outerName ≠ .uninterned (ordinaryLevel body) ∧ Correct entry body body body ∧
    environment outerName = some (.reference (.uninterned 30)) ∧
    environment (.uninterned 99) = some (.reference (.uninterned 88)) ∧
    ∃ left middle right after,
      execute body (bind (.interned entry.identity) root environment) reader = .done left middle ∧
      execute body (bind (.uninterned (ordinaryLevel body)) root environment) middle = .done right after ∧
      Keeps reader middle ∧ Keeps middle after ∧ Available after left ∧ Available after right ∧
      Equivalent (profile left) (profile right) ∧
      after.nodeRecords (muKey body body) = some (.mu entry body body body) := by
  refine ⟨actual_done,ready,root_available,(by cbv; exact List.mem_cons_self),(by cbv),
    (by cbv; intro impossible; cases impossible),installed,body_free,inner_different,ordinary_different,correct,
    (by cbv),(by cbv),?_⟩
  obtain ⟨left,middle,firstDone,first,leftAvailable,_⟩ := SourceCurrentStoredReconstruction.execute body
    (bind (.interned entry.identity) root environment) reader ready body_available
    (bound_replacements _ reader root_available replacements)
  have laterReplacements : Replacements middle environment := by
    intro name value found
    exact first.available value (replacements name value found)
  obtain ⟨right,after,secondDone,second,rightAvailable,_⟩ := SourceCurrentStoredReconstruction.execute body
    (bind (.uninterned (ordinaryLevel body)) root environment) middle first.ready (first.available body body_available)
    (bound_replacements _ middle (first.available root root_available) laterReplacements)
  have compared := SourceCurrentStoredMuProfileContract.execute entry body body body correct environment root
    reader middle ready first.ready body_available (first.available body body_available)
    root_available (first.available root root_available) replacements laterReplacements left right middle after firstDone secondDone
  exact ⟨left,middle,right,after,firstDone,secondDone,first,second,second.available left leftAvailable,rightAvailable,compared,
    second.growth.nodeRecords _ _ (first.growth.nodeRecords _ _ installed)⟩

theorem installed_parametric_contract :
    build source [] empty = .done root reader ∧ Ready reader ∧ Available reader root ∧ used root ∧
    root.free = [] ∧ root.referenceOf ≠ .empty ∧
    reader.nodeRecords (muKey body body) = some (.mu entry body body body) ∧
    body.free = [outerName] ∧ outerName ≠ .interned entry.identity ∧
    outerName ≠ .uninterned (ordinaryLevel body) ∧ Correct entry body body body ∧
    environment outerName = some (.reference (.uninterned 30)) ∧
    environment (.uninterned 99) = some (.reference (.uninterned 88)) ∧
    ∃ left middle right after,
      execute body (bind (.interned entry.identity) root environment) reader = .done left middle ∧
      execute body (bind (.uninterned (ordinaryLevel body)) root environment) middle = .done right after ∧
      Keeps reader middle ∧ Keeps middle after ∧ Available after left ∧ Available after right ∧
      Equivalent (profile left) (profile right) ∧
      after.nodeRecords (muKey body body) = some (.mu entry body body body) := checked_witness

end MicroCFTA.ProfileContractIntegrationKernels

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.ProfileContractIntegrationKernels.installed_parametric_contract
#print MicroCFTA.ProfileContractIntegrationKernels.installed_parametric_contract
#print axioms MicroCFTA.ProfileContractIntegrationKernels.installed_parametric_contract
