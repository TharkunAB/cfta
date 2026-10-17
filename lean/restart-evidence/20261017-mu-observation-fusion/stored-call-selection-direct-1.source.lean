import MicroCFTA.SourceCurrentStoredCallsReplay
import MicroCFTA.InternedUnionRetention

/-!
# Warm stored calls under source-list selection

Actual warm calls supply one result for each source value. A list with the
same complete source-value membership can reuse those calls. Its results
have the same complete membership. Source coherence justifies selection
by distinctNodes. These theorems verify supplied warm calls. They do not
assume a desired output relation or a new successful execution.
-/
namespace MicroCFTA.SourceCurrentStoredCallSelection
open InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Outcome)
open InternedStoredSubstitution (Environment)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedNestedProvenance (Values)
open SourceCurrentStoredSubstitutionCalls (Calls)
open Language

private theorem left_member {A B : Type} {relation : A → B → Prop} {first : List A} {second : List B}
    (paired : All₂ relation first second) (value : A) (member : value ∈ first) :
    ∃ other ∈ second, relation value other := by
  induction paired with
  | nil => cases member
  | cons pair _ ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨_,List.mem_cons_self,pair⟩
      · obtain ⟨other,present,related⟩ := ih later
        exact ⟨other,List.mem_cons_of_mem _ present,related⟩

private theorem right_member {A B : Type} {relation : A → B → Prop} {first : List A} {second : List B}
    (paired : All₂ relation first second) (value : B) (member : value ∈ second) :
    ∃ other ∈ first, relation other value := by
  induction paired with
  | nil => cases member
  | cons pair _ ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨_,List.mem_cons_self,pair⟩
      · obtain ⟨other,present,related⟩ := ih later
        exact ⟨other,List.mem_cons_of_mem _ present,related⟩

private theorem assemble [DecidableEq (EdgeKey Symbol Guard)]
    (environment : Environment Symbol Guard) (common : State Symbol Guard)
    (originals outputs selected : List (Value Symbol Guard))
    (actual : All₂ (fun original output => execute original environment common = .done output common) originals outputs)
    (included : ∀ value ∈ selected, value ∈ originals) :
    ∃ results, All₂ (fun original output => execute original environment common = .done output common) selected results ∧
      Calls environment selected common results common := by
  induction selected with
  | nil => exact ⟨[],.nil,.nil common⟩
  | cons original selected ih =>
      obtain ⟨output,_,called⟩ := left_member actual original (included original List.mem_cons_self)
      obtain ⟨results,paired,calls⟩ := ih (fun value member => included value (List.mem_cons_of_mem _ member))
      exact ⟨output::results,.cons called paired,.cons original selected common common common output results called calls⟩

/-- A source list with the same complete membership derives actual warm calls and the same complete output membership. -/
theorem select [DecidableEq (EdgeKey Symbol Guard)]
    (environment : Environment Symbol Guard) (common : State Symbol Guard)
    (originals outputs selected : List (Value Symbol Guard))
    (actual : All₂ (fun original output => execute original environment common = .done output common) originals outputs)
    (membership : ∀ value, value ∈ selected ↔ value ∈ originals) :
    ∃ results, All₂ (fun original output => execute original environment common = .done output common) selected results ∧
      Calls environment selected common results common ∧ ∀ value, value ∈ results ↔ value ∈ outputs := by
  obtain ⟨results,paired,calls⟩ := assemble environment common originals outputs selected actual
    (fun value member => (membership value).mp member)
  refine ⟨results,paired,calls,?_⟩
  intro value
  constructor
  · intro member
    obtain ⟨original,present,called⟩ := right_member paired value member
    obtain ⟨output,included,other⟩ := left_member actual original ((membership original).mp present)
    have same := (Outcome.done.inj (called.symm.trans other)).1
    simpa only [same] using included
  · intro member
    obtain ⟨original,present,called⟩ := right_member actual value member
    obtain ⟨output,included,other⟩ := left_member paired original ((membership original).mpr present)
    have same := (Outcome.done.inj (called.symm.trans other)).1
    simpa only [same] using included

/-- Physical distinct-node selection retains every complete source value and therefore every warm output value. -/
theorem distinct [DecidableEq (EdgeKey Symbol Guard)]
    (environment : Environment Symbol Guard) (common : State Symbol Guard)
    (originals outputs : List (Value Symbol Guard)) (facts : InternedNestedFacts.Facts common)
    (available : Values common originals)
    (actual : All₂ (fun original output => execute original environment common = .done output common) originals outputs) :
    ∃ results, All₂ (fun original output => execute original environment common = .done output common)
        (distinctNodes originals) results ∧
      Calls environment (distinctNodes originals) common results common ∧
      ∀ value, value ∈ results ↔ value ∈ outputs := by
  apply select environment common originals outputs (distinctNodes originals) actual
  intro value
  exact ⟨distinctNodes_member originals value,
    InternedUnionRetention.distinctNodes_retains common facts.coherent originals
      (fun value member => (available value member).resident) value⟩

end MicroCFTA.SourceCurrentStoredCallSelection
