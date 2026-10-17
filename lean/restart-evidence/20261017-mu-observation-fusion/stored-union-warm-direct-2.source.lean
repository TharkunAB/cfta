import MicroCFTA.SourceCurrentStoredUnionObservations
import MicroCFTA.SourceCurrentStoredCallsReplay
import MicroCFTA.SourceCurrentStoredOrdinaryUnionObservations
import MicroCFTA.InternedNormalizedUnionReplay

/-!
# Warm reconstruction after actual union selection

The selected source list is the literal flattening and identity selection
of the original inputs. No flattening fixed-point premise is required.
Actual warm member calls and an actual warm normalized-root call determine
the same finite open observations. The proof retains full cached union
payloads and delegates the ordinary-row branch to its actual expansion.
-/
namespace MicroCFTA.SourceCurrentStoredUnionWarm
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Outcome)
open InternedStoredSubstitution (Environment Replacements)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedNestedProvenance (Values)
open InternedNestedFacts (Facts)
open InternedBinderProtocol (NodeKey)
open SourceEqualityRequiredCache (Ready Ordinary)
open SourceCurrentOpenObservations (Same)
open Language

private theorem paired_equal [DecidableEq (EdgeKey Symbol Guard)]
    (environment : Environment Symbol Guard) (common : State Symbol Guard)
    {originals first second : List (Value Symbol Guard)}
    (left : All₂ (fun original output => execute original environment common = .done output common) originals first)
    (right : All₂ (fun original output => execute original environment common = .done output common) originals second) :
    first = second := by
  induction left generalizing second with
  | nil => cases right; rfl
  | cons called rest ih =>
      cases right with
      | cons other later =>
          have head := (Outcome.done.inj (called.symm.trans other)).1
          exact congr (congrArg List.cons head) (ih later)

private theorem flatten_atoms (values : List (Value Symbol Guard))
    (single : ∀ value ∈ values, unionMembers value = [value]) : values.flatMap unionMembers = values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp only [List.flatMap_cons,single value List.mem_cons_self,List.singleton_append]
      exact congrArg (List.cons value) (ih (fun value member => single value (List.mem_cons_of_mem _ member)))

private theorem union_payload (members : List (Value Symbol Guard)) (common : State Symbol Guard)
    (facts : Facts common) (available : Values common members) (value : Value Symbol Guard)
    (actual : nodeStep (.union (members.map Value.referenceOf))
      (fun entry => .union entry members (maximumDepth members) (childFree members)) common = (value,common)) :
    ∃ entry, value = .union entry members (maximumDepth members) (childFree members) ∧ Available common value := by
  let key := NodeKey.union (members.map Value.referenceOf)
  let identify := fun entry => Value.union entry members (maximumDepth members) (childFree members)
  have present := (nodeStep_correct key identify common facts.coherent.valid).2.2
  rw [actual] at present
  have output := facts.cached.nodes key value present
  obtain ⟨entry,fields⟩ := InternedGateRank.requested_fields key identify common facts.coherent
    (fun _ _ => ⟨rfl,rfl,rfl,rfl⟩)
  rw [actual] at fields
  change NodeFields key entry value at fields
  cases value with
  | empty | reference | node | mu => simp [NodeFields,key,muKey] at fields
  | union cachedEntry originals level free =>
      have same := InternedNormalizationFree.value_lists_equal common facts.coherent members originals
        (fun value member => (available value member).resident)
        (fun value member => (output.children value member).resident) (NodeKey.union.inj fields.2.1)
      simp only [NodeFields] at fields
      refine ⟨cachedEntry,?_,output⟩
      rw [same,fields.2.2.1,fields.2.2.2]

/-- Actual union selection and warm calls give the same open observations without a flattening fixed-point premise. -/
theorem warm [DecidableEq (EdgeKey Symbol Guard)] (environment : Environment Symbol Guard)
    (common : State Symbol Guard) (originalInputs selected outputs : List (Value Symbol Guard))
    (normalized result : Value Symbol Guard) (ready : Ready common) (available : Values common selected)
    (replacements : Replacements common environment)
    (selection : distinctNodes (originalInputs.flatMap unionMembers) = selected)
    (paired : All₂ (fun original output => execute original environment common = .done output common) selected outputs)
    (made : run (makeUnion originalInputs) common = (normalized,common))
    (called : execute normalized environment common = .done result common) :
    ∀ depth view, Same depth view [result] outputs := by
  cases selected with
  | nil =>
      cases paired
      have value : normalized = .empty := by
        have same := congrArg Prod.fst made
        simpa only [makeUnion,selection,run] using same.symm
      subst normalized
      have same := (Outcome.done.inj
        (called.symm.trans (SourceCurrentStoredUnionObservations.closed .empty environment common rfl))).1
      subst result
      intro depth view
      have emptySame := SourceCurrentOpenObservationConstructors.makeUnion_normalize depth common view
        ready.semantic.1.normal.facts ready.semantic.1.normal.live [] (fun value member => by cases member)
      simpa only [makeUnion,List.flatMap_nil,distinctNodes,run] using emptySame
  | cons first rest =>
      cases rest with
      | nil =>
          cases paired with
          | cons head tail =>
              cases tail
              have value : normalized = first := by
                have same := congrArg Prod.fst made
                simpa only [makeUnion,selection,run] using same.symm
              subst normalized
              have same := (Outcome.done.inj (called.symm.trans head)).1
              subst result
              exact fun depth view => Same.refl depth view _
      | cons second tail =>
          cases ordinary : ordinaryEdges (first::second::tail) with
          | some rows =>
              have allNodes : ∀ value ∈ first::second::tail, ∃ entry edges level free,
                  value = .node entry edges level free := by
                intro value member
                obtain ⟨entry,edges,level,free,same,_⟩ :=
                  InternedUnionDescendants.ordinaryEdges_contains _ rows ordinary value member
                exact ⟨entry,edges,level,free,same⟩
              have flat := flatten_atoms (first::second::tail) (by
                intro value member
                obtain ⟨entry,edges,level,free,rfl⟩ := allNodes value member
                rfl)
              have distinct : distinctNodes (first::second::tail) = first::second::tail := by
                apply InternedNormalizedUnionReplay.distinct_of_nodup
                rw [←selection]
                exact InternedUnionNormalForm.distinctNodes_nodup _
              have sameWork : makeUnion (first::second::tail) = makeUnion originalInputs := by
                simp only [makeUnion,flat,distinct,selection]
              exact SourceCurrentStoredOrdinaryUnionObservations.warm ready available replacements
                (fun value member => by obtain ⟨entry,edges,level,free,rfl⟩ := allNodes value member; trivial)
                paired (by rw [sameWork]; exact made) called
          | none =>
              have step : nodeStep (.union ((first::second::tail).map Value.referenceOf))
                  (fun entry => .union entry (first::second::tail) (maximumDepth (first::second::tail))
                    (childFree (first::second::tail))) common = (normalized,common) := by
                simpa only [makeUnion,selection,ordinary,run] using made
              obtain ⟨entry,shape,outputAvailable⟩ := union_payload (first::second::tail) common
                ready.semantic.1.normal.facts available normalized step
              rw [shape] at outputAvailable called
              obtain ⟨value,after,values,middle,actual,calls,_,_,_,_,increase,observed⟩ :=
                SourceCurrentStoredUnionObservations.complete entry (first::second::tail)
                  (maximumDepth (first::second::tail)) (childFree (first::second::tail)) environment common
                  ready outputAvailable replacements
              have equal := Outcome.done.inj (actual.symm.trans called)
              have repeated := SourceCurrentStoredCallsReplay.replay calls common
                ready.semantic.1.normal.facts.coherent.valid (by simpa only [equal.2] using increase)
              have same := paired_equal environment common repeated paired
              intro depth view
              simpa only [equal.1,same] using observed depth view

end MicroCFTA.SourceCurrentStoredUnionWarm
