import MicroCFTA.SourceCurrentCausalSourceRootLaw
import MicroCFTA.MergedPhysicalGroupEdges
import MicroCFTA.InternedFreshOrdinaryProfiles

/-!
# Causal source root comparison for ordinary nodes

The proof follows both actual ordered child and row schedules.
Only original live rows need the strict child comparison law.
An original dead row has an actual Empty child under either input map.
All profile and deletion facts use the actual historical contexts.
-/
namespace MicroCFTA.SourceCurrentCausalSourceNodeComparison
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work)
open InternedFreshOrdinaryConstruction (build buildMany buildEdges)
open InternedFreshOrdinaryFacts (build_verified buildMany_verified buildEdges_verified)
open InternedFreshOrdinaryLiveInputs (input inputProfile)
open SourceCurrentNativeNormalizationInputs (support inputNames)
open SourceCurrentUsedBinderAliasTransport (Aliases Scope)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentStoredProfileFunction (denote)
open SourceCurrentStoredRootDeletion (deleted)
open SourceCurrentCausalSourceRootLaw (Law)
open InternedRootProfile (Profile)
open InternedProfileSemantics (isEmpty)
open InternedBinderProtocol (Reference)

variable {Atom : Type}

private theorem live_aliases (rows : List (EdgeSyntax Symbol Guard))
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (aliases : Aliases (.node rows) inputs firstNames secondNames)
    (symbol : Symbol) (guard : Guard) (children : List (Syntax Symbol Guard))
    (row : EdgeSyntax.mk symbol guard children ∈ rows)
    (live : (InternedProfileSemantics.evaluateMany children (inputs.map inputProfile)).all
      (fun child => !InternedProfileSemantics.isEmpty child) = true)
    (child : Syntax Symbol Guard) (member : child ∈ children) :
    Aliases child inputs firstNames secondNames := by
  have included (label : Sum Reference Atom) (present : label ∈ Scope child inputs) :
      label ∈ Scope (.node rows) inputs := by
    rcases List.mem_cons.mp present with rfl | present
    · exact List.mem_cons_self
    · apply List.mem_cons_of_mem
      unfold support at present ⊢
      rw [InternedFreeNameSemantics.evaluate]
      exact (InternedFreeNameSemantics.evaluateEdges_member rows (inputs.map inputProfile)
        (inputs.map inputNames) label).mpr ⟨symbol,guard,children,row,live,child,member,present⟩
  exact fun a aMember b bMember => aliases a (included a aMember) b (included b bMember)


private theorem source_live [DecidableEq (EdgeKey Symbol Guard)] (children : List (Syntax Symbol Guard))
    (inputs : List (Sum (Value Symbol Guard) Atom)) (names : Atom → Reference)
    (before after : State Symbol Guard)
    (context : InternedFreshOrdinaryContext.Context before (inputs.map (input names)))
    (values : List (Value Symbol Guard))
    (called : buildMany children (inputs.map (input names)) before = .done values after)
    (live : values.any (fun value => value.referenceOf == .empty) = false) :
    (InternedProfileSemantics.evaluateMany children (inputs.map inputProfile)).all
      (fun child => !InternedProfileSemantics.isEmpty child) = true := by
  have checked := buildMany_verified children _ before context.normal.facts context.inputs
  have afterContext : InternedFreshOrdinaryContext.Context after (inputs.map (input names)) := by
    simpa only [called,Outcome.state] using context.many children
  have output := checked.result values after called
  have matched := (InternedFreshOrdinaryProfiles.buildMany_profile children _ before
    context.normal context.inputs context.profiles).result values after called
  have actualLive : values.all (fun value => !InternedProfileSemantics.isEmpty (InternedRootProfile.profile value)) = true := by
    apply List.all_eq_true.mpr
    intro value member
    rw [InternedRootProfileNode.isEmpty_profile value after afterContext.normal.proper (output value member)]
    have absent := List.any_eq_false.mp live value member
    rw [Bool.eq_false_iff.mpr absent]
    rfl
  rw [InternedProfileComposition.children_matched matched] at actualLive
  simpa only [InternedFreshOrdinaryLiveInputs.input_profiles,InternedProfileSemantics.evaluateMany_map,
    List.all_map,Function.comp_def,InternedProfileSemantics.isEmpty_map] using actualLive

private theorem source_dead [DecidableEq (EdgeKey Symbol Guard)] (children : List (Syntax Symbol Guard))
    (inputs : List (Sum (Value Symbol Guard) Atom)) (names : Atom → Reference)
    (before after : State Symbol Guard)
    (context : Context before (inputs.map (input names)))
    (values : List (Value Symbol Guard))
    (called : buildMany children (inputs.map (input names)) before = .done values after)
    (dead : (InternedProfileSemantics.evaluateMany children (inputs.map inputProfile)).all
      (fun child => !isEmpty child) = false) (assignment : Reference → Profile) :
    values.all (fun value => !isEmpty (denote value assignment)) = false := by
  apply Bool.eq_false_iff.mpr
  intro future
  have noEmpty : values.any (fun value => value.referenceOf == .empty) = false := by
    apply Bool.eq_false_iff.mpr
    intro selected
    obtain ⟨value,member,empty⟩ := List.any_eq_true.mp selected
    have same := (InternedEmptyNormalization.reference_empty value).mp (eq_of_beq empty)
    have live := List.all_eq_true.mp future value member
    rw [same,SourceCurrentStoredProfileFunction.empty] at live
    cases live
  have live := source_live children inputs names before after context.base values called noEmpty
  rw [dead] at live
  cases live

private theorem many_assigned [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (reader : State Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) (firstAssignment secondAssignment : Reference → Profile)
    (ih : ∀ child ∈ expressions, Law child)
    (properties : ∀ child ∈ expressions, Aliases child inputs firstNames secondNames ∧
      SourceCurrentScopedProfileInputs.Compatible child inputs firstNames secondNames firstAssignment secondAssignment)
    (before after later final : State Symbol Guard)
    (firstContext : Context before (inputs.map (input firstNames)))
    (secondContext : Context later (inputs.map (input secondNames)))
    (first second : List (Value Symbol Guard))
    (called : buildMany expressions (inputs.map (input firstNames)) before = .done first after)
    (other : buildMany expressions (inputs.map (input secondNames)) later = .done second final)
    (firstGrowth : Grows after reader) (secondGrowth : Grows final reader)
    (heap : SourceCurrentPublicationHeapInduction.Heap SourceCurrentStoredMuProfileContract.Correct reader)
    (history : SourceCurrentNativeMuPublication.History empty reader) :
    first.all (fun value => !isEmpty (denote value firstAssignment)) =
      second.all (fun value => !isEmpty (denote value secondAssignment)) := by
  cases expressions with
  | nil =>
      simp only [buildMany,Outcome.done.injEq] at called other
      obtain ⟨rfl,rfl⟩ := called
      obtain ⟨rfl,rfl⟩ := other
      rfl
  | cons expression expressions =>
      cases one : build expression (inputs.map (input firstNames)) before with
      | pending key state => simp only [buildMany,one,Outcome.bind] at called; cases called
      | done value middle =>
        cases two : build expression (inputs.map (input secondNames)) later with
        | pending key state => simp only [buildMany,two,Outcome.bind] at other; cases other
        | done next nextHeap =>
          cases tail : buildMany expressions (inputs.map (input firstNames)) middle with
          | pending key state => simp only [buildMany,one,tail,Outcome.bind] at called; cases called
          | done remaining last =>
            cases rest : buildMany expressions (inputs.map (input secondNames)) nextHeap with
            | pending key state => simp only [buildMany,two,rest,Outcome.bind] at other; cases other
            | done more lastHeap =>
              simp only [buildMany,one,tail,Outcome.bind,Outcome.done.injEq] at called
              simp only [buildMany,two,rest,Outcome.bind,Outcome.done.injEq] at other
              obtain ⟨rfl,rfl⟩ := called
              obtain ⟨rfl,rfl⟩ := other
              have middleContext : Context middle (inputs.map (input firstNames)) := by
                simpa only [one,Outcome.state] using firstContext.build expression
              have nextContext : Context nextHeap (inputs.map (input secondNames)) := by
                simpa only [two,Outcome.state] using secondContext.build expression
              have middleGrowth : Grows middle reader := grows_trans
                (by simpa only [tail,Outcome.state] using
                  (buildMany_verified expressions _ middle middleContext.base.normal.facts middleContext.base.inputs).growth)
                firstGrowth
              have nextGrowth : Grows nextHeap reader := grows_trans
                (by simpa only [rest,Outcome.state] using
                  (buildMany_verified expressions _ nextHeap nextContext.base.normal.facts nextContext.base.inputs).growth)
                secondGrowth
              have known := properties expression List.mem_cons_self
              have compared := ih expression List.mem_cons_self reader inputs firstNames secondNames
                firstAssignment secondAssignment (fun _ => false) (fun _ => false)
                before middle later nextHeap value next firstContext secondContext known.1 known.2
                ⟨fun _ _ => rfl,fun _ _ => rfl⟩ one two middleGrowth nextGrowth heap history
              have firstAvailable := (build_verified expression _ before firstContext.base.normal.facts
                firstContext.base.inputs).result value middle one
              have secondAvailable := (build_verified expression _ later secondContext.base.normal.facts
                secondContext.base.inputs).result next nextHeap two
              rw [SourceCurrentStoredRootDeletion.uncut value firstAssignment middle middleContext.base.normal firstAvailable,
                SourceCurrentStoredRootDeletion.uncut next secondAssignment nextHeap nextContext.base.normal secondAvailable] at compared
              have tailCompared := many_assigned expressions reader inputs firstNames secondNames
                firstAssignment secondAssignment
                (fun child member => ih child (List.mem_cons_of_mem _ member))
                (fun child member => properties child (List.mem_cons_of_mem _ member))
                middle last nextHeap lastHeap middleContext nextContext remaining more tail rest
                firstGrowth secondGrowth heap history
              simp only [List.all_cons,InternedProfileComposition.isEmpty_same compared,tailCompared]
termination_by expressions.length

private theorem rows_assigned [DecidableEq (EdgeKey Symbol Guard)] (rows : List (EdgeSyntax Symbol Guard))
    (reader : State Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) (firstAssignment secondAssignment : Reference → Profile)
    (properties : ∀ symbol guard children, EdgeSyntax.mk symbol guard children ∈ rows →
      (InternedProfileSemantics.evaluateMany children (inputs.map inputProfile)).all
        (fun child => !isEmpty child) = true →
      ∀ child ∈ children, Law child ∧ Aliases child inputs firstNames secondNames ∧
        SourceCurrentScopedProfileInputs.Compatible child inputs firstNames secondNames firstAssignment secondAssignment)
    (before after later final : State Symbol Guard)
    (firstContext : Context before (inputs.map (input firstNames)))
    (secondContext : Context later (inputs.map (input secondNames)))
    (first second : List (EdgeValue Symbol Guard))
    (called : buildEdges rows (inputs.map (input firstNames)) before = .done first after)
    (other : buildEdges rows (inputs.map (input secondNames)) later = .done second final)
    (firstGrowth : Grows after reader) (secondGrowth : Grows final reader)
    (heap : SourceCurrentPublicationHeapInduction.Heap SourceCurrentStoredMuProfileContract.Correct reader)
    (history : SourceCurrentNativeMuPublication.History empty reader) :
    first.any (fun edge => edge.children.all (fun value => !isEmpty (denote value firstAssignment))) =
      second.any (fun edge => edge.children.all (fun value => !isEmpty (denote value secondAssignment))) := by
  cases rows with
  | nil =>
      simp only [buildEdges,Outcome.done.injEq] at called other
      obtain ⟨rfl,rfl⟩ := called
      obtain ⟨rfl,rfl⟩ := other
      rfl
  | cons row rows =>
    cases row with
    | mk symbol guard children =>
      cases one : buildMany children (inputs.map (input firstNames)) before with
      | pending key state => simp only [buildEdges,one,Outcome.bind] at called; cases called
      | done values middle =>
        cases two : buildMany children (inputs.map (input secondNames)) later with
        | pending key state => simp only [buildEdges,two,Outcome.bind] at other; cases other
        | done next nextHeap =>
          let made := run (makeEdge symbol guard values) middle
          let otherMade := run (makeEdge symbol guard next) nextHeap
          cases tail : buildEdges rows (inputs.map (input firstNames)) made.2 with
          | pending key state =>
              simp only [buildEdges,one,Outcome.bind,work] at called
              change (buildEdges rows _ made.2).bind _ = _ at called
              simp only [tail,Outcome.bind] at called
              cases called
          | done remaining last =>
            cases rest : buildEdges rows (inputs.map (input secondNames)) otherMade.2 with
            | pending key state =>
                simp only [buildEdges,two,Outcome.bind,work] at other
                change (buildEdges rows _ otherMade.2).bind _ = _ at other
                simp only [rest,Outcome.bind] at other
                cases other
            | done more lastHeap =>
              simp only [buildEdges,one,Outcome.bind,work] at called
              change (buildEdges rows _ made.2).bind _ = _ at called
              simp only [tail,Outcome.bind,Outcome.done.injEq] at called
              simp only [buildEdges,two,Outcome.bind,work] at other
              change (buildEdges rows _ otherMade.2).bind _ = _ at other
              simp only [rest,Outcome.bind,Outcome.done.injEq] at other
              obtain ⟨rfl,rfl⟩ := called
              obtain ⟨rfl,rfl⟩ := other
              have middleContext : Context middle (inputs.map (input firstNames)) := by
                simpa only [one,Outcome.state] using firstContext.many children
              have nextContext : Context nextHeap (inputs.map (input secondNames)) := by
                simpa only [two,Outcome.state] using secondContext.many children
              have valuesAvailable := (buildMany_verified children _ before firstContext.base.normal.facts
                firstContext.base.inputs).result values middle one
              have nextAvailable := (buildMany_verified children _ later secondContext.base.normal.facts
                secondContext.base.inputs).result next nextHeap two
              have firstFields := MergedPhysicalGroupEdges.makeEdge_fields middle middleContext.base.normal.facts
                symbol guard values valuesAvailable
              have secondFields := MergedPhysicalGroupEdges.makeEdge_fields nextHeap nextContext.base.normal.facts
                symbol guard next nextAvailable
              have madeContext : Context made.2 (inputs.map (input firstNames)) :=
                middleContext.edge symbol guard values valuesAvailable
              have otherMadeContext : Context otherMade.2 (inputs.map (input secondNames)) :=
                nextContext.edge symbol guard next nextAvailable
              have madeGrowth : Grows made.2 reader := grows_trans
                (by simpa only [tail,Outcome.state] using
                  (buildEdges_verified rows _ made.2 madeContext.base.normal.facts madeContext.base.inputs).growth)
                firstGrowth
              have otherMadeGrowth : Grows otherMade.2 reader := grows_trans
                (by simpa only [rest,Outcome.state] using
                  (buildEdges_verified rows _ otherMade.2 otherMadeContext.base.normal.facts otherMadeContext.base.inputs).growth)
                secondGrowth
              have middleGrowth : Grows middle reader := grows_trans
                (InternedNestedFacts.edge_verified symbol guard values middle
                  middleContext.base.normal.facts valuesAvailable).growth madeGrowth
              have nextGrowth : Grows nextHeap reader := grows_trans
                (InternedNestedFacts.edge_verified symbol guard next nextHeap
                  nextContext.base.normal.facts nextAvailable).growth otherMadeGrowth
              have rowCompared : values.all (fun value => !isEmpty (denote value firstAssignment)) =
                  next.all (fun value => !isEmpty (denote value secondAssignment)) := by
                cases live : (InternedProfileSemantics.evaluateMany children (inputs.map inputProfile)).all
                    (fun child => !isEmpty child) with
                | false =>
                    rw [source_dead children inputs firstNames before middle firstContext values one live firstAssignment,
                      source_dead children inputs secondNames later nextHeap secondContext next two live secondAssignment]
                | true =>
                    have availableIH := properties symbol guard children List.mem_cons_self live
                    exact many_assigned children reader inputs firstNames secondNames firstAssignment secondAssignment
                      (fun child member => (availableIH child member).1)
                      (fun child member => (availableIH child member).2)
                      before middle later nextHeap firstContext secondContext values next one two
                      middleGrowth nextGrowth heap history
              have tailCompared := rows_assigned rows reader inputs firstNames secondNames firstAssignment secondAssignment
                (fun symbol guard children member => properties symbol guard children (List.mem_cons_of_mem _ member))
                made.2 last otherMade.2 lastHeap madeContext otherMadeContext remaining more tail rest
                firstGrowth secondGrowth heap history
              simp only [List.any_cons]
              rw [show made.1.children = values from firstFields.2.2,
                show otherMade.1.children = next from secondFields.2.2,rowCompared,tailCompared]
termination_by rows.length

/-- Strict child source laws compare actual nodes through their original live row schedules. -/
theorem node [DecidableEq (EdgeKey Symbol Guard)] (rows : List (EdgeSyntax Symbol Guard))
    (ih : ∀ symbol guard children, EdgeSyntax.mk symbol guard children ∈ rows →
      ∀ child ∈ children, Law child) : Law (.node rows) := by
  intro Atom reader inputs firstNames secondNames firstAssignment secondAssignment firstCuts secondCuts
    firstBefore firstAfter secondBefore secondAfter first second firstContext secondContext
    aliases profiles _cuts firstDone secondDone firstGrowth secondGrowth heap history
  cases firstRowsDone : buildEdges rows (inputs.map (input firstNames)) firstBefore with
  | pending key state => simp only [build,firstRowsDone,Outcome.bind] at firstDone; cases firstDone
  | done firstRows middle =>
    cases secondRowsDone : buildEdges rows (inputs.map (input secondNames)) secondBefore with
    | pending key state => simp only [build,secondRowsDone,Outcome.bind] at secondDone; cases secondDone
    | done secondRows nextHeap =>
      simp only [build,firstRowsDone,Outcome.bind,work,Outcome.done.injEq] at firstDone
      simp only [build,secondRowsDone,Outcome.bind,work,Outcome.done.injEq] at secondDone
      obtain ⟨rfl,rfl⟩ := firstDone
      obtain ⟨rfl,rfl⟩ := secondDone
      have middleContext : Context middle (inputs.map (input firstNames)) := by
        simpa only [firstRowsDone,Outcome.state] using firstContext.edges rows
      have nextContext : Context nextHeap (inputs.map (input secondNames)) := by
        simpa only [secondRowsDone,Outcome.state] using secondContext.edges rows
      have firstAvailable := (buildEdges_verified rows _ firstBefore firstContext.base.normal.facts
        firstContext.base.inputs).result firstRows middle firstRowsDone
      have secondAvailable := (buildEdges_verified rows _ secondBefore secondContext.base.normal.facts
        secondContext.base.inputs).result secondRows nextHeap secondRowsDone
      have middleGrowth : Grows middle reader := grows_trans
        (InternedNestedFacts.node_verified firstRows middle middleContext.base.normal.facts firstAvailable).growth firstGrowth
      have nextGrowth : Grows nextHeap reader := grows_trans
        (InternedNestedFacts.node_verified secondRows nextHeap nextContext.base.normal.facts secondAvailable).growth secondGrowth
      have same := rows_assigned rows reader inputs firstNames secondNames firstAssignment secondAssignment
        (fun symbol guard children row live child member => ⟨ih symbol guard children row child member,
          live_aliases rows inputs firstNames secondNames aliases symbol guard children row live child member,
          SourceCurrentScopedProfileInputs.node_child rows inputs firstNames secondNames firstAssignment secondAssignment
            profiles symbol guard children row live child member⟩)
        firstBefore middle secondBefore nextHeap firstContext secondContext firstRows secondRows
        firstRowsDone secondRowsDone middleGrowth nextGrowth heap history
      rw [SourceCurrentStoredRootDeletionConstruction.makeNode firstCuts firstRows firstAssignment
        middle middleContext.base.normal firstAvailable,
        SourceCurrentStoredRootDeletionConstruction.makeNode secondCuts secondRows secondAssignment
        nextHeap nextContext.base.normal secondAvailable,same]
      exact InternedProfileEquivalence.refl _

end MicroCFTA.SourceCurrentCausalSourceNodeComparison

