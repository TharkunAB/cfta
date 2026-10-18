import MicroCFTA.SourceCurrentCausalSourceRootLaw
import MicroCFTA.InternedProfileComposition

/-!
# Causal source root comparison through actual unions

Each original member uses its two actual adjacent source calls. Completed
tails give forward growth from those calls to the common reader. Member
laws compare their deletion observations. Actual union normalization then
combines those observations at the captured constructor states.
-/
namespace MicroCFTA.SourceCurrentCausalSourceUnionComparison
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome work)
open InternedNestedProvenance (Values)
open InternedFreshOrdinaryConstruction (build buildMany)
open InternedFreshOrdinaryLiveInputs (input inputProfile)
open InternedBinderProtocol (Reference)
open InternedRootProfile (Profile Equivalent)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentUsedBinderAliasTransport (Aliases Scope)
open SourceCurrentNativeNormalizationInputs (support inputNames)
open SourceCurrentStoredRootDeletion (deleted deletedMany)
open SourceCurrentStoredMuProfileContract (Correct)
open SourceCurrentCausalSourceRootLaw (Law)

private theorem member_aliases {Atom : Type} (expressions : List (Syntax Symbol Guard))
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (aliases : Aliases (.union expressions) inputs firstNames secondNames)
    (child : Syntax Symbol Guard) (member : child ∈ expressions) :
    Aliases child inputs firstNames secondNames := by
  have included (label : Sum Reference Atom) (present : label ∈ Scope child inputs) :
      label ∈ Scope (.union expressions) inputs := by
    rcases List.mem_cons.mp present with rfl | present
    · exact List.mem_cons_self
    · apply List.mem_cons_of_mem
      unfold support at present ⊢
      rw [InternedFreeNameSemantics.evaluate]
      exact (InternedFreeNameSemantics.evaluateMany_member expressions (inputs.map inputProfile)
        (inputs.map inputNames) label).mpr ⟨child,member,present⟩
  exact fun left leftMember right rightMember => aliases left (included left leftMember) right (included right rightMember)

variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem many_cons (expression : Syntax Symbol Guard) (rest : List (Syntax Symbol Guard))
    (inputs : List (Value Symbol Guard)) (before after : State Symbol Guard)
    (outputs : List (Value Symbol Guard))
    (actual : buildMany (expression :: rest) inputs before = .done outputs after) :
    ∃ value middle values, outputs = value :: values ∧
      build expression inputs before = .done value middle ∧
      buildMany rest inputs middle = .done values after := by
  cases called : build expression inputs before with
  | pending key current => simp only [buildMany,called,Outcome.bind] at actual; cases actual
  | done value middle =>
      cases tail : buildMany rest inputs middle with
      | pending key current => simp only [buildMany,called,tail,Outcome.bind] at actual; cases actual
      | done values final =>
          simp only [buildMany,called,tail,Outcome.bind,Outcome.done.injEq] at actual
          obtain ⟨rfl,rfl⟩ := actual
          exact ⟨value,middle,values,rfl,called,tail⟩

private theorem many {Atom : Type} (expressions : List (Syntax Symbol Guard))
    (ih : ∀ child ∈ expressions, Law child) (reader : State Symbol Guard)
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (firstAssignment secondAssignment : Reference → Profile) (firstCuts secondCuts : Reference → Bool)
    (firstBefore firstAfter secondBefore secondAfter : State Symbol Guard)
    (first second : List (Value Symbol Guard))
    (firstContext : Context firstBefore (inputs.map (input firstNames)))
    (secondContext : Context secondBefore (inputs.map (input secondNames)))
    (aliases : ∀ child ∈ expressions, Aliases child inputs firstNames secondNames)
    (profiles : ∀ child ∈ expressions, SourceCurrentScopedProfileInputs.Compatible child inputs
      firstNames secondNames firstAssignment secondAssignment)
    (cuts : ∀ child ∈ expressions, SourceCurrentScopedDeletionInputs.Compatible child inputs
      firstNames secondNames firstCuts secondCuts)
    (firstDone : buildMany expressions (inputs.map (input firstNames)) firstBefore = .done first firstAfter)
    (secondDone : buildMany expressions (inputs.map (input secondNames)) secondBefore = .done second secondAfter)
    (firstGrowth : Grows firstAfter reader) (secondGrowth : Grows secondAfter reader)
    (heap : SourceCurrentPublicationHeapInduction.Heap Correct reader)
    (history : SourceCurrentNativeMuPublication.History empty reader) :
    Equivalent (deletedMany firstCuts first firstAssignment) (deletedMany secondCuts second secondAssignment) := by
  cases expressions with
  | nil =>
      simp only [buildMany,Outcome.done.injEq] at firstDone secondDone
      obtain ⟨rfl,_⟩ := firstDone
      obtain ⟨rfl,_⟩ := secondDone
      rw [deletedMany,deletedMany]
      exact InternedProfileEquivalence.refl _
  | cons expression rest =>
      obtain ⟨left,leftMiddle,lefts,rfl,leftDone,leftTail⟩ := many_cons expression rest _ firstBefore firstAfter first firstDone
      obtain ⟨right,rightMiddle,rights,rfl,rightDone,rightTail⟩ := many_cons expression rest _ secondBefore secondAfter second secondDone
      have leftContext : Context leftMiddle (inputs.map (input firstNames)) := by
        simpa only [leftDone,Outcome.state] using firstContext.build expression
      have rightContext : Context rightMiddle (inputs.map (input secondNames)) := by
        simpa only [rightDone,Outcome.state] using secondContext.build expression
      have leftGrowth : Grows leftMiddle firstAfter := by
        simpa only [leftTail,Outcome.state] using
          (InternedFreshOrdinaryFacts.buildMany_verified rest _ leftMiddle leftContext.base.normal.facts leftContext.base.inputs).growth
      have rightGrowth : Grows rightMiddle secondAfter := by
        simpa only [rightTail,Outcome.state] using
          (InternedFreshOrdinaryFacts.buildMany_verified rest _ rightMiddle rightContext.base.normal.facts rightContext.base.inputs).growth
      have head := ih expression List.mem_cons_self reader inputs firstNames secondNames
        firstAssignment secondAssignment firstCuts secondCuts firstBefore leftMiddle secondBefore rightMiddle left right
        firstContext secondContext (aliases expression List.mem_cons_self)
        (profiles expression List.mem_cons_self) (cuts expression List.mem_cons_self)
        leftDone rightDone (grows_trans leftGrowth firstGrowth) (grows_trans rightGrowth secondGrowth) heap history
      have tail := many rest (fun child member => ih child (List.mem_cons_of_mem _ member)) reader inputs
        firstNames secondNames firstAssignment secondAssignment firstCuts secondCuts
        leftMiddle firstAfter rightMiddle secondAfter lefts rights leftContext rightContext
        (fun child member => aliases child (List.mem_cons_of_mem _ member))
        (fun child member => profiles child (List.mem_cons_of_mem _ member))
        (fun child member => cuts child (List.mem_cons_of_mem _ member))
        leftTail rightTail firstGrowth secondGrowth heap history
      rw [deletedMany,deletedMany]
      exact InternedProfileComposition.combine_same head tail
termination_by sizeOf expressions

private theorem union_parts (expressions : List (Syntax Symbol Guard)) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (context : Context before inputs) (result : Value Symbol Guard)
    (after : State Symbol Guard) (actual : build (.union expressions) inputs before = .done result after) :
    ∃ outputs middle,
      buildMany expressions inputs before = .done outputs middle ∧ Context middle inputs ∧
      Values middle outputs ∧ run (makeUnion outputs) middle = (result,after) := by
  cases called : buildMany expressions inputs before with
  | pending key current => simp only [build,called,Outcome.bind] at actual; cases actual
  | done outputs middle =>
      have made : run (makeUnion outputs) middle = (result,after) :=
        Prod.ext (Outcome.done.inj (by simpa only [build,called,Outcome.bind,work] using actual)).1
          (Outcome.done.inj (by simpa only [build,called,Outcome.bind,work] using actual)).2
      exact ⟨outputs,middle,rfl,
        by simpa only [called,Outcome.state] using context.many expressions,
        (InternedFreshOrdinaryFacts.buildMany_verified expressions inputs before context.base.normal.facts context.base.inputs).result
          outputs middle called,made⟩

/-- Immediate member laws compare actual union source calls at the same later reader. -/
theorem union (expressions : List (Syntax Symbol Guard)) (ih : ∀ child ∈ expressions, Law child) :
    Law (.union expressions) := by
  intro Atom reader inputs firstNames secondNames firstAssignment secondAssignment firstCuts secondCuts
    firstBefore firstAfter secondBefore secondAfter first second
    firstContext secondContext aliases profiles cuts firstDone secondDone firstGrowth secondGrowth heap history
  obtain ⟨left,leftMiddle,leftMany,leftContext,leftAvailable,leftMade⟩ :=
    union_parts expressions _ firstBefore firstContext first firstAfter firstDone
  obtain ⟨right,rightMiddle,rightMany,rightContext,rightAvailable,rightMade⟩ :=
    union_parts expressions _ secondBefore secondContext second secondAfter secondDone
  have leftConstructorGrowth := (run_correct (makeUnion left) leftMiddle leftContext.base.normal.facts.coherent.valid).2
  have rightConstructorGrowth := (run_correct (makeUnion right) rightMiddle rightContext.base.normal.facts.coherent.valid).2
  rw [leftMade] at leftConstructorGrowth
  rw [rightMade] at rightConstructorGrowth
  have members := many expressions ih reader inputs firstNames secondNames firstAssignment secondAssignment firstCuts secondCuts
    firstBefore leftMiddle secondBefore rightMiddle left right firstContext secondContext
    (fun child member => member_aliases expressions inputs firstNames secondNames aliases child member)
    (fun child member => SourceCurrentScopedProfileInputs.union_member expressions inputs firstNames secondNames
      firstAssignment secondAssignment profiles child member)
    (fun child member => SourceCurrentScopedDeletionInputs.union_member expressions inputs firstNames secondNames
      firstCuts secondCuts cuts child member)
    leftMany rightMany (grows_trans leftConstructorGrowth firstGrowth)
    (grows_trans rightConstructorGrowth secondGrowth) heap history
  have firstProfile := SourceCurrentStoredRootDeletionConstruction.makeUnion firstCuts left firstAssignment
    leftMiddle leftContext.base.normal leftAvailable
  have secondProfile := SourceCurrentStoredRootDeletionConstruction.makeUnion secondCuts right secondAssignment
    rightMiddle rightContext.base.normal rightAvailable
  rw [leftMade] at firstProfile
  rw [rightMade] at secondProfile
  exact InternedProfileEquivalence.trans firstProfile (InternedProfileEquivalence.trans members (InternedProfileEquivalence.symm secondProfile))

end MicroCFTA.SourceCurrentCausalSourceUnionComparison
