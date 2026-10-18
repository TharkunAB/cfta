import MicroCFTA.SourceCurrentPublicationFiniteRootReconstruction
import MicroCFTA.SourceCurrentOpenObservations

/-!
# Actual finite unfolding equations for selected Mu writers

The selected stored record supplies its actual source publication.
The strict body case constructs both stored reconstructions. The first
call is the actual Mu unfolding at the original reader. Finite observations
therefore identify that Mu with the returned ordinary reconstruction.
Physical Empty agreement applies only to the two reconstructed results.
No physical Empty agreement between a Mu and its unfolding is claimed.
-/
namespace MicroCFTA.SourceCurrentRetainedMuFiniteUnfoldEquation
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (Reference NodeKey)
open InternedNestedConstruction (Outcome)
open InternedFreshOrdinaryConstruction (ordinaryLevel)
open InternedFreshOrdinaryStoredSubstitution (execute unfold)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentNativeMuPublication (Publication History)
open SourceCurrentRetainedMuWriterAlignment (Writer)
open SourceCurrentStoredMuBinderChildLineage (bind)
open SourceCurrentPublicationFiniteRootReconstruction (BodyIH)
open SourceCurrentReaderFiniteOrdinaryStep (RelatedAt)
open SourceCurrentOpenObservations (Same)

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- An installed writer derives an actual unfolding and its finite ordinary reconstruction equation. -/
theorem finite (count : Nat) (reader : State Symbol Guard) (key : NodeKey)
    (entry : Interned NodeKey) (body cachedDepth ordinary : Value Symbol Guard)
    (event : Publication (Symbol := Symbol) (Guard := Guard))
    (writer : Writer reader key (.mu entry body cachedDepth ordinary) event)
    (ready : Ready reader)
    (selected : reader.nodeRecords key = some (.mu entry body cachedDepth ordinary))
    (strict : BodyIH count reader event (.mu entry body cachedDepth ordinary) (fun _ => none) reader) :
    ∃ left middle right final,
      unfold (.mu entry body cachedDepth ordinary) reader = .done left middle ∧
      execute ordinary
        (bind (.uninterned (ordinaryLevel cachedDepth)) (.mu entry body cachedDepth ordinary) (fun _ => none))
        middle = .done right final ∧
      execute body
        (bind (.interned entry.identity) (.mu entry body cachedDepth ordinary) (fun _ => none))
        final = .done left final ∧
      execute ordinary
        (bind (.uninterned (ordinaryLevel cachedDepth)) (.mu entry body cachedDepth ordinary) (fun _ => none))
        final = .done right final ∧
      Keeps reader middle ∧ Keeps middle final ∧ Available final left ∧ Available final right ∧
      Nonempty (History reader middle) ∧ Nonempty (History middle final) ∧
      final.nodeRecords key = some (.mu entry body cachedDepth ordinary) ∧
      RelatedAt (count + 1) reader left right ∧
      Same (count + 1) reader [.mu entry body cachedDepth ordinary] [right] := by
  have available := ready.semantic.1.normal.facts.cached.nodes key _ selected
  obtain ⟨left,middle,right,final,firstDone,secondDone,firstWarm,secondWarm,
    firstKept,secondKept,leftAvailable,rightAvailable,firstHistory,secondHistory,record,related⟩ :=
    SourceCurrentPublicationFiniteRootReconstruction.writer count reader reader key entry body cachedDepth ordinary
      event writer ready selected (.mu entry body cachedDepth ordinary) available (fun _ => none)
      (by intro _ _ impossible; cases impossible) strict
  have actual : unfold (.mu entry body cachedDepth ordinary) reader = .done left middle := firstDone
  have observed := SourceCurrentOpenObservations.unfold (count + 1) reader entry body cachedDepth ordinary left middle actual
  exact ⟨left,middle,right,final,actual,secondDone,firstWarm,secondWarm,
    firstKept,secondKept,leftAvailable,rightAvailable,firstHistory,secondHistory,record,related,
    observed.trans related.2⟩

/-- All finite strict body cases give one actual unfolding equation at every observation depth. -/
theorem all_depths (reader : State Symbol Guard) (key : NodeKey)
    (entry : Interned NodeKey) (body cachedDepth ordinary : Value Symbol Guard)
    (event : Publication (Symbol := Symbol) (Guard := Guard))
    (writer : Writer reader key (.mu entry body cachedDepth ordinary) event)
    (ready : Ready reader)
    (selected : reader.nodeRecords key = some (.mu entry body cachedDepth ordinary))
    (strict : ∀ count, BodyIH count reader event (.mu entry body cachedDepth ordinary) (fun _ => none) reader) :
    ∃ left middle right final,
      unfold (.mu entry body cachedDepth ordinary) reader = .done left middle ∧
      execute ordinary
        (bind (.uninterned (ordinaryLevel cachedDepth)) (.mu entry body cachedDepth ordinary) (fun _ => none))
        middle = .done right final ∧
      execute body
        (bind (.interned entry.identity) (.mu entry body cachedDepth ordinary) (fun _ => none))
        final = .done left final ∧
      execute ordinary
        (bind (.uninterned (ordinaryLevel cachedDepth)) (.mu entry body cachedDepth ordinary) (fun _ => none))
        final = .done right final ∧
      Keeps reader middle ∧ Keeps middle final ∧ Available final left ∧ Available final right ∧
      Nonempty (History reader middle) ∧ Nonempty (History middle final) ∧
      final.nodeRecords key = some (.mu entry body cachedDepth ordinary) ∧
      (left.referenceOf = .empty ↔ right.referenceOf = .empty) ∧
      ∀ count, Same count reader [left] [right] ∧
        Same count reader [.mu entry body cachedDepth ordinary] [right] := by
  obtain ⟨left,middle,right,final,actual,secondDone,firstWarm,secondWarm,
    firstKept,secondKept,leftAvailable,rightAvailable,firstHistory,secondHistory,record,related,_⟩ :=
    finite 0 reader key entry body cachedDepth ordinary event writer ready selected (strict 0)
  refine ⟨left,middle,right,final,actual,secondDone,firstWarm,secondWarm,
    firstKept,secondKept,leftAvailable,rightAvailable,firstHistory,secondHistory,record,related.1,?_⟩
  intro count
  obtain ⟨newLeft,newMiddle,newRight,newFinal,newActual,newSecond,_,_,_,_,_,_,_,_,_,newRelated,observed⟩ :=
    finite count reader key entry body cachedDepth ordinary event writer ready selected (strict count)
  obtain ⟨rfl,rfl⟩ := Outcome.done.inj (actual.symm.trans newActual)
  obtain ⟨rfl,_⟩ := Outcome.done.inj (secondDone.symm.trans newSecond)
  exact ⟨newRelated.2.lower,observed.lower⟩

end MicroCFTA.SourceCurrentRetainedMuFiniteUnfoldEquation
