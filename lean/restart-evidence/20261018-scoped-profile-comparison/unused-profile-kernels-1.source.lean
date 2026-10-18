import MicroCFTA.SourceCurrentStoredMuUnusedProfile
import MicroCFTA.SourceEqualityRequiredCache
import MicroCFTA.SourceCurrentConstrainedCapSourceHistory
set_option linter.all true
namespace MicroCFTA.StoredMuUnusedProfileKernels
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome finish)
open InternedFreshOrdinaryConstruction (build ordinaryLevel)
open InternedBinderProtocol (Reference NodeKey)
open InternedRootProfile (Profile Equivalent)
open SourceCurrentStoredProfileFunction (denote)
open SourceCurrentStoredMuProfileContract (shadow Correct)
open SourceEqualityRequiredCache (Ready)
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

private def source (ordinaryCase : Bool) : Syntax Nat Bool :=
  .binder true (if ordinaryCase then .node [.mk 7 false []] else .var 0)
private def actual (ordinaryCase : Bool) := build (source ordinaryCase) [] empty
private def result (ordinaryCase : Bool) : Value Nat Bool :=
  match actual ordinaryCase with | .done value _ => value | .pending .. => .empty
private def reader (ordinaryCase : Bool) := (actual ordinaryCase).state
private def probe (ordinaryCase : Bool) (name : Reference) : Value Nat Bool :=
  if ordinaryCase then result ordinaryCase else .reference name
private def key (ordinaryCase : Bool) : NodeKey :=
  muKey (probe ordinaryCase .depth) (probe ordinaryCase (.uninterned 0))
private def stored (ordinaryCase : Bool) := ((reader ordinaryCase).nodeRecords (key ordinaryCase)).getD .empty
private def entry (ordinaryCase : Bool) : Interned NodeKey :=
  match stored ordinaryCase with | .mu entry _ _ _ => entry | _ => ⟨0,.node []⟩
private def body (ordinaryCase : Bool) :=
  match stored ordinaryCase with | .mu _ body _ _ => body | _ => .empty
private def depth (ordinaryCase : Bool) :=
  match stored ordinaryCase with | .mu _ _ depth _ => depth | _ => .empty
private def ordinary (ordinaryCase : Bool) :=
  match stored ordinaryCase with | .mu _ _ _ ordinary => ordinary | _ => .empty
private theorem actual_done (ordinaryCase : Bool) :
    build (source ordinaryCase) [] empty = .done (result ordinaryCase) (reader ordinaryCase) := by
  cases ordinaryCase <;> cbv
private theorem ready (ordinaryCase : Bool) : Ready (reader ordinaryCase) :=
  SourceEqualityRequiredCache.constructed _ _ _ (actual_done ordinaryCase)
private theorem present (ordinaryCase : Bool) :
    (reader ordinaryCase).nodeRecords (key ordinaryCase) =
      some (.mu (entry ordinaryCase) (body ordinaryCase) (depth ordinaryCase) (ordinary ordinaryCase)) := by
  cases ordinaryCase <;> cbv
private theorem available (ordinaryCase : Bool) : Available (reader ordinaryCase)
    (.mu (entry ordinaryCase) (body ordinaryCase) (depth ordinaryCase) (ordinary ordinaryCase)) :=
  (ready ordinaryCase).semantic.1.normal.facts.cached.nodes _ _ (present ordinaryCase)
private theorem depth_correct (ordinaryCase : Bool) :
    InternedFreshOrdinaryDepthHeap.Correct (entry ordinaryCase) (body ordinaryCase)
      (depth ordinaryCase) (ordinary ordinaryCase) :=
  (SourceCurrentConstrainedCapSourceHistory.empty_context.build (source ordinaryCase)).depth
    (key ordinaryCase) _ _ _ _ (present ordinaryCase)
private theorem unused (ordinaryCase : Bool) :
    InternedFreshOrdinaryDepthHeap.usesLocal (depth ordinaryCase) (ordinary ordinaryCase) = false := by
  cases ordinaryCase <;> cbv
private theorem returned (ordinaryCase : Bool) :
    finish true (.mu (entry ordinaryCase) (body ordinaryCase) (depth ordinaryCase) (ordinary ordinaryCase)) =
      result ordinaryCase := by cases ordinaryCase <;> cbv
private theorem correct (ordinaryCase : Bool) :
    Correct (entry ordinaryCase) (body ordinaryCase) (depth ordinaryCase) (ordinary ordinaryCase) := by
  intro assignment replacement
  cases ordinaryCase with
  | false =>
      have first : body false = .reference (.interned (entry false).identity) := by cbv
      have second : ordinary false = .reference (.uninterned (ordinaryLevel (depth false))) := by cbv
      rw [first,second,SourceCurrentStoredProfileFunction.reference,SourceCurrentStoredProfileFunction.reference]
      simp only [shadow,ite_true]
      exact InternedProfileEquivalence.refl _
  | true =>
      rw [SourceCurrentStoredProfileFunction.closed _ _ (by cbv),
        SourceCurrentStoredProfileFunction.closed _ _ (by cbv)]
      exact InternedProfileEquivalence.refl _
private theorem compared (ordinaryCase : Bool) (assignment : Reference → Profile) :
    Equivalent (denote (result ordinaryCase) assignment)
      (denote (ordinary ordinaryCase)
        (shadow (.uninterned (ordinaryLevel (depth ordinaryCase))) (some []) assignment)) := by
  rw [← returned ordinaryCase]
  exact SourceCurrentStoredMuUnusedProfile.smart_unused _ _ _ _ _
    (ready ordinaryCase).semantic.1.normal.facts.coherent (available ordinaryCase)
    (depth_correct ordinaryCase) (correct ordinaryCase) (unused ordinaryCase) assignment

private theorem checked :
    (∀ ordinaryCase : Bool,
      build (source ordinaryCase) [] empty = .done (result ordinaryCase) (reader ordinaryCase) ∧
      Ready (reader ordinaryCase) ∧
      (reader ordinaryCase).nodeRecords (key ordinaryCase) =
        some (.mu (entry ordinaryCase) (body ordinaryCase) (depth ordinaryCase) (ordinary ordinaryCase)) ∧
      Available (reader ordinaryCase)
        (.mu (entry ordinaryCase) (body ordinaryCase) (depth ordinaryCase) (ordinary ordinaryCase)) ∧
      InternedFreshOrdinaryDepthHeap.Correct (entry ordinaryCase) (body ordinaryCase)
        (depth ordinaryCase) (ordinary ordinaryCase) ∧
      Correct (entry ordinaryCase) (body ordinaryCase) (depth ordinaryCase) (ordinary ordinaryCase) ∧
      InternedFreshOrdinaryDepthHeap.usesLocal (depth ordinaryCase) (ordinary ordinaryCase) = false ∧
      finish true (.mu (entry ordinaryCase) (body ordinaryCase) (depth ordinaryCase) (ordinary ordinaryCase)) =
        result ordinaryCase ∧
      ∀ assignment : Reference → Profile, Equivalent (denote (result ordinaryCase) assignment)
        (denote (ordinary ordinaryCase)
          (shadow (.uninterned (ordinaryLevel (depth ordinaryCase))) (some []) assignment))) ∧
    result false = .empty ∧
    body false = .reference (.interned (entry false).identity) ∧
    body true = result true ∧ (body true).free = [] ∧
    ∃ identity rows level free, result true = .node identity rows level free ∧ rows ≠ [] := by
  refine ⟨fun choice => ⟨actual_done choice,ready choice,present choice,available choice,depth_correct choice,
    correct choice,unused choice,returned choice,compared choice⟩,?_,?_,?_,?_,?_⟩
  · cbv
  · cbv
  · cbv
  · cbv
  · exact ⟨_,_,_,_,by cbv,by cbv⟩

/-- Two actual initial source builds exercise bare-self and closed ordinary cleanup. -/
theorem actual_branches :
    (∀ ordinaryCase : Bool,
      build (source ordinaryCase) [] empty = .done (result ordinaryCase) (reader ordinaryCase) ∧
      Ready (reader ordinaryCase) ∧
      (reader ordinaryCase).nodeRecords (key ordinaryCase) =
        some (.mu (entry ordinaryCase) (body ordinaryCase) (depth ordinaryCase) (ordinary ordinaryCase)) ∧
      Available (reader ordinaryCase)
        (.mu (entry ordinaryCase) (body ordinaryCase) (depth ordinaryCase) (ordinary ordinaryCase)) ∧
      InternedFreshOrdinaryDepthHeap.Correct (entry ordinaryCase) (body ordinaryCase)
        (depth ordinaryCase) (ordinary ordinaryCase) ∧
      Correct (entry ordinaryCase) (body ordinaryCase) (depth ordinaryCase) (ordinary ordinaryCase) ∧
      InternedFreshOrdinaryDepthHeap.usesLocal (depth ordinaryCase) (ordinary ordinaryCase) = false ∧
      finish true (.mu (entry ordinaryCase) (body ordinaryCase) (depth ordinaryCase) (ordinary ordinaryCase)) =
        result ordinaryCase ∧
      ∀ assignment : Reference → Profile, Equivalent (denote (result ordinaryCase) assignment)
        (denote (ordinary ordinaryCase)
          (shadow (.uninterned (ordinaryLevel (depth ordinaryCase))) (some []) assignment))) ∧
    result false = .empty ∧
    body false = .reference (.interned (entry false).identity) ∧
    body true = result true ∧ (body true).free = [] ∧
    ∃ identity rows level free, result true = .node identity rows level free ∧ rows ≠ [] := checked

end MicroCFTA.StoredMuUnusedProfileKernels
