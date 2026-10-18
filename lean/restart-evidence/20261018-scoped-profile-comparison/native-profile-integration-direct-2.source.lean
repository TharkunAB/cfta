import MicroCFTA.SourceCurrentNativeBinderProfile
import MicroCFTA.SourceEqualityRequiredCache
set_option linter.all true
namespace MicroCFTA.NativeBinderProfileIntegration
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome finish)
open InternedFreshOrdinaryConstruction (build ordinaryLevel)
open InternedFreshOrdinaryFacts (callback)
open InternedFreshOrdinaryDepthHeap (usesLocal)
open InternedBinderProtocol (Reference NodeKey)
open InternedRootProfile (Profile profile Equivalent)
open InternedStoredSubstitution (leaves)
open SourceCurrentStoredProfileFunction (denote)
open SourceCurrentStoredMuProfileContract (shadow Correct)
open SourceCurrentStoredMuTrackedProfile (erase)
open SourceCurrentPublicationHeapInduction (Heap)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceEqualityRequiredCache (Ready)
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

private def expression (used : Bool) : Syntax Nat Bool :=
  if used then .node [.mk 7 false [.var 0]] else .var 0
private def source (smart used : Bool) : Syntax Nat Bool := .binder smart (expression used)
private def actual (smart used : Bool) := build (source smart used) [] empty
private def result (smart used : Bool) : Value Nat Bool :=
  match actual smart used with | .done value _ => value | .pending .. => .empty
private def reader (smart used : Bool) := (actual smart used).state
private def depthCall (used : Bool) := callback (expression used) [] .depth (empty : State Nat Bool)
private def depthValue (used : Bool) := match depthCall used with | .done value _ => value | .pending .. => .empty
private def ordinaryCall (used : Bool) := callback (expression used) [] (.uninterned (ordinaryLevel (depthValue used))) (depthCall used).state
private def ordinaryValue (used : Bool) := match ordinaryCall used with | .done value _ => value | .pending .. => .empty
private def key (used : Bool) := muKey (depthValue used) (ordinaryValue used)
private def stored (smart used : Bool) := ((reader smart used).nodeRecords (key used)).getD .empty
private def entry (smart used : Bool) : Interned NodeKey := match stored smart used with | .mu entry _ _ _ => entry | _ => ⟨0,.node []⟩
private def body (smart used : Bool) := match stored smart used with | .mu _ body _ _ => body | _ => .empty
private def entryHeap (smart used warm : Bool) := if warm then reader smart used else empty
private theorem done (smart used warm : Bool) :
    build (source smart used) [] (entryHeap smart used warm) = .done (result smart used) (reader smart used) := by
  cases smart <;> cases used <;> cases warm <;> cbv
private theorem ready (smart used : Bool) : Ready (reader smart used) :=
  SourceEqualityRequiredCache.constructed _ _ _ (by simpa only [entryHeap,Bool.false_eq_true,ite_false] using done smart used false)
private theorem context (smart used warm : Bool) : Context (entryHeap smart used warm) [] := by
  cases warm with
  | false => exact SourceCurrentConstrainedCapSourceHistory.empty_context
  | true => exact SourceCurrentConstrainedCapSourceHistory.empty_context.build (source smart used)
private theorem present (smart used : Bool) :
    (reader smart used).nodeRecords (key used) =
      some (.mu (entry smart used) (body smart used) (depthValue used) (ordinaryValue used)) := by
  cases smart <;> cases used <;> cbv
private theorem available (smart used : Bool) :
    Available (reader smart used) (.mu (entry smart used) (body smart used) (depthValue used) (ordinaryValue used)) :=
  (ready smart used).semantic.1.normal.facts.cached.nodes _ _ (present smart used)
private theorem depth_correct (smart used : Bool) :
    InternedFreshOrdinaryDepthHeap.Correct (entry smart used) (body smart used) (depthValue used) (ordinaryValue used) :=
  (SourceCurrentConstrainedCapSourceHistory.empty_context.build (source smart used)).depth _ _ _ _ _ (present smart used)
private theorem returned (smart used : Bool) :
    finish smart (.mu (entry smart used) (body smart used) (depthValue used) (ordinaryValue used)) = result smart used := by
  cases smart <;> cases used <;> cbv
private theorem correct (smart used : Bool) :
    Correct (entry smart used) (body smart used) (depthValue used) (ordinaryValue used) := by
  intro assignment replacement
  cases smart <;> cases used <;>
    cases replacement with
    | none => cbv; exact ⟨Iff.rfl,fun _ => Iff.rfl⟩
    | some names => cases names <;> cbv <;> exact ⟨Iff.rfl,fun _ => Iff.rfl⟩
private theorem heap (smart used : Bool) : Heap Correct (reader smart used) := by
  intro other actualEntry actualBody actualDepth actualOrdinary installed
  cases smart <;> cases used <;> cbv at installed
  all_goals repeat' first | split at installed | cases installed
  all_goals first | exact correct false false | exact correct false true | exact correct true false | exact correct true true

end MicroCFTA.NativeBinderProfileIntegration
