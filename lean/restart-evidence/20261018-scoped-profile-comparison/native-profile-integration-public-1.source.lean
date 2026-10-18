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
private theorem heap (smart used : Bool) : Heap Correct (reader smart used) := by
  intro other actualEntry actualBody actualDepth actualOrdinary installed
  cases smart <;> cases used <;> cbv at installed
  all_goals try simp only [Cache.put] at installed
  all_goals repeat' first | split at installed | cases installed
  all_goals
    intro assignment replacement
    cases replacement with
    | none => cbv; exact ⟨Iff.rfl,fun _ => Iff.rfl⟩
    | some names => cases names <;> cbv <;> exact ⟨Iff.rfl,fun _ => Iff.rfl⟩

private theorem native (smart used warm : Bool) (assignment : Reference → Profile) :
    ∃ depth afterDepth ordinary cut chosen original marker,
      callback (expression used) [] .depth (entryHeap smart used warm) = .done depth afterDepth ∧
      callback (expression used) [] (.uninterned (ordinaryLevel depth)) afterDepth = .done ordinary cut ∧
      (reader smart used).nodeRecords (muKey depth ordinary) = some (.mu chosen original depth ordinary) ∧
      result smart used = finish smart (.mu chosen original depth ordinary) ∧
      Correct chosen original depth ordinary ∧
      (∀ leaf ∈ leaves original, marker ∉ (match leaf with
        | .reference name => assignment name | _ => profile leaf).getD []) ∧
      Equivalent (denote (result smart used) assignment)
        (if !smart || usesLocal depth ordinary then
          if (Value.mu chosen original depth ordinary).free.isEmpty then none
          else erase marker (denote ordinary (shadow (.uninterned (ordinaryLevel depth)) (some [marker]) assignment))
        else denote ordinary (shadow (.uninterned (ordinaryLevel depth)) (some []) assignment)) := by
  obtain ⟨depth,afterDepth,ordinary,cut,chosen,original,marker,depthDone,ordinaryDone,installed,returned,correct,fresh,matched⟩ :=
    SourceCurrentNativeBinderProfile.build_profile smart (expression used) [] (entryHeap smart used warm)
      (context smart used warm) (result smart used) (reader smart used) (done smart used warm) (heap smart used) assignment
  refine ⟨depth,afterDepth,ordinary,cut,chosen,original,marker,depthDone,ordinaryDone,installed,returned,correct,?_,matched⟩
  intro leaf member
  cases leaf <;> exact fresh _ member

private theorem complete_finish (smart used : Bool) (assignment : Reference → Profile) :
    ∃ marker : Reference,
      (∀ leaf ∈ leaves (body smart used), marker ∉ (match leaf with
        | .reference name => assignment name | _ => profile leaf).getD []) ∧
      Equivalent (denote (result smart used) assignment)
        (if !smart || usesLocal (depthValue used) (ordinaryValue used) then
          if (Value.mu (entry smart used) (body smart used) (depthValue used) (ordinaryValue used)).free.isEmpty then none
          else erase marker (denote (ordinaryValue used)
            (shadow (.uninterned (ordinaryLevel (depthValue used))) (some [marker]) assignment))
        else denote (ordinaryValue used)
          (shadow (.uninterned (ordinaryLevel (depthValue used))) (some []) assignment)) := by
  have correct := heap smart used _ _ _ _ _ (present smart used)
  obtain ⟨marker,fresh,_⟩ := SourceCurrentStoredMuFinishProfile.complete smart (entry smart used)
    (body smart used) (depthValue used) (ordinaryValue used) assignment (reader smart used)
    (ready smart used).semantic.1.normal.facts.coherent (available smart used) (depth_correct smart used) correct
  refine ⟨marker,?_,?_⟩
  · intro leaf member
    cases leaf <;> exact fresh _ member
  rw [← returned smart used]
  exact SourceCurrentStoredMuFinishProfile.finish_profile smart (entry smart used)
    (body smart used) (depthValue used) (ordinaryValue used) assignment (reader smart used)
    (ready smart used).semantic.1.normal.facts.coherent (available smart used) (depth_correct smart used) correct marker fresh

private theorem checked :
    ∀ smart used : Bool,
      Ready (reader smart used) ∧ Heap Correct (reader smart used) ∧
      (reader smart used).nodeRecords (key used) =
        some (.mu (entry smart used) (body smart used) (depthValue used) (ordinaryValue used)) ∧
      (Value.mu (entry smart used) (body smart used) (depthValue used) (ordinaryValue used)).free = [] ∧
      usesLocal (depthValue used) (ordinaryValue used) = used ∧
      (if smart && !used then result smart used = .empty
        else result smart used = .mu (entry smart used) (body smart used) (depthValue used) (ordinaryValue used)) ∧
      (∀ warm : Bool,
        build (source smart used) [] (entryHeap smart used warm) = .done (result smart used) (reader smart used) ∧
        ∀ assignment : Reference → Profile,
        ∃ depth afterDepth ordinary cut chosen original marker,
          callback (expression used) [] .depth (entryHeap smart used warm) = .done depth afterDepth ∧
          callback (expression used) [] (.uninterned (ordinaryLevel depth)) afterDepth = .done ordinary cut ∧
          (reader smart used).nodeRecords (muKey depth ordinary) = some (.mu chosen original depth ordinary) ∧
          result smart used = finish smart (.mu chosen original depth ordinary) ∧
          Correct chosen original depth ordinary ∧
          (∀ leaf ∈ leaves original, marker ∉ (match leaf with
            | .reference name => assignment name | _ => profile leaf).getD []) ∧
          Equivalent (denote (result smart used) assignment)
            (if !smart || usesLocal depth ordinary then
              if (Value.mu chosen original depth ordinary).free.isEmpty then none
              else erase marker (denote ordinary (shadow (.uninterned (ordinaryLevel depth)) (some [marker]) assignment))
            else denote ordinary (shadow (.uninterned (ordinaryLevel depth)) (some []) assignment))) ∧
      (∀ assignment : Reference → Profile,
        ∃ marker : Reference,
          (∀ leaf ∈ leaves (body smart used), marker ∉ (match leaf with
            | .reference name => assignment name | _ => profile leaf).getD []) ∧
          Equivalent (denote (result smart used) assignment)
            (if !smart || usesLocal (depthValue used) (ordinaryValue used) then
              if (Value.mu (entry smart used) (body smart used) (depthValue used) (ordinaryValue used)).free.isEmpty then none
              else erase marker (denote (ordinaryValue used)
                (shadow (.uninterned (ordinaryLevel (depthValue used))) (some [marker]) assignment))
            else denote (ordinaryValue used)
              (shadow (.uninterned (ordinaryLevel (depthValue used))) (some []) assignment))) := by
  intro smart used
  refine ⟨ready smart used,heap smart used,present smart used,?_,?_,?_,
    fun warm => ⟨done smart used warm,native smart used warm⟩,complete_finish smart used⟩
  · cases smart <;> cases used <;> cbv
  · cases smart <;> cases used <;> cbv
  · cases smart <;> cases used <;> cbv

/-- Actual raw and smart source calls derive the cache contract and both cold and warm profile receipts. -/
theorem actual_binder_returns :
    ∀ smart used : Bool,
      Ready (reader smart used) ∧ Heap Correct (reader smart used) ∧
      (reader smart used).nodeRecords (key used) =
        some (.mu (entry smart used) (body smart used) (depthValue used) (ordinaryValue used)) ∧
      (Value.mu (entry smart used) (body smart used) (depthValue used) (ordinaryValue used)).free = [] ∧
      usesLocal (depthValue used) (ordinaryValue used) = used ∧
      (if smart && !used then result smart used = .empty
        else result smart used = .mu (entry smart used) (body smart used) (depthValue used) (ordinaryValue used)) ∧
      (∀ warm : Bool,
        build (source smart used) [] (entryHeap smart used warm) = .done (result smart used) (reader smart used) ∧
        ∀ assignment : Reference → Profile,
        ∃ depth afterDepth ordinary cut chosen original marker,
          callback (expression used) [] .depth (entryHeap smart used warm) = .done depth afterDepth ∧
          callback (expression used) [] (.uninterned (ordinaryLevel depth)) afterDepth = .done ordinary cut ∧
          (reader smart used).nodeRecords (muKey depth ordinary) = some (.mu chosen original depth ordinary) ∧
          result smart used = finish smart (.mu chosen original depth ordinary) ∧
          Correct chosen original depth ordinary ∧
          (∀ leaf ∈ leaves original, marker ∉ (match leaf with
            | .reference name => assignment name | _ => profile leaf).getD []) ∧
          Equivalent (denote (result smart used) assignment)
            (if !smart || usesLocal depth ordinary then
              if (Value.mu chosen original depth ordinary).free.isEmpty then none
              else erase marker (denote ordinary (shadow (.uninterned (ordinaryLevel depth)) (some [marker]) assignment))
            else denote ordinary (shadow (.uninterned (ordinaryLevel depth)) (some []) assignment))) ∧
      (∀ assignment : Reference → Profile,
        ∃ marker : Reference,
          (∀ leaf ∈ leaves (body smart used), marker ∉ (match leaf with
            | .reference name => assignment name | _ => profile leaf).getD []) ∧
          Equivalent (denote (result smart used) assignment)
            (if !smart || usesLocal (depthValue used) (ordinaryValue used) then
              if (Value.mu (entry smart used) (body smart used) (depthValue used) (ordinaryValue used)).free.isEmpty then none
              else erase marker (denote (ordinaryValue used)
                (shadow (.uninterned (ordinaryLevel (depthValue used))) (some [marker]) assignment))
            else denote (ordinaryValue used)
              (shadow (.uninterned (ordinaryLevel (depthValue used))) (some []) assignment))) := checked

end MicroCFTA.NativeBinderProfileIntegration

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.NativeBinderProfileIntegration.actual_binder_returns
#print MicroCFTA.NativeBinderProfileIntegration.actual_binder_returns
#print axioms MicroCFTA.NativeBinderProfileIntegration.actual_binder_returns
