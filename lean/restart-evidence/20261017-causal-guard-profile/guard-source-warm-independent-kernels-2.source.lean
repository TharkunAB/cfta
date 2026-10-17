import MicroCFTA.SourceCurrentConstrainedCapGuardExecution

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace MicroCFTA.GuardSourceWarmIndependent
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedConstruction (Syntax Outcome request finish)
open InternedBinderProtocol (NodeKey)
open SourceCurrentConstrainedCapGuardDepth

private def plan : Syntax Nat Bool := .binder false (.union [.var 0,
  .node [.mk 0 false [], .mk 1 false [.empty, .binder false (.node [.mk 2 false [.var 0]])]]])

private def constant (entry : Interned NodeKey) : Value Nat Bool :=
  .node entry [.mk {identity := 0, key := ⟨0, [], false⟩} []] 0 []

private def winnerShape : Value Nat Bool → Prop
  | .mu _ (.node entry edges level free) depth ordinary =>
      Value.node entry edges level free = constant entry ∧
      depth = Value.node entry edges level free ∧ ordinary = Value.node entry edges level free
  | _ => False

set_option cbv.maxSteps 100000000 in
private theorem computed :
    (match InternedFreshOrdinaryConstruction.build plan [] empty with
     | .done value _ => winnerShape value | .pending .. => False) := by cbv

/-- Actual erased rows and nested binders produce the earlier winner law before a smart warm return. -/
theorem constructed_erased_nested_warm :
    ∃ (before : State Nat Bool) (entry : Interned NodeKey) (body : Value Nat Bool),
      InternedFreshOrdinaryConstruction.build plan [] empty = .done (.mu entry body body body) before ∧
      SourceCurrentConstrainedCapGuardHeap.Heap (fun guard : Bool => guard = true) before ∧
      before.nodeRecords (muKey body body) = some (.mu entry body body body) ∧
      request true body body (fun _ state => .done .empty state) before = .done body before ∧
      SourceCurrentConstrainedCap.Cap (fun guard : Bool => guard = true) 1 body ∧
      ¬SourceEqualityAnnotationLanguage.Annotated (fun guard : Bool => guard = true) body ∧
      profile (fun guard : Bool => guard = true) (.mu entry body body body) = none := by
  obtain ⟨value, before, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete plan
  have shaped : winnerShape value := by simpa only [done] using computed
  cases value with
  | empty | reference | node | union => cases shaped
  | mu entry body depth ordinary =>
      cases body with
      | empty | reference | mu | union => cases shaped
      | node root edges level free =>
          obtain ⟨bodySame, rfl, rfl⟩ := shaped
          let body : Value Nat Bool := .node root edges level free
          have same : body = constant root := bodySame
          have observed : profile (fun guard : Bool => guard = true) body = some 1 := by
            classical
            rw [same]
            simp [constant, profile, rows, SourceCurrentConstrainedCapGuardDepth.children, join, raise, guardCost]
          have physical := InternedFreshOrdinaryFacts.closed_verified plan
          have available := physical.result (.mu entry body body body) before done
          have facts : Facts before := by simpa only [done, Outcome.state] using physical.facts
          have ownPresent : before.nodeRecords entry.key = some (.mu entry body body body) := available.resident _ rfl
          obtain ⟨_, _, fields⟩ := facts.coherent.nodes _ _ ownPresent
          have keySame : entry.key = muKey body body := fields.2
          have present : before.nodeRecords (muKey body body) = some (.mu entry body body body) := by
            simpa only [keySame] using ownPresent
          have bodyAvailable : Available before body := available.children body (by simp [InternedProbeProvenance.children])
          have depthHeap : InternedFreshOrdinaryDepthHeap.Heap before := by
            simpa only [done, Outcome.state] using (SourceCurrentConstrainedCapSourceHistory.empty_context.build plan).depth
          have guardHeap : SourceCurrentConstrainedCapGuardHeap.Heap (fun guard : Bool => guard = true) before := by
            simpa only [done, Outcome.state] using SourceCurrentConstrainedCapGuardExecution.closed_heap (fun guard : Bool => guard = true) plan
          have unused : InternedFreshOrdinaryDepthHeap.usesLocal body body = false := by
            rw [same]
            simp [InternedFreshOrdinaryDepthHeap.usesLocal, constant, InternedDeepFreeDepth.deepNames]
          have bounded : SourceCurrentConstrainedCap.Cap (fun guard : Bool => guard = true) 1 body :=
            (profile_minimal _ _ _ observed 1).mpr (Nat.le_refl _)
          have returned := SourceCurrentConstrainedCapGuardReadback.hit_cap
            (fun guard : Bool => guard = true) 1 body body (.mu entry body body body) before facts
            bodyAvailable bodyAvailable depthHeap guardHeap present unused bounded
          have finished : finish true (.mu entry body body body) = body := by
            rw [same]
            rfl
          rw [finished] at returned
          obtain ⟨installed, table, _⟩ := facts.coherent.nodes _ _ present
          have warm : request true body body (fun _ state => .done .empty state) before = .done body before := by
            simp only [InternedNestedConstruction.request, table, present, finished]
          refine ⟨before, entry, body, done, guardHeap, present, warm, returned, ?_, ?_⟩
          · intro annotated
            have zero := (profile_zero_iff _ _).mpr annotated
            rw [observed] at zero
            cases zero
          · simp only [profile, observed, Nat.one_ne_zero, Option.some.injEq, ite_false]

#print axioms constructed_erased_nested_warm
#check @constructed_erased_nested_warm
end MicroCFTA.GuardSourceWarmIndependent
