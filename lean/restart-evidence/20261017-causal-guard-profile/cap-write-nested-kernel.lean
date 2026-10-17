import MicroCFTA.SourceCurrentConstrainedCapGuardDepth
import MicroCFTA.InternedFreshOrdinaryReplay
import MicroCFTA.SourceRecursiveIntersectionSemanticHeap

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

namespace MicroCFTA.CapWriteNestedKernel
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedRecordCoherence
open InternedBinderProtocol (NodeKey Reference)
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentConstrainedCapGuardDepth
private def annotation (guard : Bool) : Prop := guard = true
private def expression : Syntax Nat Bool := .binder false (.binder false (.node [.mk 0 false [.var 1]]))
private def actual := InternedFreshOrdinaryConstruction.build expression [] (empty : State Nat Bool)
private def root := match actual with | .done value _ => value | .pending .. => .empty
private def heap := actual.state
private def chosen := ((heap.nodes.issued 1).bind heap.nodeRecords).getD .empty
private def entry : Interned NodeKey := match chosen with | .mu entry _ _ _ => entry | _ => ⟨0, .node []⟩
private def body := match chosen with | .mu _ body _ _ => body | _ => .empty
private def depth := match chosen with | .mu _ _ depth _ => depth | _ => .empty
private def ordinary := match chosen with | .mu _ _ _ ordinary => ordinary | _ => .empty
private def node : Interned NodeKey := match body with | .node node _ _ _ => node | _ => ⟨0, .node []⟩
private def row : Interned (EdgeKey Nat Bool) :=
  match body with | .node _ [.mk row _] _ _ => row | _ => ⟨0, ⟨0, [], false⟩⟩

set_option cbv.maxSteps 100000000 in
private theorem done : actual = .done root heap := by cbv
private theorem present : heap.nodeRecords (muKey depth ordinary) = some (.mu entry body depth ordinary) := by cbv
private theorem body_shape : body = .node node [.mk row [.reference .depth]] 0 [.depth] := by cbv
private theorem bad_guard : row.key.constraint = false := by cbv
private theorem same_depth : depth = body := by cbv
private theorem same_ordinary : ordinary = body := by cbv
private theorem unused : InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = false := by cbv

private theorem observed_profile : profile annotation body = some 1 := by
  rw [body_shape]
  simp only [profile, rows, SourceCurrentConstrainedCapGuardDepth.children, guardCost, annotation,
    bad_guard, Bool.false_eq_true, ↓reduceIte, join, raise]
  rfl

/-- Nested closed source writes produce nonhereditary finite-cap probes and body in the same cell, then exact warm replay retains that heap. -/
theorem nested_actual_cell_profiles :
    InternedFreshOrdinaryConstruction.build expression [] (empty : State Nat Bool) = .done root heap ∧
      InternedFreshOrdinaryConstruction.build expression [] heap = .done root heap ∧
      heap.nodeRecords (muKey depth ordinary) = some (.mu entry body depth ordinary) ∧
      SourceRecursiveIntersectionSemanticHeap.SemanticHeap heap ∧ Available heap body ∧
      profile annotation body = some 1 ∧ profile annotation depth = some 1 ∧ profile annotation ordinary = some 1 ∧
      Cap annotation 1 depth ∧ Cap annotation 1 ordinary ∧ Cap annotation 1 body ∧ ¬Cap annotation 0 body ∧
      InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = false := by
  have built := done
  have semantic := SourceRecursiveIntersectionSemanticHeap.constructed expression root heap built
  have bodyAvailable := (semantic.1.normal.facts.cached.nodes _ _ present).children body (by simp [InternedProbeProvenance.children])
  have bounded : Cap annotation 1 body := cap_of_profile annotation 1 body (by simp [observed_profile, Within])
  have notZero : ¬Cap annotation 0 body := by
    intro zero
    have impossible := profile_of_cap zero
    simp [observed_profile, Within] at impossible
  have replay := InternedFreshOrdinaryReplay.build_replay expression [] (empty : State Nat Bool) heap root heap
    empty_facts.coherent.valid built (grows_refl heap)
  exact ⟨built, replay, present, semantic, bodyAvailable, observed_profile,
    same_depth ▸ observed_profile, same_ordinary ▸ observed_profile,
    same_depth ▸ bounded, same_ordinary ▸ bounded, bounded, notZero, unused⟩

#print axioms nested_actual_cell_profiles
#check @nested_actual_cell_profiles
end MicroCFTA.CapWriteNestedKernel
