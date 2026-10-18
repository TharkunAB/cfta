import MicroCFTA.SourceCurrentRequiredPrimaryOrigins
import MicroCFTA.SourceCurrentMuEndpoint
import MicroCFTA.SourceCurrentRequiredEndpoints

/-!
# Required can change a false primary class to a true primary class

The source is a closed used Mu. Its ordinary body has a union child.
The class has two distinct paths and a coherent normalized record.
Required exposes the body and keeps the selected union endpoint.
The primary gate then returns true. Both selected endpoints remain closed.
This example does not refute structural guard provenance or language preservation.
-/
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000
namespace MicroCFTA.SourceCurrentRequiredPrimaryRetentionBoundary
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedConstruction
open InternedNestedProvenance (Values)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Heap" => State Symbol Guard
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) :=
  SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private def plain : Guard := ⟨some [],.top⟩
private def leaf : Syntax Symbol Guard := .node [.mk ("leaf",.top) plain []]
private def expression : Syntax Symbol Guard :=
  .binder false (.node [.mk ("outer",.top) plain [.union [.var 0,leaf],leaf]])
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Node := match built with | .done value _ => value | .pending .. => .empty
private def heap : Heap := built.state
private def paths : EqualityNormalize.Class := [[0,0],[0,1]]
private def record := (SourceEqualityClassOrder.recordOf paths).getD ⟨.empty,[]⟩
private noncomputable def called := SourceEqualityRequiredExecution.requireAll 8 8
  (record.paths.map (List.map Int.ofNat)) [root] heap
private noncomputable def outputs : List Node := match called with | .done results _ => results | _ => []
private noncomputable def after : Heap := match called with | .done _ final => final | _ => heap
private theorem built_done : InternedFreshOrdinaryConstruction.build expression [] empty = .done root heap := by cbv
private theorem record_paths : record.paths = paths := by cbv
private theorem coherent : SourceEqualityClassOrder.Coherent record := by
  obtain ⟨actual,done,checked,_⟩ := SourceEqualityClassOrder.recordOf_complete paths
    ((EqualityTrie.toPathTrie_succeeds_iff _).mp
      ⟨.branch [(0,.branch [(0,.terminal),(1,.terminal)])],by cbv⟩)
  have same : actual = record := Option.some.inj (done.symm.trans (by cbv))
  exact same ▸ checked
private theorem active : EqualityNormalize.Nontrivial record.paths := by
  rw [record_paths]
  exact ⟨[0,0],by simp [paths],[0,1],by simp [paths],by decide⟩
private theorem normalized : EqualityNormalize.mkEqConstraints 4 [record.paths] = .normalized [record.paths] := by cbv
private theorem semantic : SourceEqualityRequiredSemanticCache.SemanticReady heap :=
  SourceEqualityRequiredSemanticCache.constructed expression root heap built_done
private theorem costs : InternedFreshOrdinaryCostHeap.Heap heap := by
  simpa only [built_done,Outcome.state] using InternedFreshOrdinaryCosts.closed_heap expression
private theorem normal : SourceCurrentRequiredUnionNormal.UnionNormal heap := by
  simpa only [built_done,Outcome.state] using SourceCurrentRequiredUnionNormal.source expression
private theorem guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain heap := by
  simpa only [built_done,Outcome.state] using SourceCurrentConstrainedCapGuardExecution.closed_heap Plain expression
private theorem available : Values heap [root] := by
  intro value member
  cases List.mem_singleton.mp member
  exact (InternedFreshOrdinaryFacts.closed_verified expression).result root heap built_done
private theorem used : ∃ entry body depth ordinary,
    root = .mu entry body depth ordinary ∧ .interned entry.identity ∈ body.free ∧
      InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true ∧ root.free = [] := by
  have checked : (match root with
      | .mu entry body depth ordinary => .interned entry.identity ∈ body.free ∧
          InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true ∧
            (Value.mu entry body depth ordinary).free = []
      | _ => False) := by
    cbv
    trivial
  cases same : root with
  | mu entry body depth ordinary => exact ⟨entry,body,depth,ordinary,rfl,by simpa only [same] using checked⟩
  | empty | reference | node | union => simp only [same] at checked
private theorem before_false : SourceCurrentMuEndpoint.classMeets true source reaches 8
    [root] record.paths heap = .done (some false) heap := by cbv
private theorem before_trace : EndpointStatefulGateTrace.ClassTrace source reaches [root] record.paths heap false heap :=
  EndpointStatefulGateTrace.class_trace_of_done source reaches 8 [root] record.paths heap false heap
    (by simpa only [SourceCurrentMuEndpoint.primary_class] using before_false)
private theorem called_done : called = .done outputs after := by cbv
private theorem after_true : SourceCurrentMuEndpoint.classMeets true source reaches 8
    outputs record.paths after = .done (some true) after := by cbv
private theorem after_trace : EndpointStatefulGateTrace.ClassTrace source reaches outputs record.paths after true after :=
  EndpointStatefulGateTrace.class_trace_of_done source reaches 8 outputs record.paths after true after
    (by simpa only [SourceCurrentMuEndpoint.primary_class] using after_true)
private theorem no_after_false : ¬ EndpointStatefulGateTrace.ClassTrace source reaches outputs record.paths after false after := by
  intro falseTrace
  have impossible := (EndpointStatefulGateTrace.class_trace_unique source reaches outputs record.paths after
    false true after after falseTrace after_trace).1
  cases impossible
private theorem endpoints : ∀ path ∈ record.paths,
    SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) outputs := by
  have ready := SourceEqualityExposureCosts.gate_ready semantic costs
  have done : SourceEqualityRequiredExecution.requireAll 8 8 (SourceEqualitySelectedRequired.paths [record.paths])
      [root] heap = .done outputs after := by
    have encoded : SourceEqualitySelectedRequired.paths [record.paths] = record.paths.map (List.map Int.ofNat) := by cbv
    simpa only [encoded] using (show SourceEqualityRequiredExecution.requireAll 8 8
      (record.paths.map (List.map Int.ofNat)) [root] heap = .done outputs after from called_done)
  have closed := SourceCurrentRequiredEndpoints.selected_paths_closed source reaches heap semantic ready
    [record.paths] [root] available (by intro selected member; cases List.mem_singleton.mp member; exact before_trace)
    8 8 outputs heap after done semantic available (grows_refl heap)
  intro path member
  apply closed path (by simpa only [List.flatten_cons,List.flatten_nil,List.append_nil] using member)
  rw [record_paths] at member
  simp only [paths,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl <;> intro impossible <;> cases impossible

private theorem witness :
    ∃ (expression : Syntax Symbol Guard) (root : Node) (before after : Heap)
      (record : SourceEqualityClassOrder.Record) (results : List Node),
      InternedFreshOrdinaryConstruction.build expression [] empty = .done root before ∧
      (∃ entry body depth ordinary, root = .mu entry body depth ordinary ∧
        .interned entry.identity ∈ body.free ∧ InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true ∧ root.free = []) ∧
      SourceEqualityRequiredSemanticCache.SemanticReady before ∧ InternedFreshOrdinaryCostHeap.Heap before ∧
      SourceCurrentRequiredUnionNormal.UnionNormal before ∧ SourceCurrentConstrainedCapGuardHeap.Heap Plain before ∧
      Values before [root] ∧ record.paths = [[0,0],[0,1]] ∧ SourceEqualityClassOrder.Coherent record ∧
      EqualityNormalize.Nontrivial record.paths ∧
      EqualityNormalize.mkEqConstraints 4 [record.paths] = .normalized [record.paths] ∧
      EndpointStatefulGateTrace.ClassTrace source reaches [root] record.paths before false before ∧
      SourceCurrentMuEndpoint.classMeets true source reaches 8 [root] record.paths before = .done (some false) before ∧
      SourceEqualityRequiredExecution.requireAll 8 8 (record.paths.map (List.map Int.ofNat)) [root] before = .done results after ∧
      SourceCurrentMuEndpoint.classMeets true source reaches 8 results record.paths after = .done (some true) after ∧
      (¬ EndpointStatefulGateTrace.ClassTrace source reaches results record.paths after false after) ∧
      (∀ path ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) results) := by
  exact ⟨expression,root,heap,after,record,outputs,built_done,used,semantic,costs,normal,guards,available,
    record_paths,coherent,active,normalized,before_trace,before_false,called_done,after_true,no_after_false,endpoints⟩

/-- A normalized active class can become primary-true after actual successful Required exposure. -/
theorem required_changes_primary :
    ∃ (expression : Syntax Symbol Guard) (root : Node) (before after : Heap)
      (record : SourceEqualityClassOrder.Record) (results : List Node),
      InternedFreshOrdinaryConstruction.build expression [] empty = .done root before ∧
      (∃ entry body depth ordinary, root = .mu entry body depth ordinary ∧
        .interned entry.identity ∈ body.free ∧ InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true ∧ root.free = []) ∧
      SourceEqualityRequiredSemanticCache.SemanticReady before ∧ InternedFreshOrdinaryCostHeap.Heap before ∧
      SourceCurrentRequiredUnionNormal.UnionNormal before ∧ SourceCurrentConstrainedCapGuardHeap.Heap Plain before ∧
      Values before [root] ∧ record.paths = [[0,0],[0,1]] ∧ SourceEqualityClassOrder.Coherent record ∧
      EqualityNormalize.Nontrivial record.paths ∧
      EqualityNormalize.mkEqConstraints 4 [record.paths] = .normalized [record.paths] ∧
      EndpointStatefulGateTrace.ClassTrace source reaches [root] record.paths before false before ∧
      SourceCurrentMuEndpoint.classMeets true source reaches 8 [root] record.paths before = .done (some false) before ∧
      SourceEqualityRequiredExecution.requireAll 8 8 (record.paths.map (List.map Int.ofNat)) [root] before = .done results after ∧
      SourceCurrentMuEndpoint.classMeets true source reaches 8 results record.paths after = .done (some true) after ∧
      (¬ EndpointStatefulGateTrace.ClassTrace source reaches results record.paths after false after) ∧
      (∀ path ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) results) := witness
end MicroCFTA.SourceCurrentRequiredPrimaryRetentionBoundary
