import MicroCFTA.SourceCurrentOpenWeakSimulation
import MicroCFTA.SourceEqualityRequiredCache

namespace MicroCFTA.PreorderNormalizationReview
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (unfold)
open InternedBinderProtocol (Reference NodeKey)
open InternedEdgeResidency (nodeEdges)
open SourceEqualityRequiredCache (Ready)
open MergedFreshOrdinaryGraph (Origin successors)
open SourceCurrentOpenObservations (Same RowMatch ReferenceOrigin)
open SourceCurrentOpenOriginSteps (Path)
open SourceCurrentOpenWeakSimulation (Forward)
open Productivity (Reachable)

set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

private def value (outcome : Outcome Nat Bool (Value Nat Bool)) : Value Nat Bool :=
  match outcome with | .done result _ => result | .pending .. => .empty
private def leaf (symbol : Nat) : Syntax Nat Bool := .node [.mk symbol false []]
private def source : Syntax Nat Bool := .binder false (.node [.mk 9 false
  [.union [.binder false (leaf 1),.binder false (leaf 2),.var 0],
   .union [leaf 1,leaf 2,.var 0]]])
private def built := build source [] empty
private def root := value built
private def reader := built.state
private def body : Value Nat Bool := match root with | .mu _ body _ _ => body | _ => .empty
private def own : Reference := match root with | .mu entry .. => .interned entry.identity | _ => .depth
private def u : Value Nat Bool := (children body)[0]?.getD .empty
private def v : Value Nat Bool := (children body)[1]?.getD .empty
private def unionMembers : Value Nat Bool → List (Value Nat Bool)
  | .union _ members .. => members | _ => []
private def muA := (unionMembers u)[0]?.getD .empty
private def muB := (unionMembers u)[1]?.getD .empty
private def z : Value Nat Bool := .reference own
private def muBody : Value Nat Bool → Value Nat Bool
  | .mu _ body .. => body | _ => .empty
private def a := muBody muA
private def b := muBody muB
private def merged := (unionMembers v)[0]?.getD .empty
private def rowA : EdgeValue Nat Bool := (nodeEdges a)[0]?.getD ⟨⟨0,⟨0,false,[]⟩⟩,[]⟩
private def rowB : EdgeValue Nat Bool := (nodeEdges b)[0]?.getD ⟨⟨0,⟨0,false,[]⟩⟩,[]⟩

private theorem actual : build source [] empty = .done root reader := by cbv
private theorem ready : Ready reader := SourceEqualityRequiredCache.constructed source root reader actual
private theorem root_available : Available reader root :=
  (InternedFreshOrdinaryFacts.build_verified source [] empty InternedNestedFacts.empty_facts
    (by intro input member; cases member)).result root reader actual
private theorem body_available : Available reader body := by
  apply root_available.children body
  cbv
private theorem u_available : Available reader u := body_available.children u (by cbv)
private theorem v_available : Available reader v := body_available.children v (by cbv)
private theorem made_u : run (makeUnion [muA,muB,z]) reader = (u,reader) := by cbv
private theorem made_v : run (makeUnion [a,b,z]) reader = (v,reader) := by cbv
private theorem unfolded_a : unfold muA reader = .done a reader := by cbv
private theorem unfolded_b : unfold muB reader = .done b reader := by cbv
private theorem su : successors reader u = [muA,muB,z] := by cbv
private theorem sv : successors reader v = [merged,z] := by cbv
private theorem sma : successors reader muA = [a] := by cbv
private theorem smb : successors reader muB = [b] := by cbv
private theorem sa : successors reader a = [] := by cbv
private theorem sb : successors reader b = [] := by cbv
private theorem sm : successors reader merged = [] := by cbv
private theorem sz : successors reader z = [] := by rfl
private theorem na : nodeEdges a = [rowA] := by cbv
private theorem nb : nodeEdges b = [rowB] := by cbv
private theorem nm : nodeEdges merged = [rowA,rowB] := by cbv
private theorem nu : nodeEdges u = [] := by cbv
private theorem nv : nodeEdges v = [] := by cbv
private theorem nma : nodeEdges muA = [] := by cbv
private theorem nmb : nodeEdges muB = [] := by cbv
private theorem nz : nodeEdges z = [] := by rfl

end MicroCFTA.PreorderNormalizationReview
