import MicroCFTA.SourceCurrentBuildStructuralRowOrigins

/-!
# Actual Nat and Bool source row cases

The cases retain completed source calls. The node case separates the source
index from the canonical output index. The binder case reads an earlier
stored payload through different current syntax.
-/
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000
namespace MicroCFTA.BuildRowOriginsKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedFreshOrdinaryConstruction (build buildEdges)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentBuildStructuralRowOrigins (SourceRow build_row_origin)
open SourceCurrentStoredLiteralRowLineage (RowAt)
local notation "Node" => Value Nat Bool
local notation "Row" => EdgeValue Nat Bool
local notation "Heap" => State Nat Bool

private def value (called : Outcome Nat Bool Node) : Node :=
  match called with | .done result _ => result | .pending .. => .empty
private def row0 (result : Node) : Row :=
  (nodeEdges result)[0]?.getD (run (makeEdge 0 false []) (empty : Heap)).1
private def seedSource : Syntax Nat Bool := .node [.mk 3 true []]
private def seedCall := build seedSource [] (empty : Heap)
private def seed : Node := value seedCall
private def seedHeap : Heap := seedCall.state
private def nodeRows : List (EdgeSyntax Nat Bool) :=
  [.mk 9 false [],.mk 3 true [],.mk 9 false []]
private def nodeSource : Syntax Nat Bool := .node nodeRows
private def nodeCall := build nodeSource [] seedHeap
private def nodeValue : Node := value nodeCall
private def nodeHeap : Heap := nodeCall.state
private def nodeRow : Row := row0 nodeValue
private def unionSource : Syntax Nat Bool := .union [.empty,seedSource]
private def unionCall := build unionSource [] (empty : Heap)
private def unionValue : Node := value unionCall
private def unionHeap : Heap := unionCall.state
private def unionRow : Row := row0 unionValue
private def bodySource : Syntax Nat Bool := .node [.mk 7 false [.var 0]]
private def creator : Syntax Nat Bool := .binder false bodySource
private def coldCall := build creator [] (empty : Heap)
private def muValue : Node := value coldCall
private def muHeap : Heap := coldCall.state
private def requester : Syntax Nat Bool := .binder false (.union [.empty,bodySource])
private def muBody : Node := match muValue with | .mu _ body _ _ => body | _ => .empty
private def muEntry := match muValue with
  | .mu entry _ _ _ => entry
  | _ => (Cache.intern (empty : Heap).nodes .empty).1
private def muDepth : Node := match muValue with | .mu _ _ depth _ => depth | _ => .empty
private def muOrdinary : Node := match muValue with | .mu _ _ _ ordinary => ordinary | _ => .empty
private def muRow : Row := row0 muBody
private def cleanSource : Syntax Nat Bool := .binder true (.node [.mk 8 true []])
private def cleanCall := build cleanSource [] (empty : Heap)
private def cleanValue : Node := value cleanCall
private def cleanHeap : Heap := cleanCall.state
private def cleanEntry := match cleanValue with
  | .node entry _ _ _ => entry
  | _ => (Cache.intern (empty : Heap).nodes .empty).1
private def cleanRow : Row := row0 cleanValue

private theorem seed_done : build seedSource [] (empty : Heap) = .done seed seedHeap := by cbv
private theorem node_done : build nodeSource [] seedHeap = .done nodeValue nodeHeap := by cbv
private theorem union_done : build unionSource [] (empty : Heap) = .done unionValue unionHeap := by cbv
private theorem cold_done : build creator [] (empty : Heap) = .done muValue muHeap := by cbv
private theorem warm_done : build requester [] muHeap = .done muValue muHeap := by cbv
private theorem capture_done : build (.var 0) [unionValue] unionHeap = .done unionValue unionHeap := by
  simp only [build,List.getElem?_cons_zero,Option.getD_some]
private theorem clean_done : build cleanSource [] (empty : Heap) = .done cleanValue cleanHeap := by cbv
private theorem node_part : RowAt nodeValue nodeRow := by
  cbv
  exact .node (index := 0) rfl
private theorem union_part : RowAt unionValue unionRow := by
  cbv
  exact .node (index := 0) rfl
private theorem mu_part : RowAt muValue muRow := by
  cbv
  exact .mu (.node (index := 0) rfl)
private theorem clean_part : RowAt cleanValue cleanRow := by
  cbv
  exact .node (index := 0) rfl
private theorem seed_context : Context seedHeap [] := by
  simpa only [seedCall,seed_done,Outcome.state] using
    (SourceCurrentConstrainedCapSourceHistory.empty_context (Symbol := Nat) (Guard := Bool)).build seedSource
private theorem mu_context : Context muHeap [] := by
  simpa only [coldCall,cold_done,Outcome.state] using
    (SourceCurrentConstrainedCapSourceHistory.empty_context (Symbol := Nat) (Guard := Bool)).build creator
private theorem captured_context : Context unionHeap [unionValue] := by
  have context : Context unionHeap [] := by
    simpa only [unionCall,union_done,Outcome.state] using
      (SourceCurrentConstrainedCapSourceHistory.empty_context (Symbol := Nat) (Guard := Bool)).build unionSource
  have available : Available unionHeap unionValue :=
    (InternedFreshOrdinaryFacts.closed_verified unionSource).result unionValue unionHeap union_done
  refine ⟨{context.base with inputs := ?_},context.depth⟩
  intro selected member
  have same : selected = unionValue := by simpa only [List.mem_singleton] using member
  subst selected
  exact available

private theorem checked_witness :
    build seedSource [] (empty : Heap) = .done seed seedHeap ∧
    build nodeSource [] seedHeap = .done nodeValue nodeHeap ∧
    nodeRows[1]? = some (.mk 3 true []) ∧
    nodeRows[0]? = nodeRows[2]? ∧
    (nodeEdges nodeValue).length = 2 ∧
    (nodeEdges nodeValue)[0]? = some nodeRow ∧ nodeRow.entry.key.symbol = 3 ∧
    SourceRow nodeSource [] seedHeap nodeValue nodeHeap nodeRow ∧
    build unionSource [] (empty : Heap) = .done unionValue unionHeap ∧
    SourceRow unionSource [] (empty : Heap) unionValue unionHeap unionRow ∧
    build (.var 0) [unionValue] unionHeap = .done unionValue unionHeap ∧
    SourceRow (.var 0) [unionValue] unionHeap unionValue unionHeap unionRow ∧
    build creator [] (empty : Heap) = .done muValue muHeap ∧
    creator ≠ requester ∧
    build requester [] muHeap = .done muValue muHeap ∧
    SourceRow requester [] muHeap muValue muHeap muRow ∧
    (∃ entry body depth ordinary, muValue = .mu entry body depth ordinary ∧
      InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true ∧
      muHeap.nodeRecords (muKey depth ordinary) = some muValue) ∧
    build cleanSource [] (empty : Heap) = .done cleanValue cleanHeap ∧
    (∃ entry rows depth free, cleanValue = .node entry rows depth free) ∧
    SourceRow cleanSource [] (empty : Heap) cleanValue cleanHeap cleanRow := by
  refine ⟨seed_done,node_done,?_,?_,?_,?_,?_,?_,union_done,?_,?_,?_,cold_done,?_,warm_done,?_,?_,clean_done,?_,?_⟩
  · rfl
  · rfl
  · cbv
  · cbv
  · cbv
  · exact build_row_origin nodeSource [] seedHeap nodeValue nodeHeap seed_context node_done nodeRow node_part
  · exact build_row_origin unionSource [] empty unionValue unionHeap
      SourceCurrentConstrainedCapSourceHistory.empty_context union_done unionRow union_part
  · exact capture_done
  · exact build_row_origin (.var 0) [unionValue] unionHeap unionValue unionHeap captured_context capture_done unionRow union_part
  · intro same
    cases same
  · exact build_row_origin requester [] muHeap muValue muHeap mu_context warm_done muRow mu_part
  · refine ⟨muEntry,muBody,muDepth,muOrdinary,?_,?_,?_⟩ <;> cbv
  · refine ⟨cleanEntry,nodeEdges cleanValue,cleanValue.depth,cleanValue.free,?_⟩
    cbv
  · exact build_row_origin cleanSource [] empty cleanValue cleanHeap
      SourceCurrentConstrainedCapSourceHistory.empty_context clean_done cleanRow clean_part

/-- Actual node, union, capture, warm retained Mu and smart cleanup calls produce source row receipts. -/
theorem actual_builds :
    build seedSource [] (empty : Heap) = .done seed seedHeap ∧
    build nodeSource [] seedHeap = .done nodeValue nodeHeap ∧
    nodeRows[1]? = some (.mk 3 true []) ∧
    nodeRows[0]? = nodeRows[2]? ∧
    (nodeEdges nodeValue).length = 2 ∧
    (nodeEdges nodeValue)[0]? = some nodeRow ∧ nodeRow.entry.key.symbol = 3 ∧
    SourceRow nodeSource [] seedHeap nodeValue nodeHeap nodeRow ∧
    build unionSource [] (empty : Heap) = .done unionValue unionHeap ∧
    SourceRow unionSource [] (empty : Heap) unionValue unionHeap unionRow ∧
    build (.var 0) [unionValue] unionHeap = .done unionValue unionHeap ∧
    SourceRow (.var 0) [unionValue] unionHeap unionValue unionHeap unionRow ∧
    build creator [] (empty : Heap) = .done muValue muHeap ∧
    creator ≠ requester ∧
    build requester [] muHeap = .done muValue muHeap ∧
    SourceRow requester [] muHeap muValue muHeap muRow ∧
    (∃ entry body depth ordinary, muValue = .mu entry body depth ordinary ∧
      InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true ∧
      muHeap.nodeRecords (muKey depth ordinary) = some muValue) ∧
    build cleanSource [] (empty : Heap) = .done cleanValue cleanHeap ∧
    (∃ entry rows depth free, cleanValue = .node entry rows depth free) ∧
    SourceRow cleanSource [] (empty : Heap) cleanValue cleanHeap cleanRow := checked_witness

end MicroCFTA.BuildRowOriginsKernels
