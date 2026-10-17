import MicroCFTA.SourceCurrentWarmConstructionParts
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
namespace MicroCFTA.WarmConstructionPartsKernels
open Cache InternedConstructorTemplates
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryGrowth InternedFreshOrdinaryReplay
open Language
private def body : Syntax Nat Bool := .node [.mk 7 false [.var 0, .binder true (.node [.mk 8 true [.var 0]])]]
private def expression : Syntax Nat Bool := .binder false body
private def initial := build expression [] (empty : State Nat Bool)
private def value : Value Nat Bool := match initial with | .done value _ => value | .pending .. => .empty
private def common : State Nat Bool := initial.state
private theorem cold : build expression [] empty = .done value common := by cbv
private theorem valid : Valid common := by
  have retained := build_correct expression [] (empty : State Nat Bool) empty_valid
  simpa only [cold, Outcome.state] using retained.1
private theorem nested_proof :
    build expression [] empty = .done value common ∧
    (empty : State Nat Bool).nodes.next < common.nodes.next ∧
    ∃ depth ordinary rawDepth rawOrdinary,
      InternedFreshOrdinaryFacts.callback body [] .depth common = .done depth common ∧
      InternedFreshOrdinaryFacts.callback body [] (.uninterned (ordinaryLevel depth)) common = .done ordinary common ∧
      build body [.reference .depth] common = .done rawDepth common ∧
      run (withoutSelfReference .depth rawDepth) common = (depth, common) ∧
      build body [.reference (.uninterned (ordinaryLevel depth))] common = .done rawOrdinary common ∧
      run (withoutSelfReference (.uninterned (ordinaryLevel depth)) rawOrdinary) common = (ordinary, common) ∧
      request false depth ordinary (InternedFreshOrdinaryFacts.callback body []) common = .done value common := by
  have warm := build_replays expression [] empty common value common empty_valid cold (grows_refl _)
  exact ⟨cold, by cbv, SourceCurrentWarmConstructionParts.binder false body [] common value valid warm⟩
/-- An allocated nested binder derives every raw probe, filter, and request at its actual warm heap. -/
theorem nested :
    build expression [] empty = .done value common ∧
    (empty : State Nat Bool).nodes.next < common.nodes.next ∧
    ∃ depth ordinary rawDepth rawOrdinary,
      InternedFreshOrdinaryFacts.callback body [] .depth common = .done depth common ∧
      InternedFreshOrdinaryFacts.callback body [] (.uninterned (ordinaryLevel depth)) common = .done ordinary common ∧
      build body [.reference .depth] common = .done rawDepth common ∧
      run (withoutSelfReference .depth rawDepth) common = (depth, common) ∧
      build body [.reference (.uninterned (ordinaryLevel depth))] common = .done rawOrdinary common ∧
      run (withoutSelfReference (.uninterned (ordinaryLevel depth)) rawOrdinary) common = (ordinary, common) ∧
      request false depth ordinary (InternedFreshOrdinaryFacts.callback body []) common = .done value common := nested_proof
private def members : List (Syntax Nat Bool) := [.node [.mk 10 true []], .empty]
private def children : List (Syntax Nat Bool) := [.union members, expression]
private def originalRows : List (EdgeSyntax Nat Bool) := [.mk 9 false children]
private def nodeExpression : Syntax Nat Bool := .node originalRows
private def nodeInitial := build nodeExpression [] (empty : State Nat Bool)
private def nodeValue : Value Nat Bool := match nodeInitial with | .done value _ => value | .pending .. => .empty
private def nodeCommon : State Nat Bool := nodeInitial.state
private theorem nodeCold : build nodeExpression [] empty = .done nodeValue nodeCommon := by cbv
private theorem nodeValid : Valid nodeCommon := by
  have retained := build_correct nodeExpression [] (empty : State Nat Bool) empty_valid
  simpa only [nodeCold, Outcome.state] using retained.1
private theorem node_union_proof :
    build nodeExpression [] empty = .done nodeValue nodeCommon ∧
    (empty : State Nat Bool).edges.next < nodeCommon.edges.next ∧
    ∃ row first second values,
      SourceCurrentRowPlanReplay.rowRun (.mk 9 false children) [] nodeCommon = .done row nodeCommon ∧
      run (makeNode [row]) nodeCommon = (nodeValue, nodeCommon) ∧
      buildMany children [] nodeCommon = .done [first, second] nodeCommon ∧
      build expression [] nodeCommon = .done second nodeCommon ∧
      buildMany members [] nodeCommon = .done values nodeCommon ∧
      All₂ (fun plan output => build plan [] nodeCommon = .done output nodeCommon) members values ∧
      run (makeUnion values) nodeCommon = (first, nodeCommon) := by
  have warm := build_replays nodeExpression [] empty nodeCommon nodeValue nodeCommon empty_valid nodeCold (grows_refl _)
  obtain ⟨rows, rowsDone, finalNode⟩ := SourceCurrentWarmConstructionParts.node originalRows [] nodeCommon nodeValue nodeValid warm
  have rowCalls := SourceCurrentWarmConstructionParts.rows originalRows [] nodeCommon rows nodeValid rowsDone
  cases rowCalls with
  | cons rowCall rest =>
      cases rest
      obtain ⟨outputs, childrenDone, edgeDone⟩ := SourceCurrentWarmConstructionParts.bind
        (buildMany children []) (fun values state => work (makeEdge 9 false values) state) nodeCommon _ nodeValid
        (buildMany_correct children []) (fun values => InternedNestedConstruction.work_correct (makeEdge 9 false values))
        (buildMany_replays children []) rowCall
      have childCalls := SourceCurrentWarmConstructionParts.many children [] nodeCommon outputs nodeValid childrenDone
      cases childCalls with
      | cons firstDone rest =>
          cases rest with
          | cons secondDone rest =>
              cases rest
              obtain ⟨values, memberDone, finalUnion⟩ := SourceCurrentWarmConstructionParts.union members [] nodeCommon _ nodeValid firstDone
              exact ⟨nodeCold, by cbv, _, _, _, values, rowCall, finalNode, childrenDone, secondDone,
                memberDone, SourceCurrentWarmConstructionParts.many members [] nodeCommon values nodeValid memberDone, finalUnion⟩
/-- Actual node, row, ordered children, and union calls all replay at the returned allocated heap. -/
theorem node_union :
    build nodeExpression [] empty = .done nodeValue nodeCommon ∧
    (empty : State Nat Bool).edges.next < nodeCommon.edges.next ∧
    ∃ row first second values,
      SourceCurrentRowPlanReplay.rowRun (.mk 9 false children) [] nodeCommon = .done row nodeCommon ∧
      run (makeNode [row]) nodeCommon = (nodeValue, nodeCommon) ∧
      buildMany children [] nodeCommon = .done [first, second] nodeCommon ∧
      build expression [] nodeCommon = .done second nodeCommon ∧
      buildMany members [] nodeCommon = .done values nodeCommon ∧
      All₂ (fun plan output => build plan [] nodeCommon = .done output nodeCommon) members values ∧
      run (makeUnion values) nodeCommon = (first, nodeCommon) := node_union_proof
end MicroCFTA.WarmConstructionPartsKernels
#check @MicroCFTA.WarmConstructionPartsKernels.nested
#print MicroCFTA.WarmConstructionPartsKernels.nested
#print axioms MicroCFTA.WarmConstructionPartsKernels.nested
#check @MicroCFTA.WarmConstructionPartsKernels.node_union
#print MicroCFTA.WarmConstructionPartsKernels.node_union
#print axioms MicroCFTA.WarmConstructionPartsKernels.node_union
