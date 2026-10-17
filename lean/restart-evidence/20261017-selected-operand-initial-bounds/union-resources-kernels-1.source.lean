import MicroCFTA.SourceCurrentProjectionUnionResources
import MicroCFTA.InternedFreshOrdinaryCosts
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000

namespace MicroCFTA.ProjectionUnionResourcesIntegration
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceCurrentProjectionUnionResources
open SourceCurrentMemoMergeResourceControl (Fits)
open SourceCurrentProjectionNumericReplay
open MergedFreshOrdinaryExposure (nodeEdges)

private def expression : InternedNestedConstruction.Syntax Nat Bool :=
  .union [.binder false (.node [.mk 0 true [], .mk 1 false [.var 0]]), .node [.mk 3 false []]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def input : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def source := built.state
private def exposed := nodeEdges 8 input source
private def rows : List (EdgeValue Nat Bool) := match exposed with | .done rows _ => rows | _ => []
private def middle := exposed.state
private def rebuilt := run (makeNode rows) middle
private def bound := SourceCurrentMemoMergeResourceControl.initialBound source.nodes.next source.edges.next
  (InternedValueMassHeap.initialBound source)

private theorem constructed : built = .done input source := by cbv
private theorem literal : exposed = .done rows middle := by cbv
private theorem actualRead : SourceEqualityProjectionRead.Read input source rows middle := .done 8 literal
private theorem semantic : SourceEqualityRequiredSemanticCache.SemanticReady source :=
  SourceEqualityRequiredSemanticCache.constructed expression input source constructed
private theorem costs : InternedFreshOrdinaryCostHeap.Heap source := InternedFreshOrdinaryCosts.closed_heap expression
private theorem available : Available source input :=
  (InternedFreshOrdinaryFacts.closed_verified expression).result input source constructed
private theorem closed : input.free = [] := by cbv
private theorem initial : Fits bound source := SourceCurrentMemoMergeResourceControl.initial source
  (InternedValueMassHeap.initialBound source) (InternedValueMassHeap.initial source semantic.ready.semantic.1.normal.facts)
private theorem resourceRead := SourceCurrentProjectionUnionResources.read actualRead bound semantic costs available closed initial

/-- A real union over a productive Mu obtains computed row width and exact full-state warm replay. -/
theorem allocating_read :
    built = .done input source ∧
      (match input with | .union _ members _ _ => ∃ member ∈ members, match member with | .mu .. => True | _ => False | _ => False) ∧
      source.nodes.next < middle.nodes.next ∧ source.edges.next < middle.edges.next ∧
      Fits (readGrowth bound) middle ∧ rows.length ≤ readWidth bound ∧
      nodeEdges (readFuel bound) input source = .done rows middle ∧
      nodeEdges (readFuel bound) input middle = .done rows middle := by
  have warm := MergedFreshOrdinaryColdReplay.nodeEdges_replay (readFuel bound) input source middle
    semantic.ready.semantic.1.normal.facts.coherent.valid rows middle resourceRead.2.2.2.2.2.1 (grows_refl _)
  exact ⟨constructed, by cbv; exact ⟨_, List.mem_cons_self, True.intro⟩,
    by cbv, by cbv, resourceRead.2.1, resourceRead.2.2.1, resourceRead.2.2.2.2.2.1, warm⟩

private theorem actualHead : SourceEqualityRequiredHead.Head input source rebuilt.1 rebuilt.2 :=
  .read 8 rows middle literal rfl
private theorem resourceHead := SourceCurrentProjectionUnionResources.head actualHead bound semantic costs available closed initial

/-- The actual normalized head pays its node and repeats warm at the complete returned heap. -/
theorem constructed_head_warm :
    SourceEqualityRequiredHead.Head input source rebuilt.1 rebuilt.2 ∧
      Fits (headGrowth bound) rebuilt.2 ∧
      SourceEqualityRequiredWorker.head (readFuel (headGrowth bound)) input source = .done rebuilt.1 rebuilt.2 ∧
      ∃ warm : SourceEqualityRequiredHead.Head input rebuilt.2 rebuilt.1 rebuilt.2,
        Fits (headGrowth (headGrowth bound)) rebuilt.2 ∧
        HeadReady (readFuel (headGrowth (headGrowth bound))) warm := by
  have warmRead : nodeEdges 8 input rebuilt.2 = .done rows rebuilt.2 :=
    MergedFreshOrdinaryColdReplay.nodeEdges_replay 8 input source rebuilt.2
      semantic.ready.semantic.1.normal.facts.coherent.valid rows middle literal
      ((SourceEqualityRequiredCache.node rows middle resourceRead.1.semantic.ready
        resourceRead.2.2.2.1 resourceRead.2.2.2.2.1).1.growth)
  have warmBuilt : run (makeNode rows) rebuilt.2 = (rebuilt.1, rebuilt.2) := by cbv
  have warm : SourceEqualityRequiredHead.Head input rebuilt.2 rebuilt.1 rebuilt.2 := .read 8 rows rebuilt.2 warmRead warmBuilt
  have warmed := SourceCurrentProjectionUnionResources.head warm (headGrowth bound)
    resourceHead.1.semantic resourceHead.1.costs (resourceHead.1.keeps.available input available) closed resourceHead.2.1
  exact ⟨actualHead, resourceHead.2.1, head_replay resourceHead.2.2.2.2 _ (Nat.le_refl _),
    warm, warmed.2.1, warmed.2.2.2.2⟩

/-- A counted duplicate scan retains one shared computed fuel before actual union node work. -/
theorem counted_union :
    ∃ reads : SourceEqualityProjectionUnion.ReadAll [input, input] source (rows ++ rows) middle,
      Fits (readAllGrowth 3 bound) middle ∧
      (rows ++ rows).length ≤ 3 * readAllGrowth 3 bound ∧
      ReadAllReady (readFuel (readAllGrowth 3 bound)) reads ∧
      ∃ actual : SourceEqualityProjectionUnion.Union [input, input] source
          (run (makeNode (rows ++ rows)) middle).1 (run (makeNode (rows ++ rows)) middle).2,
        Fits (unionGrowth 3 bound) (run (makeNode (rows ++ rows)) middle).2 ∧
        SourceEqualityProjectionWorker.union (readFuel (unionGrowth 3 bound)) [input, input] source =
          .done (run (makeNode (rows ++ rows)) middle).1 (run (makeNode (rows ++ rows)) middle).2 := by
  have warmRead : SourceEqualityProjectionRead.Read input middle rows middle := .done 8
    (MergedFreshOrdinaryColdReplay.nodeEdges_replay 8 input source middle
      semantic.ready.semantic.1.normal.facts.coherent.valid rows middle literal (grows_refl _))
  have reads : SourceEqualityProjectionUnion.ReadAll [input, input] source (rows ++ rows) middle := by
    simpa only [List.append_nil] using SourceEqualityProjectionUnion.ReadAll.cons actualRead (.cons warmRead .nil)
  have inputs : Values source [input, input] := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact available
    · exact List.mem_singleton.mp member ▸ available
  have closures : MergedColdReaderClosedInputs.ClosedValues [input, input] := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact closed
    · exact List.mem_singleton.mp member ▸ closed
  have first := SourceCurrentProjectionUnionResources.readAll reads 3 bound semantic costs inputs closures initial (by simp)
  have actual : SourceEqualityProjectionUnion.Union [input, input] source
      (run (makeNode (rows ++ rows)) middle).1 (run (makeNode (rows ++ rows)) middle).2 := .node reads rfl
  have last := SourceCurrentProjectionUnionResources.union actual 3 bound semantic costs inputs closures initial (by simp)
  exact ⟨reads, first.2.1, first.2.2.1, first.2.2.2.2.2, actual, last.2.1,
    union_replay last.2.2.2.2 _ (Nat.le_refl _)⟩

end MicroCFTA.ProjectionUnionResourcesIntegration

#print axioms MicroCFTA.ProjectionUnionResourcesIntegration.allocating_read
#check @MicroCFTA.ProjectionUnionResourcesIntegration.allocating_read
#print axioms MicroCFTA.ProjectionUnionResourcesIntegration.constructed_head_warm
#check @MicroCFTA.ProjectionUnionResourcesIntegration.constructed_head_warm
#print axioms MicroCFTA.ProjectionUnionResourcesIntegration.counted_union
#check @MicroCFTA.ProjectionUnionResourcesIntegration.counted_union
