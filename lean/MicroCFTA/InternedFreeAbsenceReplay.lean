import MicroCFTA.InternedFreeAbsenceContext
import MicroCFTA.InternedRequestFreeReadback
import MicroCFTA.InternedRequestAgreement
import MicroCFTA.InternedOrdinaryAbsenceReplay

/-!
# Full source replay after one interned free name disappears

Change one interned literal input to any reference. Two completed source
executions return the same complete record when the first result omits
that free name. Both histories must extend to one coherent cache.
The recursive case derives absence in both actual probes from the final
free-name table. It then reuses their exact source request.
-/
namespace MicroCFTA.InternedFreeAbsenceReplay
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedNestedMissReadback InternedStoredMuOrigins InternedNestedSpecialization
open InternedFreeAbsenceConstructors InternedFreeAbsenceContext InternedOccurrenceObservations
open InternedRequestAgreement
open InternedBinderProtocol (Reference)

mutual
/-- Completed unrestricted source calls agree exactly after the changed interned free name disappears. -/
theorem build_related [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (identity : Nat) (replacement : Reference) : RawReplay expression identity replacement := by
  intro names left right common afterLeft afterRight lc rc coherent first second firstDone secondDone lg rg
  refine ⟨InternedFreeAbsenceContext.build_empty expression identity replacement names left right afterLeft afterRight
    lc rc first second firstDone secondDone, ?_⟩
  intro absent
  cases expression with
  | empty =>
      simp only [build, Outcome.done.injEq] at firstDone secondDone
      exact firstDone.1.symm.trans secondDone.1
  | var index =>
      simp only [build, Outcome.done.injEq] at firstDone secondDone
      obtain ⟨rfl, rfl⟩ := firstDone
      obtain ⟨rfl, rfl⟩ := secondDone
      cases selected : names[index]? with
      | none => simp [List.getElem?_map, selected]
      | some name =>
          have different : name ≠ .interned identity := by
            intro same
            simp [List.getElem?_map, selected, same, Value.free] at absent
          simp [List.getElem?_map, selected, change, different]
  | node edges =>
      simp only [build] at firstDone secondDone
      obtain ⟨leftEdges, middleLeft, leftBuilt, leftMade⟩ := bind_done _ _ _ _ firstDone
      obtain ⟨rightEdges, middleRight, rightBuilt, rightMade⟩ := bind_done _ _ _ _ secondDone
      have leftContext : Context middleLeft names := by
        simpa only [leftBuilt, Outcome.state] using lc.edges edges
      have rightContext : Context middleRight (names.map (change identity replacement)) := by
        simpa only [rightBuilt, Outcome.state] using rc.edges edges
      have leftAvailable := (buildEdges_verified edges _ left lc.normal.facts lc.inputs).result leftEdges middleLeft leftBuilt
      have rightAvailable := (buildEdges_verified edges _ right rc.normal.facts rc.inputs).result rightEdges middleRight rightBuilt
      simp only [work, Outcome.done.injEq] at leftMade rightMade
      obtain ⟨rfl, rfl⟩ := leftMade
      obtain ⟨rfl, rfl⟩ := rightMade
      have related := buildEdges_related edges identity replacement names left right common middleLeft middleRight
        lc rc coherent leftEdges rightEdges leftBuilt rightBuilt
        (grows_trans (run_correct (makeNode leftEdges) middleLeft leftContext.normal.facts.coherent.valid).2 lg)
        (grows_trans (run_correct (makeNode rightEdges) middleRight rightContext.normal.facts.coherent.valid).2 rg)
      exact (makeNode_related (.interned identity) leftEdges rightEdges middleLeft middleRight common
        leftContext.normal rightContext.normal coherent leftAvailable rightAvailable related lg rg).2 absent
  | union members =>
      simp only [build] at firstDone secondDone
      obtain ⟨leftValues, middleLeft, leftBuilt, leftMade⟩ := bind_done _ _ _ _ firstDone
      obtain ⟨rightValues, middleRight, rightBuilt, rightMade⟩ := bind_done _ _ _ _ secondDone
      have leftContext : Context middleLeft names := by
        simpa only [leftBuilt, Outcome.state] using lc.many members
      have rightContext : Context middleRight (names.map (change identity replacement)) := by
        simpa only [rightBuilt, Outcome.state] using rc.many members
      have leftAvailable := (buildMany_verified members _ left lc.normal.facts lc.inputs).result leftValues middleLeft leftBuilt
      have rightAvailable := (buildMany_verified members _ right rc.normal.facts rc.inputs).result rightValues middleRight rightBuilt
      simp only [work, Outcome.done.injEq] at leftMade rightMade
      obtain ⟨rfl, rfl⟩ := leftMade
      obtain ⟨rfl, rfl⟩ := rightMade
      have related := buildMany_related members identity replacement names left right common middleLeft middleRight
        lc rc coherent leftValues rightValues leftBuilt rightBuilt
        (grows_trans (run_correct (makeUnion leftValues) middleLeft leftContext.normal.facts.coherent.valid).2 lg)
        (grows_trans (run_correct (makeUnion rightValues) middleRight rightContext.normal.facts.coherent.valid).2 rg)
      exact (makeUnion_related (.interned identity) leftValues rightValues middleLeft middleRight common
        leftContext.normal rightContext.normal leftAvailable rightAvailable related lg rg).2 absent
  | binder smart body =>
      have finalHeap : InternedFreeNameHeap.Heap afterLeft := by
        simpa only [firstDone, Outcome.state] using (lc.build (.binder smart body)).freeNames
      rw [build] at firstDone secondDone
      change ((callback body (names.map Value.reference) .depth left).bind fun depth middle =>
        (callback body (names.map Value.reference) (.uninterned depth.depth) middle).bind fun ordinary beforeRequest =>
          request smart depth ordinary (callback body (names.map Value.reference)) beforeRequest) = .done first afterLeft at firstDone
      change ((callback body ((names.map (change identity replacement)).map Value.reference) .depth right).bind fun depth middle =>
        (callback body ((names.map (change identity replacement)).map Value.reference) (.uninterned depth.depth) middle).bind fun ordinary beforeRequest =>
          request smart depth ordinary (callback body ((names.map (change identity replacement)).map Value.reference)) beforeRequest) = .done second afterRight at secondDone
      obtain ⟨leftDepth, afterLeftDepth, leftDepthDone, leftLater⟩ := bind_done _ _ _ _ firstDone
      obtain ⟨rightDepth, afterRightDepth, rightDepthDone, rightLater⟩ := bind_done _ _ _ _ secondDone
      obtain ⟨leftOrdinary, beforeLeftRequest, leftOrdinaryDone, leftRequestDone⟩ := bind_done _ _ _ _ leftLater
      obtain ⟨rightOrdinary, beforeRightRequest, rightOrdinaryDone, rightRequestDone⟩ := bind_done _ _ _ _ rightLater
      have leftDepthContext : Context afterLeftDepth names := by
        simpa only [leftDepthDone, Outcome.state] using lc.callback body .depth (depth_available left)
      have rightDepthContext : Context afterRightDepth (names.map (change identity replacement)) := by
        simpa only [rightDepthDone, Outcome.state] using rc.callback body .depth (depth_available right)
      have leftRequestContext : Context beforeLeftRequest names := by
        simpa only [leftOrdinaryDone, Outcome.state] using
          leftDepthContext.callback body (.uninterned leftDepth.depth) (ordinary_available afterLeftDepth leftDepth.depth)
      have rightRequestContext : Context beforeRightRequest (names.map (change identity replacement)) := by
        simpa only [rightOrdinaryDone, Outcome.state] using
          rightDepthContext.callback body (.uninterned rightDepth.depth) (ordinary_available afterRightDepth rightDepth.depth)
      have leftDepthVerified := callback_verified body _ .depth left lc.normal.facts (lc.local .depth (depth_available left)).inputs
      have leftOrdinaryVerified := callback_verified body _ (.uninterned leftDepth.depth) afterLeftDepth leftDepthContext.normal.facts
        (leftDepthContext.local (.uninterned leftDepth.depth) (ordinary_available afterLeftDepth leftDepth.depth)).inputs
      have leftDepthAvailable : Available beforeLeftRequest leftDepth := by
        simpa only [leftOrdinaryDone, Outcome.state] using
          leftOrdinaryVerified.available leftDepth (leftDepthVerified.result leftDepth afterLeftDepth leftDepthDone)
      have leftOrdinaryAvailable := leftOrdinaryVerified.result leftOrdinary beforeLeftRequest leftOrdinaryDone
      have probeAbsent := InternedRequestFreeReadback.interned_probe_absent smart body _ leftDepth leftOrdinary beforeLeftRequest
        leftRequestContext.normal.facts leftDepthAvailable leftOrdinaryAvailable first afterLeft leftRequestDone finalHeap identity absent
      have leftRequestGrowth : Grows beforeLeftRequest afterLeft := by
        simpa only [leftRequestDone, Outcome.state] using
          (request_correct smart leftDepth leftOrdinary _ (callback_growing body (names.map Value.reference))
            beforeLeftRequest leftRequestContext.normal.facts.coherent.valid).2
      have rightRequestGrowth : Grows beforeRightRequest afterRight := by
        simpa only [rightRequestDone, Outcome.state] using
          (request_correct smart rightDepth rightOrdinary _
            (callback_growing body ((names.map (change identity replacement)).map Value.reference))
            beforeRightRequest rightRequestContext.normal.facts.coherent.valid).2
      have leftOrdinaryGrowth : Grows afterLeftDepth beforeLeftRequest := by
        simpa only [leftOrdinaryDone, Outcome.state] using
          (callback_growing body (names.map Value.reference) (.uninterned leftDepth.depth)
            afterLeftDepth leftDepthContext.normal.facts.coherent.valid).2
      have rightOrdinaryGrowth : Grows afterRightDepth beforeRightRequest := by
        simpa only [rightOrdinaryDone, Outcome.state] using
          (callback_growing body ((names.map (change identity replacement)).map Value.reference) (.uninterned rightDepth.depth)
            afterRightDepth rightDepthContext.normal.facts.coherent.valid).2
      have depthSame := callback_equal body identity replacement (build_related body identity replacement) names .depth
        (by intro impossible; cases impossible) left right common afterLeftDepth afterRightDepth lc rc coherent
        (depth_available left) (depth_available right) leftDepth rightDepth leftDepthDone rightDepthDone
        (grows_trans leftOrdinaryGrowth (grows_trans leftRequestGrowth lg))
        (grows_trans rightOrdinaryGrowth (grows_trans rightRequestGrowth rg)) probeAbsent.1
      subst rightDepth
      have ordinarySame := callback_equal body identity replacement (build_related body identity replacement) names
        (.uninterned leftDepth.depth) (by intro impossible; cases impossible)
        afterLeftDepth afterRightDepth common beforeLeftRequest beforeRightRequest leftDepthContext rightDepthContext coherent
        (ordinary_available afterLeftDepth leftDepth.depth) (ordinary_available afterRightDepth leftDepth.depth)
        leftOrdinary rightOrdinary leftOrdinaryDone rightOrdinaryDone
        (grows_trans leftRequestGrowth lg) (grows_trans rightRequestGrowth rg) probeAbsent.2
      subst rightOrdinary
      exact source_request_same smart leftDepth leftOrdinary body body (names.map Value.reference)
        ((names.map (change identity replacement)).map Value.reference) beforeLeftRequest beforeRightRequest afterLeft afterRight common
        first second leftRequestContext.normal.facts.coherent.valid rightRequestContext.normal.facts.coherent.valid
        leftRequestDone rightRequestDone lg rg
termination_by sizeOf expression

/-- Ordered completed child calls retain the free-name absence observation at each source position. -/
theorem buildMany_related [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (identity : Nat) (replacement : Reference) (names : List Reference)
    (left right common afterLeft afterRight : State Symbol Guard)
    (lc : Context left names) (rc : Context right (names.map (change identity replacement))) (coherent : Coherent common)
    (first second : List (Value Symbol Guard))
    (firstDone : buildMany expressions (names.map Value.reference) left = .done first afterLeft)
    (secondDone : buildMany expressions ((names.map (change identity replacement)).map Value.reference) right = .done second afterRight)
    (lg : Grows afterLeft common) (rg : Grows afterRight common) :
    Paired (Related (.interned identity)) first second := by
  cases expressions with
  | nil =>
      simp only [buildMany, Outcome.done.injEq] at firstDone secondDone
      obtain ⟨rfl, rfl⟩ := firstDone
      obtain ⟨rfl, rfl⟩ := secondDone
      exact .nil
  | cons head tail =>
      simp only [buildMany] at firstDone secondDone
      obtain ⟨leftHead, middleLeft, headLeftDone, laterLeft⟩ := bind_done _ _ _ _ firstDone
      obtain ⟨rightHead, middleRight, headRightDone, laterRight⟩ := bind_done _ _ _ _ secondDone
      obtain ⟨leftTail, lastLeft, tailLeftDone, assembledLeft⟩ := bind_done _ _ _ _ laterLeft
      obtain ⟨rightTail, lastRight, tailRightDone, assembledRight⟩ := bind_done _ _ _ _ laterRight
      simp only [Outcome.done.injEq] at assembledLeft assembledRight
      obtain ⟨rfl, rfl⟩ := assembledLeft
      obtain ⟨rfl, rfl⟩ := assembledRight
      have leftContext : Context middleLeft names := by simpa only [headLeftDone, Outcome.state] using lc.build head
      have rightContext : Context middleRight (names.map (change identity replacement)) := by
        simpa only [headRightDone, Outcome.state] using rc.build head
      have leftTailGrowth : Grows middleLeft lastLeft := by
        simpa only [tailLeftDone, Outcome.state] using
          (buildMany_correct tail (names.map Value.reference) middleLeft leftContext.normal.facts.coherent.valid).2
      have rightTailGrowth : Grows middleRight lastRight := by
        simpa only [tailRightDone, Outcome.state] using
          (buildMany_correct tail ((names.map (change identity replacement)).map Value.reference) middleRight rightContext.normal.facts.coherent.valid).2
      exact .cons (build_related head identity replacement names left right common middleLeft middleRight lc rc coherent
        leftHead rightHead headLeftDone headRightDone (grows_trans leftTailGrowth lg) (grows_trans rightTailGrowth rg))
        (buildMany_related tail identity replacement names middleLeft middleRight common lastLeft lastRight
          leftContext rightContext coherent leftTail rightTail tailLeftDone tailRightDone lg rg)
termination_by sizeOf expressions

/-- Completed edge lists retain source metadata and paired child observations before dead-edge removal. -/
theorem buildEdges_related [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (identity : Nat) (replacement : Reference) (names : List Reference)
    (left right common afterLeft afterRight : State Symbol Guard)
    (lc : Context left names) (rc : Context right (names.map (change identity replacement))) (coherent : Coherent common)
    (first second : List (EdgeValue Symbol Guard))
    (firstDone : buildEdges expressions (names.map Value.reference) left = .done first afterLeft)
    (secondDone : buildEdges expressions ((names.map (change identity replacement)).map Value.reference) right = .done second afterRight)
    (lg : Grows afterLeft common) (rg : Grows afterRight common) :
    Paired (EdgeRelated (.interned identity)) first second := by
  cases expressions with
  | nil =>
      simp only [buildEdges, Outcome.done.injEq] at firstDone secondDone
      obtain ⟨rfl, rfl⟩ := firstDone
      obtain ⟨rfl, rfl⟩ := secondDone
      exact .nil
  | cons head tail =>
      cases head with
      | mk symbol guard children =>
          simp only [buildEdges] at firstDone secondDone
          obtain ⟨leftValues, middleLeft, childrenLeftDone, laterLeft⟩ := bind_done _ _ _ _ firstDone
          obtain ⟨rightValues, middleRight, childrenRightDone, laterRight⟩ := bind_done _ _ _ _ secondDone
          obtain ⟨leftEdge, afterLeftEdge, edgeLeftDone, remainingLeft⟩ := bind_done _ _ _ _ laterLeft
          obtain ⟨rightEdge, afterRightEdge, edgeRightDone, remainingRight⟩ := bind_done _ _ _ _ laterRight
          obtain ⟨leftTail, lastLeft, tailLeftDone, assembledLeft⟩ := bind_done _ _ _ _ remainingLeft
          obtain ⟨rightTail, lastRight, tailRightDone, assembledRight⟩ := bind_done _ _ _ _ remainingRight
          simp only [Outcome.done.injEq] at assembledLeft assembledRight
          obtain ⟨rfl, rfl⟩ := assembledLeft
          obtain ⟨rfl, rfl⟩ := assembledRight
          have leftContext : Context middleLeft names := by simpa only [childrenLeftDone, Outcome.state] using lc.many children
          have rightContext : Context middleRight (names.map (change identity replacement)) := by
            simpa only [childrenRightDone, Outcome.state] using rc.many children
          have leftAvailable := (buildMany_verified children _ left lc.normal.facts lc.inputs).result leftValues middleLeft childrenLeftDone
          have rightAvailable := (buildMany_verified children _ right rc.normal.facts rc.inputs).result rightValues middleRight childrenRightDone
          have leftEdgeContext : Context afterLeftEdge names := by
            have current := leftContext.edge symbol guard leftValues leftAvailable
            change Context (work (makeEdge symbol guard leftValues) middleLeft).state names at current
            simpa only [edgeLeftDone, Outcome.state] using current
          have rightEdgeContext : Context afterRightEdge (names.map (change identity replacement)) := by
            have current := rightContext.edge symbol guard rightValues rightAvailable
            change Context (work (makeEdge symbol guard rightValues) middleRight).state _ at current
            simpa only [edgeRightDone, Outcome.state] using current
          have leftTailGrowth : Grows afterLeftEdge lastLeft := by
            simpa only [tailLeftDone, Outcome.state] using
              (buildEdges_correct tail (names.map Value.reference) afterLeftEdge leftEdgeContext.normal.facts.coherent.valid).2
          have rightTailGrowth : Grows afterRightEdge lastRight := by
            simpa only [tailRightDone, Outcome.state] using
              (buildEdges_correct tail ((names.map (change identity replacement)).map Value.reference) afterRightEdge rightEdgeContext.normal.facts.coherent.valid).2
          have leftEdgeGrowth : Grows middleLeft afterLeftEdge := by
            simpa only [edgeLeftDone, Outcome.state] using (work_correct (makeEdge symbol guard leftValues) middleLeft leftContext.normal.facts.coherent.valid).2
          have rightEdgeGrowth : Grows middleRight afterRightEdge := by
            simpa only [edgeRightDone, Outcome.state] using (work_correct (makeEdge symbol guard rightValues) middleRight rightContext.normal.facts.coherent.valid).2
          refine .cons ?_ (buildEdges_related tail identity replacement names afterLeftEdge afterRightEdge common lastLeft lastRight
            leftEdgeContext rightEdgeContext coherent leftTail rightTail tailLeftDone tailRightDone lg rg)
          simp only [work, Outcome.done.injEq] at edgeLeftDone edgeRightDone
          rw [← edgeLeftDone.1, ← edgeRightDone.1]
          refine ⟨?_, ?_, ?_⟩
          · simp only [InternedOrdinaryAbsenceReplay.makeEdge_key _ _ _ _ leftContext.normal.facts.coherent,
              InternedOrdinaryAbsenceReplay.makeEdge_key _ _ _ _ rightContext.normal.facts.coherent]
          · simp only [InternedOrdinaryAbsenceReplay.makeEdge_key _ _ _ _ leftContext.normal.facts.coherent,
              InternedOrdinaryAbsenceReplay.makeEdge_key _ _ _ _ rightContext.normal.facts.coherent]
          · rw [InternedShallowValues.makeEdge_children symbol guard leftValues middleLeft
                leftContext.normal.facts.coherent leftContext.normal.facts.cached leftAvailable,
              InternedShallowValues.makeEdge_children symbol guard rightValues middleRight
                rightContext.normal.facts.coherent rightContext.normal.facts.cached rightAvailable]
            exact buildMany_related children identity replacement names left right common middleLeft middleRight lc rc coherent
              leftValues rightValues childrenLeftDone childrenRightDone
              (grows_trans leftEdgeGrowth (grows_trans leftTailGrowth lg))
              (grows_trans rightEdgeGrowth (grows_trans rightTailGrowth rg))
termination_by sizeOf expressions
end

end MicroCFTA.InternedFreeAbsenceReplay
