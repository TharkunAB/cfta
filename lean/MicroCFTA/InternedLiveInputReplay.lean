import MicroCFTA.InternedLiveInputContext
import MicroCFTA.InternedLexicalLiveness

/-!
# Complete source congruence for live lexical inputs

Two completed executions give the same record if each retained abstract
input has the same reference on both sides. Abstract atoms distinguish
lexical positions before actual references can alias. Dead source edges
need no input agreement. Both histories extend to one coherent cache.
-/
set_option maxHeartbeats 800000

namespace MicroCFTA.InternedLiveInputReplay
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedNestedMissReadback InternedStoredMuOrigins InternedNestedSpecialization
open InternedFreeAbsenceContext InternedLiveInputContext InternedFreeNameSemantics
open InternedRequestAgreement
open InternedBinderProtocol (Reference)

mutual
/-- Completed full source calls depend only on their live lexical inputs. -/
theorem build_same [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) : Replay expression := by
  intro Atom atoms firstMap secondMap agree left right common afterLeft afterRight lc rc coherent first second firstDone secondDone lg rg
  cases expression with
  | empty =>
      simp only [build, Outcome.done.injEq] at firstDone secondDone
      exact firstDone.1.symm.trans secondDone.1
  | var index =>
      simp only [build, Outcome.done.injEq] at firstDone secondDone
      obtain ⟨rfl, rfl⟩ := firstDone
      obtain ⟨rfl, rfl⟩ := secondDone
      cases selected : atoms[index]? with
      | none => simp [List.getElem?_map, selected]
      | some atom =>
          have same := agree atom (by simp [liveInputs, evaluate, List.getElem?_map, selected])
          simp [List.getElem?_map, selected, same]
  | node edges =>
      simp only [build] at firstDone secondDone
      obtain ⟨leftEdges, middleLeft, leftBuilt, leftMade⟩ := bind_done _ _ _ _ firstDone
      obtain ⟨rightEdges, middleRight, rightBuilt, rightMade⟩ := bind_done _ _ _ _ secondDone
      have leftContext : Context middleLeft (atoms.map firstMap) := by
        simpa only [leftBuilt, Outcome.state] using lc.edges edges
      have rightContext : Context middleRight (atoms.map secondMap) := by
        simpa only [rightBuilt, Outcome.state] using rc.edges edges
      simp only [work, Outcome.done.injEq] at leftMade rightMade
      obtain ⟨rfl, rfl⟩ := leftMade
      obtain ⟨rfl, rfl⟩ := rightMade
      have related := buildEdges_same edges atoms firstMap secondMap (by simpa only [liveInputs, evaluate] using agree) left right common middleLeft middleRight
        lc rc coherent leftEdges rightEdges leftBuilt rightBuilt
        (grows_trans (run_correct (makeNode leftEdges) middleLeft leftContext.normal.facts.coherent.valid).2 lg)
        (grows_trans (run_correct (makeNode rightEdges) middleRight rightContext.normal.facts.coherent.valid).2 rg)
      have same : makeNode leftEdges = makeNode rightEdges := by unfold makeNode; rw [related]
      rw [← same] at rg ⊢
      exact InternedObservedAbsence.run_shared _ middleLeft middleRight common
        leftContext.normal.facts.coherent.valid rightContext.normal.facts.coherent.valid lg rg
  | union members =>
      simp only [build] at firstDone secondDone
      obtain ⟨leftValues, middleLeft, leftBuilt, leftMade⟩ := bind_done _ _ _ _ firstDone
      obtain ⟨rightValues, middleRight, rightBuilt, rightMade⟩ := bind_done _ _ _ _ secondDone
      have leftContext : Context middleLeft (atoms.map firstMap) := by
        simpa only [leftBuilt, Outcome.state] using lc.many members
      have rightContext : Context middleRight (atoms.map secondMap) := by
        simpa only [rightBuilt, Outcome.state] using rc.many members
      simp only [work, Outcome.done.injEq] at leftMade rightMade
      obtain ⟨rfl, rfl⟩ := leftMade
      obtain ⟨rfl, rfl⟩ := rightMade
      have related := buildMany_same members atoms firstMap secondMap (by simpa only [liveInputs, evaluate] using agree) left right common middleLeft middleRight
        lc rc coherent leftValues rightValues leftBuilt rightBuilt
        (grows_trans (run_correct (makeUnion leftValues) middleLeft leftContext.normal.facts.coherent.valid).2 lg)
        (grows_trans (run_correct (makeUnion rightValues) middleRight rightContext.normal.facts.coherent.valid).2 rg)
      rw [← related] at rg ⊢
      exact InternedObservedAbsence.run_shared _ middleLeft middleRight common
        leftContext.normal.facts.coherent.valid rightContext.normal.facts.coherent.valid lg rg
  | binder smart body =>
      rw [build] at firstDone secondDone
      change ((callback body ((atoms.map firstMap).map Value.reference) .depth left).bind fun depth middle =>
        (callback body ((atoms.map firstMap).map Value.reference) (.uninterned depth.depth) middle).bind fun ordinary beforeRequest =>
          request smart depth ordinary (callback body ((atoms.map firstMap).map Value.reference)) beforeRequest) = .done first afterLeft at firstDone
      change ((callback body ((atoms.map secondMap).map Value.reference) .depth right).bind fun depth middle =>
        (callback body ((atoms.map secondMap).map Value.reference) (.uninterned depth.depth) middle).bind fun ordinary beforeRequest =>
          request smart depth ordinary (callback body ((atoms.map secondMap).map Value.reference)) beforeRequest) = .done second afterRight at secondDone
      obtain ⟨leftDepth, afterLeftDepth, leftDepthDone, leftLater⟩ := bind_done _ _ _ _ firstDone
      obtain ⟨rightDepth, afterRightDepth, rightDepthDone, rightLater⟩ := bind_done _ _ _ _ secondDone
      obtain ⟨leftOrdinary, beforeLeftRequest, leftOrdinaryDone, leftRequestDone⟩ := bind_done _ _ _ _ leftLater
      obtain ⟨rightOrdinary, beforeRightRequest, rightOrdinaryDone, rightRequestDone⟩ := bind_done _ _ _ _ rightLater
      have leftDepthContext : Context afterLeftDepth (atoms.map firstMap) := by
        simpa only [leftDepthDone, Outcome.state] using lc.callback body .depth (depth_available left)
      have rightDepthContext : Context afterRightDepth (atoms.map secondMap) := by
        simpa only [rightDepthDone, Outcome.state] using rc.callback body .depth (depth_available right)
      have leftRequestContext : Context beforeLeftRequest (atoms.map firstMap) := by
        simpa only [leftOrdinaryDone, Outcome.state] using
          leftDepthContext.callback body (.uninterned leftDepth.depth) (ordinary_available afterLeftDepth leftDepth.depth)
      have rightRequestContext : Context beforeRightRequest (atoms.map secondMap) := by
        simpa only [rightOrdinaryDone, Outcome.state] using
          rightDepthContext.callback body (.uninterned rightDepth.depth) (ordinary_available afterRightDepth rightDepth.depth)
      have leftRequestGrowth : Grows beforeLeftRequest afterLeft := by
        simpa only [leftRequestDone, Outcome.state] using
          (request_correct smart leftDepth leftOrdinary _ (callback_growing body ((atoms.map firstMap).map Value.reference))
            beforeLeftRequest leftRequestContext.normal.facts.coherent.valid).2
      have rightRequestGrowth : Grows beforeRightRequest afterRight := by
        simpa only [rightRequestDone, Outcome.state] using
          (request_correct smart rightDepth rightOrdinary _
            (callback_growing body ((atoms.map secondMap).map Value.reference))
            beforeRightRequest rightRequestContext.normal.facts.coherent.valid).2
      have leftOrdinaryGrowth : Grows afterLeftDepth beforeLeftRequest := by
        simpa only [leftOrdinaryDone, Outcome.state] using
          (callback_growing body ((atoms.map firstMap).map Value.reference) (.uninterned leftDepth.depth)
            afterLeftDepth leftDepthContext.normal.facts.coherent.valid).2
      have rightOrdinaryGrowth : Grows afterRightDepth beforeRightRequest := by
        simpa only [rightOrdinaryDone, Outcome.state] using
          (callback_growing body ((atoms.map secondMap).map Value.reference) (.uninterned rightDepth.depth)
            afterRightDepth rightDepthContext.normal.facts.coherent.valid).2
      have depthSame := callback_same body (build_same body) smart atoms firstMap secondMap .depth
        agree left right common afterLeftDepth afterRightDepth lc rc coherent
        (depth_available left) (depth_available right) leftDepth rightDepth leftDepthDone rightDepthDone
        (grows_trans leftOrdinaryGrowth (grows_trans leftRequestGrowth lg))
        (grows_trans rightOrdinaryGrowth (grows_trans rightRequestGrowth rg))
      subst rightDepth
      have ordinarySame := callback_same body (build_same body) smart atoms firstMap secondMap
        (.uninterned leftDepth.depth) agree
        afterLeftDepth afterRightDepth common beforeLeftRequest beforeRightRequest leftDepthContext rightDepthContext coherent
        (ordinary_available afterLeftDepth leftDepth.depth) (ordinary_available afterRightDepth leftDepth.depth)
        leftOrdinary rightOrdinary leftOrdinaryDone rightOrdinaryDone
        (grows_trans leftRequestGrowth lg) (grows_trans rightRequestGrowth rg)
      subst rightOrdinary
      exact source_request_same smart leftDepth leftOrdinary body body ((atoms.map firstMap).map Value.reference)
        ((atoms.map secondMap).map Value.reference) beforeLeftRequest beforeRightRequest afterLeft afterRight common
        first second leftRequestContext.normal.facts.coherent.valid rightRequestContext.normal.facts.coherent.valid
        leftRequestDone rightRequestDone lg rg
termination_by sizeOf expression

/-- Ordered completed child calls agree when all retained lexical inputs agree. -/
theorem buildMany_same [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (atoms : List Atom) (firstMap secondMap : Atom → Reference)
    (agree : ∀ atom ∈ (evaluateMany expressions (atoms.map (fun a => some [a])) (atoms.map (fun a => [a]))).flatten,
      firstMap atom = secondMap atom)
    (left right common afterLeft afterRight : State Symbol Guard)
    (lc : Context left (atoms.map firstMap)) (rc : Context right (atoms.map secondMap)) (coherent : Coherent common)
    (first second : List (Value Symbol Guard))
    (firstDone : buildMany expressions ((atoms.map firstMap).map Value.reference) left = .done first afterLeft)
    (secondDone : buildMany expressions ((atoms.map secondMap).map Value.reference) right = .done second afterRight)
    (lg : Grows afterLeft common) (rg : Grows afterRight common) :
    first = second := by
  cases expressions with
  | nil =>
      simp only [buildMany, Outcome.done.injEq] at firstDone secondDone
      obtain ⟨rfl, rfl⟩ := firstDone
      obtain ⟨rfl, rfl⟩ := secondDone
      rfl
  | cons head tail =>
      simp only [buildMany] at firstDone secondDone
      obtain ⟨leftHead, middleLeft, headLeftDone, laterLeft⟩ := bind_done _ _ _ _ firstDone
      obtain ⟨rightHead, middleRight, headRightDone, laterRight⟩ := bind_done _ _ _ _ secondDone
      obtain ⟨leftTail, lastLeft, tailLeftDone, assembledLeft⟩ := bind_done _ _ _ _ laterLeft
      obtain ⟨rightTail, lastRight, tailRightDone, assembledRight⟩ := bind_done _ _ _ _ laterRight
      simp only [Outcome.done.injEq] at assembledLeft assembledRight
      obtain ⟨rfl, rfl⟩ := assembledLeft
      obtain ⟨rfl, rfl⟩ := assembledRight
      have leftContext : Context middleLeft (atoms.map firstMap) := by simpa only [headLeftDone, Outcome.state] using lc.build head
      have rightContext : Context middleRight (atoms.map secondMap) := by
        simpa only [headRightDone, Outcome.state] using rc.build head
      have leftTailGrowth : Grows middleLeft lastLeft := by
        simpa only [tailLeftDone, Outcome.state] using
          (buildMany_correct tail ((atoms.map firstMap).map Value.reference) middleLeft leftContext.normal.facts.coherent.valid).2
      have rightTailGrowth : Grows middleRight lastRight := by
        simpa only [tailRightDone, Outcome.state] using
          (buildMany_correct tail ((atoms.map secondMap).map Value.reference) middleRight rightContext.normal.facts.coherent.valid).2
      have headSame := build_same head atoms firstMap secondMap
        (fun atom member => agree atom (by simp only [evaluateMany, List.flatten_cons, List.mem_append]; exact Or.inl member))
        left right common middleLeft middleRight lc rc coherent
        leftHead rightHead headLeftDone headRightDone (grows_trans leftTailGrowth lg) (grows_trans rightTailGrowth rg)
      have tailSame := buildMany_same tail atoms firstMap secondMap
        (fun atom member => agree atom (by simp only [evaluateMany, List.flatten_cons, List.mem_append]; exact Or.inr member))
        middleLeft middleRight common lastLeft lastRight
        leftContext rightContext coherent leftTail rightTail tailLeftDone tailRightDone lg rg
      rw [headSame, tailSame]
termination_by sizeOf expressions

/-- Completed source edge lists have equal surviving records when live inputs agree. -/
theorem buildEdges_same [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (atoms : List Atom) (firstMap secondMap : Atom → Reference)
    (agree : ∀ atom ∈ evaluateEdges expressions (atoms.map (fun a => some [a])) (atoms.map (fun a => [a])),
      firstMap atom = secondMap atom)
    (left right common afterLeft afterRight : State Symbol Guard)
    (lc : Context left (atoms.map firstMap)) (rc : Context right (atoms.map secondMap)) (coherent : Coherent common)
    (first second : List (EdgeValue Symbol Guard))
    (firstDone : buildEdges expressions ((atoms.map firstMap).map Value.reference) left = .done first afterLeft)
    (secondDone : buildEdges expressions ((atoms.map secondMap).map Value.reference) right = .done second afterRight)
    (lg : Grows afterLeft common) (rg : Grows afterRight common) :
    surviving first = surviving second := by
  cases expressions with
  | nil =>
      simp only [buildEdges, Outcome.done.injEq] at firstDone secondDone
      obtain ⟨rfl, rfl⟩ := firstDone
      obtain ⟨rfl, rfl⟩ := secondDone
      rfl
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
          have leftContext : Context middleLeft (atoms.map firstMap) := by simpa only [childrenLeftDone, Outcome.state] using lc.many children
          have rightContext : Context middleRight (atoms.map secondMap) := by
            simpa only [childrenRightDone, Outcome.state] using rc.many children
          have leftAvailable := (buildMany_verified children _ left lc.normal.facts lc.inputs).result leftValues middleLeft childrenLeftDone
          have rightAvailable := (buildMany_verified children _ right rc.normal.facts rc.inputs).result rightValues middleRight childrenRightDone
          have leftEdgeContext : Context afterLeftEdge (atoms.map firstMap) := by
            have current := leftContext.edge symbol guard leftValues leftAvailable
            change Context (work (makeEdge symbol guard leftValues) middleLeft).state (atoms.map firstMap) at current
            simpa only [edgeLeftDone, Outcome.state] using current
          have rightEdgeContext : Context afterRightEdge (atoms.map secondMap) := by
            have current := rightContext.edge symbol guard rightValues rightAvailable
            change Context (work (makeEdge symbol guard rightValues) middleRight).state _ at current
            simpa only [edgeRightDone, Outcome.state] using current
          have leftTailGrowth : Grows afterLeftEdge lastLeft := by
            simpa only [tailLeftDone, Outcome.state] using
              (buildEdges_correct tail ((atoms.map firstMap).map Value.reference) afterLeftEdge leftEdgeContext.normal.facts.coherent.valid).2
          have rightTailGrowth : Grows afterRightEdge lastRight := by
            simpa only [tailRightDone, Outcome.state] using
              (buildEdges_correct tail ((atoms.map secondMap).map Value.reference) afterRightEdge rightEdgeContext.normal.facts.coherent.valid).2
          have leftEdgeGrowth : Grows middleLeft afterLeftEdge := by
            simpa only [edgeLeftDone, Outcome.state] using (work_correct (makeEdge symbol guard leftValues) middleLeft leftContext.normal.facts.coherent.valid).2
          have rightEdgeGrowth : Grows middleRight afterRightEdge := by
            simpa only [edgeRightDone, Outcome.state] using (work_correct (makeEdge symbol guard rightValues) middleRight rightContext.normal.facts.coherent.valid).2
          have tailSame := buildEdges_same tail atoms firstMap secondMap
            (fun atom member => agree atom (by simp only [evaluateEdges, List.mem_append]; exact Or.inr member))
            afterLeftEdge afterRightEdge common lastLeft lastRight
            leftEdgeContext rightEdgeContext coherent leftTail rightTail tailLeftDone tailRightDone lg rg
          have leftLive := InternedLexicalLiveness.buildMany_empty children atoms firstMap left middleLeft lc leftValues childrenLeftDone
          have rightLive := InternedLexicalLiveness.buildMany_empty children atoms secondMap right middleRight rc rightValues childrenRightDone
          have leftChildren : leftEdge.children = leftValues := by
            simp only [work, Outcome.done.injEq] at edgeLeftDone
            rw [← edgeLeftDone.1]
            exact InternedShallowValues.makeEdge_children symbol guard leftValues middleLeft
              leftContext.normal.facts.coherent leftContext.normal.facts.cached leftAvailable
          have rightChildren : rightEdge.children = rightValues := by
            simp only [work, Outcome.done.injEq] at edgeRightDone
            rw [← edgeRightDone.1]
            exact InternedShallowValues.makeEdge_children symbol guard rightValues middleRight
              rightContext.normal.facts.coherent rightContext.normal.facts.cached rightAvailable
          cases live : (InternedProfileSemantics.evaluateMany children (atoms.map (fun a => some [a]))).all
              (fun child => !InternedProfileSemantics.isEmpty child) with
          | false =>
              simpa only [surviving, List.filter_cons, leftChildren, rightChildren, leftLive, rightLive,
                live, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] using tailSame
          | true =>
              have childrenSame := buildMany_same children atoms firstMap secondMap
                (fun atom member => agree atom (by simp only [evaluateEdges, live, ↓reduceIte, List.mem_append]; exact Or.inl member))
                left right common middleLeft middleRight lc rc coherent
                leftValues rightValues childrenLeftDone childrenRightDone
                (grows_trans leftEdgeGrowth (grows_trans leftTailGrowth lg))
                (grows_trans rightEdgeGrowth (grows_trans rightTailGrowth rg))
              have edgeSame : leftEdge = rightEdge := by
                have leftDone := edgeLeftDone
                have rightDone := edgeRightDone
                simp only [work, Outcome.done.injEq] at leftDone rightDone
                rw [← leftDone.1, ← rightDone.1, ← childrenSame]
                apply InternedObservedAbsence.run_shared _ middleLeft middleRight common
                  leftContext.normal.facts.coherent.valid rightContext.normal.facts.coherent.valid
                · simpa only [leftDone.2] using grows_trans leftTailGrowth lg
                · simpa only [childrenSame, rightDone.2] using grows_trans rightTailGrowth rg
              simp only [surviving, List.filter_cons, leftChildren, rightChildren, leftLive, rightLive,
                live, Bool.not_true, Bool.not_false, ↓reduceIte]
              change leftEdge :: surviving leftTail = rightEdge :: surviving rightTail
              rw [edgeSame, tailSame]
termination_by sizeOf expressions
end

end MicroCFTA.InternedLiveInputReplay
