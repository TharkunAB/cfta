import MicroCFTA.InternedFreshOrdinaryLiveInputContext
import MicroCFTA.InternedFreshOrdinaryLexicalLiveness
import MicroCFTA.InternedFreshOrdinaryGrowth
import MicroCFTA.InternedRequestAgreement

/-!
# Exact repaired source comparison with arbitrary fixed captures

Two completed source runs agree when their surviving varying references
agree. Fixed captured values can be arbitrary available records. The proof
uses actual repaired ordinary choices and one coherent common cache.
Discarded edges require no agreement on their varying inputs.
-/
set_option maxHeartbeats 800000

namespace MicroCFTA.InternedFreshOrdinaryLiveInputReplay
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request work_correct request_correct)
open InternedNestedProvenance (depth_available ordinary_available)
open InternedNestedSpecialization
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts InternedFreshOrdinaryGrowth
open InternedFreshOrdinaryContext InternedFreshOrdinaryLiveInputs InternedFreshOrdinaryLiveInputContext
open InternedFreeNameSemantics
open InternedBinderProtocol (Reference)

mutual
/-- Completed full source calls depend only on their live lexical inputs. -/
theorem build_same [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) : Replay expression := by
  intro Atom inputs firstNames secondNames agree left right common afterLeft afterRight lc rc coherent first second firstDone secondDone lg rg
  cases expression with
  | empty =>
      simp only [build, Outcome.done.injEq] at firstDone secondDone
      exact firstDone.1.symm.trans secondDone.1
  | var index =>
      simp only [build, Outcome.done.injEq] at firstDone secondDone
      obtain ⟨rfl, rfl⟩ := firstDone
      obtain ⟨rfl, rfl⟩ := secondDone
      cases found : inputs[index]? with
      | none => simp [List.getElem?_map, found]
      | some selected =>
          cases selected with
          | inl value => simp [List.getElem?_map, found, input]
          | inr atom =>
              have same : firstNames atom = secondNames atom :=
                agree (.inr atom) (by simp [liveInputs, evaluate, List.getElem?_map, found, inputNames])
              simp [List.getElem?_map, found, input, same]
  | node edges =>
      simp only [build] at firstDone secondDone
      obtain ⟨leftEdges, middleLeft, leftBuilt, leftMade⟩ := bind_done _ _ _ _ firstDone
      obtain ⟨rightEdges, middleRight, rightBuilt, rightMade⟩ := bind_done _ _ _ _ secondDone
      have leftContext : Context middleLeft (inputs.map (input firstNames)) := by
        simpa only [leftBuilt, Outcome.state] using lc.edges edges
      have rightContext : Context middleRight (inputs.map (input secondNames)) := by
        simpa only [rightBuilt, Outcome.state] using rc.edges edges
      simp only [work, Outcome.done.injEq] at leftMade rightMade
      obtain ⟨rfl, rfl⟩ := leftMade
      obtain ⟨rfl, rfl⟩ := rightMade
      have related := buildEdges_same edges inputs firstNames secondNames (by simpa only [liveInputs, evaluate] using agree) left right common middleLeft middleRight
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
      have leftContext : Context middleLeft (inputs.map (input firstNames)) := by
        simpa only [leftBuilt, Outcome.state] using lc.many members
      have rightContext : Context middleRight (inputs.map (input secondNames)) := by
        simpa only [rightBuilt, Outcome.state] using rc.many members
      simp only [work, Outcome.done.injEq] at leftMade rightMade
      obtain ⟨rfl, rfl⟩ := leftMade
      obtain ⟨rfl, rfl⟩ := rightMade
      have related := buildMany_same members inputs firstNames secondNames (by simpa only [liveInputs, evaluate] using agree) left right common middleLeft middleRight
        lc rc coherent leftValues rightValues leftBuilt rightBuilt
        (grows_trans (run_correct (makeUnion leftValues) middleLeft leftContext.normal.facts.coherent.valid).2 lg)
        (grows_trans (run_correct (makeUnion rightValues) middleRight rightContext.normal.facts.coherent.valid).2 rg)
      rw [← related] at rg ⊢
      exact InternedObservedAbsence.run_shared _ middleLeft middleRight common
        leftContext.normal.facts.coherent.valid rightContext.normal.facts.coherent.valid lg rg
  | binder smart body =>
      rw [build] at firstDone secondDone
      change ((callback body (inputs.map (input firstNames)) .depth left).bind fun depth middle =>
        (callback body (inputs.map (input firstNames)) (.uninterned (ordinaryLevel depth)) middle).bind fun ordinary beforeRequest =>
          request smart depth ordinary (callback body (inputs.map (input firstNames))) beforeRequest) = .done first afterLeft at firstDone
      change ((callback body (inputs.map (input secondNames)) .depth right).bind fun depth middle =>
        (callback body (inputs.map (input secondNames)) (.uninterned (ordinaryLevel depth)) middle).bind fun ordinary beforeRequest =>
          request smart depth ordinary (callback body (inputs.map (input secondNames))) beforeRequest) = .done second afterRight at secondDone
      obtain ⟨leftDepth, afterLeftDepth, leftDepthDone, leftLater⟩ := bind_done _ _ _ _ firstDone
      obtain ⟨rightDepth, afterRightDepth, rightDepthDone, rightLater⟩ := bind_done _ _ _ _ secondDone
      obtain ⟨leftOrdinary, beforeLeftRequest, leftOrdinaryDone, leftRequestDone⟩ := bind_done _ _ _ _ leftLater
      obtain ⟨rightOrdinary, beforeRightRequest, rightOrdinaryDone, rightRequestDone⟩ := bind_done _ _ _ _ rightLater
      have leftDepthContext : Context afterLeftDepth (inputs.map (input firstNames)) := by
        simpa only [leftDepthDone, Outcome.state] using lc.callback body .depth (depth_available left)
      have rightDepthContext : Context afterRightDepth (inputs.map (input secondNames)) := by
        simpa only [rightDepthDone, Outcome.state] using rc.callback body .depth (depth_available right)
      have leftRequestContext : Context beforeLeftRequest (inputs.map (input firstNames)) := by
        simpa only [leftOrdinaryDone, Outcome.state] using
          leftDepthContext.callback body (.uninterned (ordinaryLevel leftDepth)) (ordinary_available afterLeftDepth (ordinaryLevel leftDepth))
      have rightRequestContext : Context beforeRightRequest (inputs.map (input secondNames)) := by
        simpa only [rightOrdinaryDone, Outcome.state] using
          rightDepthContext.callback body (.uninterned (ordinaryLevel rightDepth)) (ordinary_available afterRightDepth (ordinaryLevel rightDepth))
      have leftRequestGrowth : Grows beforeLeftRequest afterLeft := by
        simpa only [leftRequestDone, Outcome.state] using
          (request_correct smart leftDepth leftOrdinary _ (InternedFreshOrdinaryActiveOrigins.callback_growing body (inputs.map (input firstNames)))
            beforeLeftRequest leftRequestContext.normal.facts.coherent.valid).2
      have rightRequestGrowth : Grows beforeRightRequest afterRight := by
        simpa only [rightRequestDone, Outcome.state] using
          (request_correct smart rightDepth rightOrdinary _
            (InternedFreshOrdinaryActiveOrigins.callback_growing body (inputs.map (input secondNames)))
            beforeRightRequest rightRequestContext.normal.facts.coherent.valid).2
      have leftOrdinaryGrowth : Grows afterLeftDepth beforeLeftRequest := by
        simpa only [leftOrdinaryDone, Outcome.state] using
          (InternedFreshOrdinaryActiveOrigins.callback_growing body (inputs.map (input firstNames)) (.uninterned (ordinaryLevel leftDepth))
            afterLeftDepth leftDepthContext.normal.facts.coherent.valid).2
      have rightOrdinaryGrowth : Grows afterRightDepth beforeRightRequest := by
        simpa only [rightOrdinaryDone, Outcome.state] using
          (InternedFreshOrdinaryActiveOrigins.callback_growing body (inputs.map (input secondNames)) (.uninterned (ordinaryLevel rightDepth))
            afterRightDepth rightDepthContext.normal.facts.coherent.valid).2
      have depthSame := callback_same body (build_same body) smart inputs firstNames secondNames .depth
        agree left right common afterLeftDepth afterRightDepth lc rc coherent
        (depth_available left) (depth_available right) leftDepth rightDepth leftDepthDone rightDepthDone
        (grows_trans leftOrdinaryGrowth (grows_trans leftRequestGrowth lg))
        (grows_trans rightOrdinaryGrowth (grows_trans rightRequestGrowth rg))
      subst rightDepth
      have ordinarySame := callback_same body (build_same body) smart inputs firstNames secondNames
        (.uninterned (ordinaryLevel leftDepth)) agree
        afterLeftDepth afterRightDepth common beforeLeftRequest beforeRightRequest leftDepthContext rightDepthContext coherent
        (ordinary_available afterLeftDepth (ordinaryLevel leftDepth)) (ordinary_available afterRightDepth (ordinaryLevel leftDepth))
        leftOrdinary rightOrdinary leftOrdinaryDone rightOrdinaryDone
        (grows_trans leftRequestGrowth lg) (grows_trans rightRequestGrowth rg)
      subst rightOrdinary
      exact InternedRequestAgreement.request_same smart leftDepth leftOrdinary _ _
        beforeLeftRequest beforeRightRequest afterLeft afterRight common first second
        leftRequestContext.normal.facts.coherent.valid rightRequestContext.normal.facts.coherent.valid
        (InternedFreshOrdinaryActiveOrigins.callback_growing body (inputs.map (input firstNames)))
        (InternedFreshOrdinaryActiveOrigins.callback_growing body (inputs.map (input secondNames)))
        leftRequestDone rightRequestDone lg rg
termination_by sizeOf expression

/-- Ordered completed child calls agree when all retained lexical inputs agree. -/
theorem buildMany_same [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (agree : ∀ atom ∈ (evaluateMany expressions (inputs.map inputProfile) (inputs.map inputNames)).flatten,
      Sum.elim id firstNames atom = Sum.elim id secondNames atom)
    (left right common afterLeft afterRight : State Symbol Guard)
    (lc : Context left (inputs.map (input firstNames))) (rc : Context right (inputs.map (input secondNames))) (coherent : Coherent common)
    (first second : List (Value Symbol Guard))
    (firstDone : buildMany expressions (inputs.map (input firstNames)) left = .done first afterLeft)
    (secondDone : buildMany expressions (inputs.map (input secondNames)) right = .done second afterRight)
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
      have leftContext : Context middleLeft (inputs.map (input firstNames)) := by simpa only [headLeftDone, Outcome.state] using lc.build head
      have rightContext : Context middleRight (inputs.map (input secondNames)) := by
        simpa only [headRightDone, Outcome.state] using rc.build head
      have leftTailGrowth : Grows middleLeft lastLeft := by
        simpa only [tailLeftDone, Outcome.state] using
          (buildMany_correct tail (inputs.map (input firstNames)) middleLeft leftContext.normal.facts.coherent.valid).2
      have rightTailGrowth : Grows middleRight lastRight := by
        simpa only [tailRightDone, Outcome.state] using
          (buildMany_correct tail (inputs.map (input secondNames)) middleRight rightContext.normal.facts.coherent.valid).2
      have headSame := build_same head inputs firstNames secondNames
        (fun atom member => agree atom (by simp only [evaluateMany, List.flatten_cons, List.mem_append]; exact Or.inl member))
        left right common middleLeft middleRight lc rc coherent
        leftHead rightHead headLeftDone headRightDone (grows_trans leftTailGrowth lg) (grows_trans rightTailGrowth rg)
      have tailSame := buildMany_same tail inputs firstNames secondNames
        (fun atom member => agree atom (by simp only [evaluateMany, List.flatten_cons, List.mem_append]; exact Or.inr member))
        middleLeft middleRight common lastLeft lastRight
        leftContext rightContext coherent leftTail rightTail tailLeftDone tailRightDone lg rg
      rw [headSame, tailSame]
termination_by sizeOf expressions

/-- Completed source edge lists have equal surviving records when live inputs agree. -/
theorem buildEdges_same [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (agree : ∀ atom ∈ evaluateEdges expressions (inputs.map inputProfile) (inputs.map inputNames),
      Sum.elim id firstNames atom = Sum.elim id secondNames atom)
    (left right common afterLeft afterRight : State Symbol Guard)
    (lc : Context left (inputs.map (input firstNames))) (rc : Context right (inputs.map (input secondNames))) (coherent : Coherent common)
    (first second : List (EdgeValue Symbol Guard))
    (firstDone : buildEdges expressions (inputs.map (input firstNames)) left = .done first afterLeft)
    (secondDone : buildEdges expressions (inputs.map (input secondNames)) right = .done second afterRight)
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
          have leftContext : Context middleLeft (inputs.map (input firstNames)) := by simpa only [childrenLeftDone, Outcome.state] using lc.many children
          have rightContext : Context middleRight (inputs.map (input secondNames)) := by
            simpa only [childrenRightDone, Outcome.state] using rc.many children
          have leftAvailable := (buildMany_verified children _ left lc.normal.facts lc.inputs).result leftValues middleLeft childrenLeftDone
          have rightAvailable := (buildMany_verified children _ right rc.normal.facts rc.inputs).result rightValues middleRight childrenRightDone
          have leftEdgeContext : Context afterLeftEdge (inputs.map (input firstNames)) := by
            have current := leftContext.edge symbol guard leftValues leftAvailable
            change Context (work (makeEdge symbol guard leftValues) middleLeft).state (inputs.map (input firstNames)) at current
            simpa only [edgeLeftDone, Outcome.state] using current
          have rightEdgeContext : Context afterRightEdge (inputs.map (input secondNames)) := by
            have current := rightContext.edge symbol guard rightValues rightAvailable
            change Context (work (makeEdge symbol guard rightValues) middleRight).state _ at current
            simpa only [edgeRightDone, Outcome.state] using current
          have leftTailGrowth : Grows afterLeftEdge lastLeft := by
            simpa only [tailLeftDone, Outcome.state] using
              (buildEdges_correct tail (inputs.map (input firstNames)) afterLeftEdge leftEdgeContext.normal.facts.coherent.valid).2
          have rightTailGrowth : Grows afterRightEdge lastRight := by
            simpa only [tailRightDone, Outcome.state] using
              (buildEdges_correct tail (inputs.map (input secondNames)) afterRightEdge rightEdgeContext.normal.facts.coherent.valid).2
          have leftEdgeGrowth : Grows middleLeft afterLeftEdge := by
            simpa only [edgeLeftDone, Outcome.state] using (work_correct (makeEdge symbol guard leftValues) middleLeft leftContext.normal.facts.coherent.valid).2
          have rightEdgeGrowth : Grows middleRight afterRightEdge := by
            simpa only [edgeRightDone, Outcome.state] using (work_correct (makeEdge symbol guard rightValues) middleRight rightContext.normal.facts.coherent.valid).2
          have tailSame := buildEdges_same tail inputs firstNames secondNames
            (fun atom member => agree atom (by simp only [evaluateEdges, List.mem_append]; exact Or.inr member))
            afterLeftEdge afterRightEdge common lastLeft lastRight
            leftEdgeContext rightEdgeContext coherent leftTail rightTail tailLeftDone tailRightDone lg rg
          have leftLive := InternedFreshOrdinaryLexicalLiveness.buildMany_empty children inputs firstNames left middleLeft lc leftValues childrenLeftDone
          have rightLive := InternedFreshOrdinaryLexicalLiveness.buildMany_empty children inputs secondNames right middleRight rc rightValues childrenRightDone
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
          cases live : (InternedProfileSemantics.evaluateMany children (inputs.map inputProfile)).all
              (fun child => !InternedProfileSemantics.isEmpty child) with
          | false =>
              simpa only [surviving, List.filter_cons, leftChildren, rightChildren, leftLive, rightLive,
                live, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] using tailSame
          | true =>
              have childrenSame := buildMany_same children inputs firstNames secondNames
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

end MicroCFTA.InternedFreshOrdinaryLiveInputReplay
