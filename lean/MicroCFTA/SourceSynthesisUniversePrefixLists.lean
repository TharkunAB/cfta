import MicroCFTA.SourceSynthesisUniversePrefixSeed
import MicroCFTA.SourceSynthesisUniversePrefixHeight
import MicroCFTA.InternedGuardedExecutionLists

/-!
# Source-ordered universe-prefix child construction

Later siblings can select the first universe. Seed advancement preserves
the allowed atoms of earlier results. Actual edge readback retains the
ordered child values. The height bounds use the original syntax sizes.
-/
namespace MicroCFTA.SourceSynthesisUniversePrefixLists
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work)
open InternedRecordCoherence (Covered)
open SourceSynthesisUniversePrefixSeed
open SourceSynthesisUniversePrefixHeight

variable {Guard : Type} [SizeOf Guard] [DecidableEq (EdgeKey String Guard)]

/-- One actual expression returns allowed atoms and an input-syntax height bound. -/
def Returns (top : Guard) (catalog : List (String × Nat)) (expression : Syntax String Guard) : Prop :=
  ∀ (pick : Option (Seed top catalog)) (state : State String Guard),
    Facts state → Covered [] state → Ready pick state →
    ∃ value final newPick,
      InternedFreshOrdinaryConstruction.build expression [] state = .done value final ∧
      Ready newPick final ∧ Advances pick newPick ∧ Allowed newPick value ∧
      height value ≤ sizeOf expression

/-- An ordered child list retains every result under its final seed. -/
def ManyReturns (top : Guard) (catalog : List (String × Nat))
    (expressions : List (Syntax String Guard)) : Prop :=
  ∀ (pick : Option (Seed top catalog)) (state : State String Guard),
    Facts state → Covered [] state → Ready pick state →
    ∃ values final newPick,
      InternedFreshOrdinaryConstruction.buildMany expressions [] state = .done values final ∧
      Ready newPick final ∧ Advances pick newPick ∧
      (∀ value ∈ values, Allowed newPick value) ∧ childrenHeight values ≤ sizeOf expressions

/-- Each source row supplies the expression property for all of its children. -/
def RowReturns (top : Guard) (catalog : List (String × Nat)) (row : EdgeSyntax String Guard) : Prop :=
  ∀ child ∈ (match row with | .mk _ _ children => children), Returns top catalog child

/-- Actual edge construction retains allowed children and the source-row height bound. -/
def EdgesReturns (top : Guard) (catalog : List (String × Nat))
    (rows : List (EdgeSyntax String Guard)) : Prop :=
  ∀ (pick : Option (Seed top catalog)) (state : State String Guard),
    Facts state → Covered [] state → Ready pick state →
    ∃ edges final newPick,
      InternedFreshOrdinaryConstruction.buildEdges rows [] state = .done edges final ∧
      Ready newPick final ∧ Advances pick newPick ∧
      (∀ edge ∈ edges, ∀ child ∈ edge.children, Allowed newPick child) ∧
      edgesHeight edges ≤ sizeOf rows

/-- Source-order list execution transports earlier results through every later seed advance. -/
theorem many_returns (top : Guard) (catalog : List (String × Nat))
    (expressions : List (Syntax String Guard)) :
    (∀ expression ∈ expressions, Returns top catalog expression) → ManyReturns top catalog expressions := by
  induction expressions with
  | nil =>
      intro _ pick state _ _ ready
      refine ⟨[], state, pick, ?_, ready, advances_refl pick, ?_⟩
      · simp only [InternedFreshOrdinaryConstruction.buildMany]
      · constructor
        · intro value member; cases member
        · simp [childrenHeight]
  | cons first rest ih =>
      intro checked pick state facts covered ready
      obtain ⟨value, afterHead, headPick, headDone, headReady, headAdvance, headAllowed, headHeight⟩ :=
        checked first List.mem_cons_self pick state facts covered ready
      have verified := InternedFreshOrdinaryFacts.build_verified first [] state facts
        (by intro value member; cases member)
      have headFacts : Facts afterHead := by simpa only [headDone, Outcome.state] using verified.facts
      have headCovered := InternedFreshOrdinaryCoverage.build_covered first [] state
        facts.coherent.valid covered value afterHead headDone
      obtain ⟨values, final, finalPick, tailDone, tailReady, tailAdvance, tailAllowed, tailHeight⟩ :=
        ih (fun expression member => checked expression (List.mem_cons_of_mem _ member))
          headPick afterHead headFacts headCovered headReady
      have completed : InternedFreshOrdinaryConstruction.buildMany (first :: rest) [] state =
          .done (value :: values) final := by
        simp only [InternedFreshOrdinaryConstruction.buildMany, headDone, Outcome.bind, tailDone]
      refine ⟨value :: values, final, finalPick, completed, tailReady,
        advances_trans headAdvance tailAdvance, ?_, ?_⟩
      · intro selected member
        rcases List.mem_cons.mp member with rfl | later
        · exact allowed_advances tailAdvance headAllowed
        · exact tailAllowed selected later
      · simp only [childrenHeight, List.cons.sizeOf_spec]
        omega

/-- Actual row interning preserves its children while the remaining rows advance the seed. -/
theorem edges_returns (top : Guard) (catalog : List (String × Nat))
    (rows : List (EdgeSyntax String Guard)) :
    (∀ row ∈ rows, RowReturns top catalog row) → EdgesReturns top catalog rows := by
  induction rows with
  | nil =>
      intro _ pick state _ _ ready
      refine ⟨[], state, pick, ?_, ready, advances_refl pick, ?_⟩
      · simp only [InternedFreshOrdinaryConstruction.buildEdges]
      · constructor
        · intro edge member; cases member
        · simp [edgesHeight]
  | cons first rest ih =>
      cases first with
      | mk symbol constraint children =>
          intro checked pick state facts covered ready
          obtain ⟨values, afterChildren, childPick, childrenDone, childrenReady,
              childrenAdvance, childrenAllowed, childrenHeightBound⟩ :=
            many_returns top catalog children (checked _ List.mem_cons_self)
              pick state facts covered ready
          have childrenVerified := InternedFreshOrdinaryFacts.buildMany_verified children [] state facts
            (by intro value member; cases member)
          have childrenFacts : Facts afterChildren := by
            simpa only [childrenDone, Outcome.state] using childrenVerified.facts
          have childrenAvailable := childrenVerified.result values afterChildren childrenDone
          have childrenCovered := InternedFreshOrdinaryCoverage.buildMany_covered children [] state
            facts.coherent.valid covered values afterChildren childrenDone
          let made := run (makeEdge symbol constraint values) afterChildren
          have edgeVerified := edge_verified symbol constraint values afterChildren childrenFacts childrenAvailable
          have edgeFacts : Facts made.2 := edgeVerified.facts
          have edgeCovered := InternedNestedCoverage.run_covered (makeEdge symbol constraint values)
            afterChildren childrenFacts.coherent.valid childrenCovered
          have edgeReady : Ready childPick made.2 := ready_makeEdge childPick symbol constraint values
            afterChildren childrenFacts.coherent.valid childrenReady
          have exactChildren : made.1.children = values :=
            (InternedGuardedExecutionLists.makeEdge_fields symbol constraint values afterChildren
              childrenFacts.coherent childrenFacts.cached childrenAvailable).2
          obtain ⟨edges, final, finalPick, tailDone, tailReady, tailAdvance, tailAllowed, tailHeight⟩ :=
            ih (fun row member => checked row (List.mem_cons_of_mem _ member))
              childPick made.2 edgeFacts edgeCovered edgeReady
          have headHeight : edgeHeight made.1 = childrenHeight values := by
            have same : edgeHeight made.1 = childrenHeight made.1.children := by
              cases made.1
              rfl
            rw [same, exactChildren]
          dsimp only [made] at tailDone
          have completed : InternedFreshOrdinaryConstruction.buildEdges
              (.mk symbol constraint children :: rest) [] state = .done (made.1 :: edges) final := by
            simp only [InternedFreshOrdinaryConstruction.buildEdges, childrenDone, Outcome.bind, work, tailDone]
            rfl
          refine ⟨made.1 :: edges, final, finalPick, completed, tailReady,
            advances_trans childrenAdvance tailAdvance, ?_, ?_⟩
          · intro edge member child selected
            rcases List.mem_cons.mp member with rfl | later
            · apply allowed_advances tailAdvance
              exact childrenAllowed child (exactChildren ▸ selected)
            · exact tailAllowed edge later child selected
          · simp only [edgesHeight, headHeight, List.cons.sizeOf_spec, EdgeSyntax.mk.sizeOf_spec]
            omega

end MicroCFTA.SourceSynthesisUniversePrefixLists
