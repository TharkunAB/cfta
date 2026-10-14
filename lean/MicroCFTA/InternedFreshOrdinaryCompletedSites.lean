import MicroCFTA.InternedFreshOrdinaryContext
import MicroCFTA.InternedFreshOrdinaryGrowth
import MicroCFTA.InternedNestedTraceSites

/-!
# Actual completed descendants under the repaired constructor policy

Ordered children retain their original semantic contexts. Each source site
has a completed representative inside an actual completed enclosing run.
Captured inputs can be arbitrary available values.
-/
namespace MicroCFTA.InternedFreshOrdinaryCompletedSites
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work work_correct)
open InternedNestedProvenance (Values depth_available ordinary_available)
open InternedNestedSpecialization
open InternedFreshOrdinaryContext InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryGrowth

/-- Each member of a completed child list has an actual earlier complete execution with preserved cache order. -/
theorem buildMany_member_checked [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (before : State Symbol Guard)
    (values : List (Value Symbol Guard)) (final : State Symbol Guard)
    (context : Context before environment)
    (completed : buildMany expressions environment before = .done values final)
    (selected : Syntax Symbol Guard) (member : selected ∈ expressions) :
    ∃ start value finish, build selected environment start = .done value finish ∧
      Context start environment ∧ Grows before start ∧ Grows finish final := by
  cases expressions with
  | nil => cases member
  | cons first rest =>
      simp only [buildMany] at completed
      obtain ⟨head, middle, firstDone, later⟩ := bind_done _ _ _ _ completed
      obtain ⟨tail, last, tailDone, assembled⟩ := bind_done _ _ _ _ later
      simp only [Outcome.done.injEq] at assembled
      obtain ⟨rfl, rfl⟩ := assembled
      have headFacts := build_correct first environment before context.normal.facts.coherent.valid
      rw [firstDone] at headFacts
      have headContext : Context middle environment := by
        simpa only [firstDone, Outcome.state] using context.build first
      have tailFacts := buildMany_correct rest environment middle headFacts.1
      rw [tailDone] at tailFacts
      rcases List.mem_cons.mp member with rfl | inRest
      · exact ⟨before, head, middle, firstDone, context, grows_refl _, tailFacts.2⟩
      · obtain ⟨start, value, finish, selectedDone, startValid, initialGrowth, suffix⟩ :=
          buildMany_member_checked rest environment middle tail last headContext tailDone selected inRest
        exact ⟨start, value, finish, selectedDone, startValid, grows_trans headFacts.2 initialGrowth, suffix⟩
termination_by expressions.length

/-- Every source edge child completes before edge interning and later edge computations. -/
theorem buildEdges_member_checked [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (before : State Symbol Guard)
    (values : List (EdgeValue Symbol Guard)) (final : State Symbol Guard)
    (context : Context before environment)
    (completed : buildEdges expressions environment before = .done values final)
    (symbol : Symbol) (constraint : Guard) (children : List (Syntax Symbol Guard))
    (edge : .mk symbol constraint children ∈ expressions) (selected : Syntax Symbol Guard) (member : selected ∈ children) :
    ∃ start value finish, build selected environment start = .done value finish ∧
      Context start environment ∧ Grows before start ∧ Grows finish final := by
  cases expressions with
  | nil => cases edge
  | cons first rest =>
      cases first with
      | mk own guard ownChildren =>
          simp only [buildEdges] at completed
          obtain ⟨childValues, middle, childrenDone, later⟩ := bind_done _ _ _ _ completed
          obtain ⟨builtEdge, afterEdge, edgeDone, afterEdgeDone⟩ := bind_done _ _ _ _ later
          obtain ⟨tail, last, tailDone, assembled⟩ := bind_done _ _ _ _ afterEdgeDone
          simp only [Outcome.done.injEq] at assembled
          obtain ⟨rfl, rfl⟩ := assembled
          have childrenFacts := buildMany_correct ownChildren environment before context.normal.facts.coherent.valid
          rw [childrenDone] at childrenFacts
          have childrenContext : Context middle environment := by
            simpa only [childrenDone, Outcome.state] using context.many ownChildren
          have childAvailable : Values middle childValues := (buildMany_verified ownChildren environment before context.normal.facts context.inputs).result childValues middle childrenDone
          have edgeContext : Context afterEdge environment := by
            have current := childrenContext.edge own guard childValues childAvailable
            change Context (work (makeEdge own guard childValues) middle).state environment at current
            simpa only [edgeDone, Outcome.state] using current
          have edgeFacts := work_correct (makeEdge own guard childValues) middle childrenFacts.1
          rw [edgeDone] at edgeFacts
          have tailFacts := buildEdges_correct rest environment afterEdge edgeFacts.1
          rw [tailDone] at tailFacts
          rcases List.mem_cons.mp edge with same | inRest
          · cases same
            obtain ⟨start, value, finish, selectedDone, startValid, initialGrowth, suffix⟩ :=
              buildMany_member_checked children environment before childValues middle context childrenDone selected member
            exact ⟨start, value, finish, selectedDone, startValid, initialGrowth,
              grows_trans suffix (grows_trans edgeFacts.2 tailFacts.2)⟩
          · obtain ⟨start, value, finish, selectedDone, startValid, initialGrowth, suffix⟩ :=
              buildEdges_member_checked rest environment afterEdge tail last edgeContext tailDone symbol constraint children inRest selected member
            exact ⟨start, value, finish, selectedDone, startValid,
              grows_trans childrenFacts.2 (grows_trans edgeFacts.2 initialGrowth), suffix⟩
termination_by expressions.length


/-- A descendant before any crossed binder retains an actual completed source call and context. -/
theorem zero_site [DecidableEq (EdgeKey Symbol Guard)]
    {expression target : Syntax Symbol Guard} {crossed : Nat}
    (site : InternedNestedTraceSites.Site expression target crossed) (zero : crossed = 0)
    (environment : List (Value Symbol Guard)) (before final : State Symbol Guard) (value : Value Symbol Guard)
    (context : Context before environment)
    (completed : build expression environment before = .done value final) :
    ∃ start result finish, build target environment start = .done result finish ∧
      Context start environment ∧ Grows before start ∧ Grows finish final := by
  induction site generalizing before final value with
  | here expression => exact ⟨before, value, final, completed, context, grows_refl _, grows_refl _⟩
  | @node sourceEdges symbol constraint children child target crossed edge member nested ih =>
      simp only [build] at completed
      obtain ⟨edges, middle, edgesDone, later⟩ := bind_done _ _ _ _ completed
      have edgesFacts := buildEdges_correct sourceEdges environment before context.normal.facts.coherent.valid
      rw [edgesDone] at edgesFacts
      have laterFacts := work_correct (makeNode edges) middle edgesFacts.1
      rw [later] at laterFacts
      obtain ⟨childStart, childValue, childFinal, childDone, childContext, initialGrowth, suffix⟩ :=
        buildEdges_member_checked sourceEdges environment before edges middle context edgesDone symbol constraint children edge child member
      obtain ⟨start, result, finish, targetDone, startContext, targetPrefix, targetSuffix⟩ :=
        ih zero childStart childFinal childValue childContext childDone
      exact ⟨start, result, finish, targetDone, startContext, grows_trans initialGrowth targetPrefix,
        grows_trans targetSuffix (grows_trans suffix laterFacts.2)⟩
  | @union expressions child target crossed member nested ih =>
      simp only [build] at completed
      obtain ⟨members, middle, membersDone, later⟩ := bind_done _ _ _ _ completed
      have membersFacts := buildMany_correct expressions environment before context.normal.facts.coherent.valid
      rw [membersDone] at membersFacts
      have laterFacts := work_correct (makeUnion members) middle membersFacts.1
      rw [later] at laterFacts
      obtain ⟨childStart, childValue, childFinal, childDone, childContext, initialGrowth, suffix⟩ :=
        buildMany_member_checked expressions environment before members middle context membersDone child member
      obtain ⟨start, result, finish, targetDone, startContext, targetPrefix, targetSuffix⟩ :=
        ih zero childStart childFinal childValue childContext childDone
      exact ⟨start, result, finish, targetDone, startContext, grows_trans initialGrowth targetPrefix,
        grows_trans targetSuffix (grows_trans suffix laterFacts.2)⟩
  | binder nested ih => omega

end MicroCFTA.InternedFreshOrdinaryCompletedSites
