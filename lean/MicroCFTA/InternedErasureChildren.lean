import MicroCFTA.InternedErasureSyntax

/-!
# Source-ordered residuals for erased child dependencies

Actual earlier child, edge, and parent records supply every replay step.
Residual composition keeps new discarded-edge effects in source order.
-/
namespace MicroCFTA.InternedErasureChildren
open InternedConstructorTemplates InternedNestedConstruction InternedRecordCoherence
open InternedNestedSpecialization InternedNestedCoherence InternedErasureResidual
open InternedErasedEdgeReplay (run_coherent)

/-- Earlier completed child lists combine locally derived erased-dependency residuals. -/
theorem many_residual [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (first second : List (Value Symbol Guard))
    (children : ∀ expression ∈ expressions, ∀ before value final, Coherent before →
      build expression first before = .done value final → Residual value final (build expression second))
    (before final : State Symbol Guard) (values : List (Value Symbol Guard)) (coherent : Coherent before)
    (completed : buildMany expressions first before = .done values final) :
    Residual values final (buildMany expressions second) := by
  induction expressions generalizing before values with
  | nil =>
      simp only [buildMany, Outcome.done.injEq] at completed
      obtain ⟨rfl, rfl⟩ := completed
      exact pure_residual [] before _ (fun _ _ _ => by simp only [buildMany])
  | cons head tail ih =>
      simp only [buildMany] at completed
      obtain ⟨value, middle, headDone, remaining⟩ := bind_done _ _ _ _ completed
      obtain ⟨tailValues, last, tailDone, assembled⟩ := bind_done _ _ _ _ remaining
      simp only [Outcome.done.injEq] at assembled
      obtain ⟨rfl, same⟩ := assembled
      subst last
      have headResidual := children head (by simp) before value middle coherent headDone
      have middleCoherent : Coherent middle := by simpa only [headDone, Outcome.state] using build_coherent head first before coherent
      have tailResidual := ih (fun expression member => children expression (by simp [member]))
        middle tailValues middleCoherent tailDone
      have tailGrowth : Grows middle final := by
        simpa only [tailDone, Outcome.state] using (buildMany_correct tail first middle middleCoherent.valid).2
      have assembledResidual := bind_residual (buildMany tail second)
        (fun later current => .done (value :: later) current) tailValues final (value :: tailValues) final
        tailResidual (pure_residual _ final _ (fun _ _ _ => rfl)) (grows_refl final)
      have result := bind_residual (build head second)
        (fun value current => (buildMany tail second current).bind fun later last => .done (value :: later) last)
        value middle (value :: tailValues) final headResidual assembledResidual tailGrowth
      simpa only [Residual, buildMany] using result

/-- Earlier source edge lists replay each edge after their changed child residual effects. -/
theorem edges_residual [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (first second : List (Value Symbol Guard))
    (children : ∀ symbol constraint expressions', .mk symbol constraint expressions' ∈ expressions →
      ∀ expression ∈ expressions', ∀ before value final, Coherent before →
        build expression first before = .done value final → Residual value final (build expression second))
    (before final : State Symbol Guard) (values : List (EdgeValue Symbol Guard)) (coherent : Coherent before)
    (completed : buildEdges expressions first before = .done values final) :
    Residual values final (buildEdges expressions second) := by
  induction expressions generalizing before values with
  | nil =>
      simp only [buildEdges, Outcome.done.injEq] at completed
      obtain ⟨rfl, rfl⟩ := completed
      exact pure_residual [] before _ (fun _ _ _ => by simp only [buildEdges])
  | cons head tail ih =>
      cases head with
      | mk symbol constraint sourceChildren =>
          simp only [buildEdges] at completed
          obtain ⟨childValues, middle, childrenDone, remaining⟩ := bind_done _ _ _ _ completed
          obtain ⟨edge, afterEdge, edgeDone, afterEdgeDone⟩ := bind_done _ _ _ _ remaining
          obtain ⟨tailEdges, last, tailDone, assembled⟩ := bind_done _ _ _ _ afterEdgeDone
          simp only [Outcome.done.injEq] at assembled
          obtain ⟨rfl, same⟩ := assembled
          subst last
          have childResidual := many_residual sourceChildren first second
            (children symbol constraint sourceChildren (by simp)) before middle childValues coherent childrenDone
          have middleCoherent : Coherent middle := by
            simpa only [childrenDone, Outcome.state] using buildMany_coherent sourceChildren first before coherent
          have edgeResidual := work_residual (makeEdge symbol constraint childValues) middle afterEdge edge middleCoherent.valid edgeDone
          have edgeCorrect := work_correct (makeEdge symbol constraint childValues) middle middleCoherent.valid
          rw [edgeDone] at edgeCorrect
          have edgeCoherent : Coherent afterEdge := by
            have current := run_coherent (makeEdge symbol constraint childValues) middle (makeEdge_safe _ _ _) middleCoherent
            change Coherent (work (makeEdge symbol constraint childValues) middle).state at current
            simpa only [edgeDone, Outcome.state] using current
          have tailResidual := ih
            (fun symbol constraint expressions' member => children symbol constraint expressions' (by simp [member]))
            afterEdge tailEdges edgeCoherent tailDone
          have tailGrowth : Grows afterEdge final := by
            simpa only [tailDone, Outcome.state] using (buildEdges_correct tail first afterEdge edgeCoherent.valid).2
          have assemble := bind_residual (buildEdges tail second)
            (fun edges current => .done (edge :: edges) current) tailEdges final (edge :: tailEdges) final
            tailResidual (pure_residual _ final _ (fun _ _ _ => rfl)) (grows_refl final)
          have edgeAndTail := bind_residual (work (makeEdge symbol constraint childValues))
            (fun edge current => (buildEdges tail second current).bind fun edges last => .done (edge :: edges) last)
            edge afterEdge (edge :: tailEdges) final edgeResidual assemble tailGrowth
          have result := bind_residual (buildMany sourceChildren second)
            (fun values current => (work (makeEdge symbol constraint values) current).bind fun edge afterEdge =>
              (buildEdges tail second afterEdge).bind fun edges last => .done (edge :: edges) last)
            childValues middle (edge :: tailEdges) final childResidual edgeAndTail (grows_trans edgeCorrect.2 tailGrowth)
          simpa only [Residual, buildEdges] using result

end MicroCFTA.InternedErasureChildren
