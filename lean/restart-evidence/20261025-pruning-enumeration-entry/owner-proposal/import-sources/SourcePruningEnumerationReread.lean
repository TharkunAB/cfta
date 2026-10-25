import MicroCFTA.EnumerationObservations

namespace MicroCFTA.SourcePruningEnumerationReread
open EnumerationState EnumerationCorrectness EnumerationCompressionFrame EnumerationObservations
variable {Symbol Guard : Type}

/-- An observed pending slot derives a finite reread and its actual compressed state. -/
theorem pending_reread_complete (readFuel uv oldHandle : Nat) (scs : List EnumerationState.Suspended)
    (before readAfter entry : EnumerationState.State Symbol Guard)
    (total : UnionFind.Total before.representatives)
    (observed : Success (getValue readFuel uv) before (.unenumerated (some oldHandle) scs) readAfter)
    (entered : Frame readAfter entry) :
    ∃ (root size rereadFuel : Nat) (after : EnumerationState.State Symbol Guard),
      Frame before readAfter ∧ UnionFind.Reaches before.representatives uv root size ∧
      Success (representative rereadFuel uv) entry root after ∧
      Frame entry after ∧ Frame before after ∧
      after.values[root]? = some (.unenumerated (some oldHandle) scs) ∧ root < after.values.length := by
  obtain ⟨found, lookup, initialStored, readState⟩ :=
    (getValue_success readFuel uv before readAfter (.unenumerated (some oldHandle) scs)).mp observed
  have firstRepresentative : Success (representative readFuel uv) before found.representative readAfter := by
    exact (EnumerationSchedule.representative_success readFuel uv before readAfter found.representative).mpr
      ⟨found, lookup, rfl, readState⟩
  have firstFrame : Frame before readAfter := by
    exact representative_frame readFuel uv found.representative before readAfter total firstRepresentative
  obtain ⟨rereadFuel, after, second, finalFrame⟩ :=
    representative_transport readFuel uv before entry readAfter found.representative
      (firstFrame.trans entered) total firstRepresentative
  have rereadFrame : Frame entry after := by
    exact representative_frame rereadFuel uv found.representative entry after
      ((firstFrame.trans entered).total total) second
  have stored : after.values[found.representative]? = some (.unenumerated (some oldHandle) scs) := by
    simpa only [(firstFrame.trans finalFrame).values] using initialStored
  refine ⟨found.representative, found.size, rereadFuel, after, firstFrame,
    (UnionFind.findRoot_correct readFuel before.representatives uv found lookup).1,
    second, rereadFrame, firstFrame.trans finalFrame, stored, ?_⟩
  exact (List.getElem?_eq_some_iff.mp stored).elim (fun bound _ => bound)

/-- An actual false recursion check retains the complete compression frame. -/
theorem checkRepeated_false_frame (graph : EnumerationState.Graph Symbol Guard)
    (fuel uv node : Nat) (scs : List EnumerationState.Suspended)
    (before after : EnumerationState.State Symbol Guard) (total : UnionFind.Total before.representatives)
    (observed : Success (EnumerationDriver.checkRepeated graph fuel uv node scs) before false after) :
    Frame before after := by
  cases view : graph.node node with
  | empty | alternatives _ | unresolved _ =>
      exact pure_frame false false before after (by
        simpa only [EnumerationDriver.checkRepeated, view] using observed)
  | recursive _ =>
      simp only [EnumerationDriver.checkRepeated, view] at observed
      obtain ⟨root, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp observed
      by_cases seen : recursionKey node scs ∈ resolved.recursionAncestry root
      · simp [Success, setValue, get, getThe, MonadStateOf.get, modify, modifyGet,
          MonadStateOf.modifyGet, bind, pure, StateT.pure, StateT.bind, StateT.get, StateT.modifyGet,
          ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk, ExceptT.run, seen] at continued
      · have same : after = resolved := by
          simpa [Success, get, getThe, MonadStateOf.get, bind, pure, StateT.pure, StateT.bind,
            StateT.get, ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk,
            ExceptT.run, seen, eq_comm] using continued
        subst after
        exact representative_frame fuel uv root before resolved total resolution

end MicroCFTA.SourcePruningEnumerationReread
