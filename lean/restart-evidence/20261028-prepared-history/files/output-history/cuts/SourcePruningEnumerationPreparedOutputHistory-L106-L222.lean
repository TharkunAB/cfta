    (property : Fragment → Caller width → Queries → Cached → Output width Typing → Prop)
    (hook : Fragment → Caller width → Queries → Cached →
      SourcePruningEnumerationNativeContinuations.HookResult (Output width Typing) (Failure width Typing) width)
    (checkEmpty : Bool) (workFuel uv : Nat) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (caller : Caller width) (before : Cached) (queries : Queries)
    (continued : ∀ fragment reached saved after, ∀ output ∈ hookOutputs (hook fragment reached saved after),
      property fragment reached saved after output) :
    ∀ output ∈ hookOutputs (
      let selected := SourcePruningEnumerationSelectedContinuations.run hook checkEmpty workFuel workFuel
        workFuel workFuel workFuel workFuel workFuel uv edgesOf caller before queries
      match selected.2 with
      | none => .stopped [] (.preparation uv selected.1) none
      | some folded => finish uv folded),
      ∃ fragment reached saved after,
        SourcePruningEnumerationSelectedContinuations.Invocation hook checkEmpty workFuel workFuel
          workFuel workFuel workFuel workFuel workFuel uv edgesOf
          caller before queries fragment reached saved after ∧ property fragment reached saved after output := by
  generalize observed : SourcePruningEnumerationSelectedContinuations.run hook checkEmpty workFuel workFuel
    workFuel workFuel workFuel workFuel workFuel uv edgesOf caller before queries = selected
  obtain ⟨raw, result⟩ := selected
  cases result with
  | none => intro output member; cases member
  | some folded =>
      intro output member
      rw [finish_hook_outputs] at member
      obtain ⟨fragment, reached, saved, after, invocation, emitted⟩ :=
        SourcePruningEnumerationSelectedContinuations.output_invocation hook checkEmpty workFuel workFuel
          workFuel workFuel workFuel workFuel workFuel uv edgesOf caller before queries folded (congrArg Prod.snd observed) output member
      exact ⟨fragment, reached, saved, after, invocation, continued fragment reached saved after output emitted⟩

/-- Every actual bounded resume output has its complete operation path from that resume input. -/
theorem resume_output_history
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveFuel : Nat) :
    ∀ (metadata : Metadata Typing) (caller : Caller width) (queries : Queries) (before : Cached) (next : Option Next),
      ∀ output ∈ hookOutputs (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
        workFuel recursiveFuel metadata caller queries before next),
        OutputHistory holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
          recursiveFuel metadata caller queries before next output := by
  induction recursiveFuel with
  | zero =>
      intro metadata caller queries before next output member
      cases next with
      | none =>
          simp only [resume, hookOutputs, List.mem_singleton] at member
          subst output
          exact .stopped
      | some next =>
          cases next with
          | done =>
              simp only [resume, hookOutputs, List.mem_singleton] at member
              subst output
              exact .done
          | stuck | expand _ => cases member
  | succ recursiveFuel ih =>
      intro metadata caller queries before next output member
      cases next with
      | none =>
          simp only [resume, hookOutputs, List.mem_singleton] at member
          subst output
          exact .stopped
      | some next =>
          cases next with
          | done =>
              simp only [resume, hookOutputs, List.mem_singleton] at member
              subst output
              exact .done
          | stuck => cases member
          | expand uv =>
              rw [resume] at member
              dsimp only at member
              split at member
              · cases member
              · exact .parked (by assumption) (ih _ _ _ _ _ output member)
              · cases member
              · cases member
              · have continued : ∀ (updated : Metadata Typing) (fragment : Fragment)
                    (reached : Caller width) (saved : Queries) (after : Cached),
                    ∀ output ∈ hookOutputs (continueWith
                      (resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel)
                      graph templates stop order workFuel updated uv fragment reached saved after),
                      ∃ recorded core,
                        ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates workFuel updated uv
                          (.inl fragment) after.core) = [.ok ((false, recorded), core)] ∧
                        OutputHistory holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
                          recursiveFuel recorded reached saved (EnumerationExpandableIndex.frame core after)
                            (SourcePruningEnumerationRestart.decision stop order recorded
                              (EnumerationExpandableIndex.frame core after)) output := by
                  intro updated fragment reached saved after current emitted
                  obtain ⟨recorded, core, callback, listed⟩ := continueWith_output_restart _ graph templates
                    stop order workFuel updated uv fragment reached saved after current emitted
                  exact ⟨recorded, core, callback, ih _ _ _ _ _ current listed⟩
                obtain ⟨fragment, headCaller, headQueries, headCache, invocation, recorded, core, callback, tail⟩ :=
                  selected_finish_history _ _ checkEmpty workFuel uv edgesOf _ _ _ (continued _) output member
                exact .selected (by assumption) invocation callback tail
              · cases member
              · cases member

/-- The actual driver supplies the original decision for every certified output path. -/
theorem run_output_history
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveFuel : Nat) (metadata : Metadata Typing) (caller : Caller width)
    (queries : Queries) (before : Cached) :
    ∀ output ∈ hookOutputs (run holeKey fits admits graph templates checkEmpty edgesOf stop order
      workFuel recursiveFuel metadata caller queries before),
      OutputHistory holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel
        metadata caller queries before (SourcePruningEnumerationRestart.decision stop order metadata before) output :=
  resume_output_history holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel
    metadata caller queries before _

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
