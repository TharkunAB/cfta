import MicroCFTA.SourcePruningEnumerationOpaqueSuffixIsolation
import MicroCFTA.SourcePruningEnumerationRawAliasPrimitives
import MicroCFTA.SourcePruningRecordTypes
import MicroCFTA.EnumerationExecution

namespace MicroCFTA.SourcePruningEnumerationCapturedFinalizeRawAliases
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationExecution
open SourcePruningPartialMatch
open SourcePruningEnumerationRawAliasPrimitives
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard Typing : Type}
local notation "Core" => EnumerationState.State Symbol EnumGuard
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol EnumGuard
attribute [local instance] FormulaExecutable.formulaDecidableEq
set_option autoImplicit false

local instance rawAliasMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/- Note [Captured raw alias growth]
Finalization changes stored values and resets expansion ancestry.
Its successful core equation retains the representative forest exactly.
The recordTypes callback can compress that forest during partial rendering
and pending-group reads. Each successful representative read retains all
existing finite aliases. These forward laws need no total forest or safe state.
They do not identify the causal branch of an arbitrary output.
-/

private theorem pure_sameClass_forward {α : Type} (value result : α) (before after : Core)
    (actual : Success (pure value) before result after) :
    ∀ left right, UnionFind.SameClass before.representatives left right →
      UnionFind.SameClass after.representatives left right := by
  obtain ⟨_valueSame, stateSame⟩ := (success_pure value result before after).mp actual
  subst after
  exact fun _ _ same => same

private theorem get_value_sameClass_forward (fuel uv : Nat) (value : UVarValue Symbol) (before after : Core)
    (actual : Success (getValue fuel uv) before value after) :
    ∀ left right, UnionFind.SameClass before.representatives left right →
      UnionFind.SameClass after.representatives left right := by
  obtain ⟨found, lookup, _stored, rfl⟩ := (getValue_success fuel uv before after value).mp actual
  exact findRoot_sameClass_forward fuel uv before.representatives found lookup

private theorem partial_render_sameClass_forward (graph : Graph Symbol EnumGuard) (fuel : Nat)
    (fragment : Fragments.Fragment Symbol) (before after : Core)
    (term : Language.Term (PartialSymbol Symbol))
    (actual : Success (expandPartial graph fuel fragment) before term after) :
    ∀ left right, UnionFind.SameClass before.representatives left right →
      UnionFind.SameClass after.representatives left right := by
  induction fuel generalizing fragment before after term with
  | zero => exact (success_failure .fuelExhausted before after term actual).elim
  | succ fuel ih =>
    cases fragment with
    | node symbol children =>
      change Success (children.mapM (expandPartial graph fuel) >>= fun terms =>
        pure (.node (.concrete symbol) terms)) before term after at actual
      obtain ⟨terms, middle, traversed, final⟩ := (success_bind _ _ _ _ _).mp actual
      let invariant := fun state : Core => ∀ left right,
        UnionFind.SameClass before.representatives left right →
          UnionFind.SameClass state.representatives left right
      have step : ∀ child ∈ children, ∀ previous output next,
          invariant previous → Success (expandPartial graph fuel child) previous output next →
          invariant next := by
        intro child _member previous output next previousAliases childSuccess left right same
        exact ih child previous next output childSuccess left right (previousAliases left right same)
      have rendered := mapM_invariant (expandPartial graph fuel) invariant children step
        before middle terms (fun _ _ same => same) traversed
      intro left right same
      exact pure_sameClass_forward _ term middle after final left right (rendered left right same)
    | hole uv =>
      rw [expandPartial] at actual
      obtain ⟨value, middle, reading, final⟩ := (success_bind _ _ _ _ _).mp actual
      have readAliases := get_value_sameClass_forward (fuel + 1) uv value before middle reading
      cases value with
      | eliminated =>
        intro left right same
        exact pure_sameClass_forward _ term middle after final left right (readAliases left right same)
      | enumerated stored =>
        intro left right same
        exact ih stored middle after term final left right (readAliases left right same)
      | unenumerated node scs =>
        cases node with
        | none =>
          intro left right same
          exact pure_sameClass_forward _ term middle after final left right (readAliases left right same)
        | some node =>
          cases scs with
          | cons first rest =>
            intro left right same
            exact pure_sameClass_forward _ term middle after final left right (readAliases left right same)
          | nil =>
            cases view : graph.node node <;> simp only [view] at final
            all_goals
              intro left right same
              exact pure_sameClass_forward _ term middle after final left right (readAliases left right same)

private theorem resume_sameClass_forward (fuel current : Nat) (term : Language.Term (PartialSymbol Symbol))
    (pending : SourcePruningPartialMatch.Pending Symbol) (before after : Core)
    (result : Option (SourcePruningPartialMatch.Pending Symbol))
    (actual : Success (SourcePruningResume.resume fuel current term pending) before result after) :
    ∀ left right, UnionFind.SameClass before.representatives left right →
      UnionFind.SameClass after.representatives left right := by
  let part : Template.Pattern Symbol × Nat →
      EnumerateM Symbol EnumGuard (Option (Pending Symbol)) := fun entry => do
    let root ← representative fuel entry.2
    pure (if root = current then matchPartial entry.1 term else some [(entry.1, root)])
  change Success (pending.mapM part >>= fun results =>
    pure ((results.mapM id : Option (List (Pending Symbol))).map (fun pieces => pieces.flatMap id)))
      before result after at actual
  obtain ⟨results, middle, traversed, final⟩ := (success_bind _ _ _ _ _).mp actual
  let invariant := fun state : Core => ∀ left right,
    UnionFind.SameClass before.representatives left right →
      UnionFind.SameClass state.representatives left right
  have step : ∀ entry ∈ pending, ∀ previous output next,
      invariant previous → Success (part entry) previous output next → invariant next := by
    intro entry _member previous output next previousAliases reading
    change Success (representative fuel entry.2 >>= fun root =>
      pure (if root = current then matchPartial entry.1 term else some [(entry.1, root)]))
        previous output next at reading
    obtain ⟨root, between, compressed, finished⟩ := (success_bind _ _ _ _ _).mp reading
    intro left right same
    exact pure_sameClass_forward _ output between next finished left right
      (representative_sameClass_forward fuel entry.2 root previous between compressed left right
        (previousAliases left right same))
  have scanned := mapM_invariant part invariant pending step before middle results
    (fun _ _ same => same) traversed
  intro left right same
  exact pure_sameClass_forward _ result middle after final left right (scanned left right same)

private theorem oracle_sameClass_forward (graph : Graph Symbol EnumGuard)
    (templates : List (Template.Pattern Symbol)) (fuel : Nat)
    (pending : List (SourcePruningPartialMatch.Pending Symbol)) (uv : Nat)
    (input : Sum (Fragments.Fragment Symbol) Nat) (before after : Core)
    (result : Bool × List (SourcePruningPartialMatch.Pending Symbol))
    (actual : Success (SourcePruningOracle.oracle graph templates fuel pending uv input) before result after) :
    ∀ left right, UnionFind.SameClass before.representatives left right →
      UnionFind.SameClass after.representatives left right := by
  cases input with
  | inr node => exact pure_sameClass_forward _ result before after actual
  | inl fragment =>
    by_cases rejected : SourcePruningTemplates.rejectEarly templates fragment = true
    · simp only [SourcePruningOracle.oracle, ite_eq_left rejected] at actual
      exact pure_sameClass_forward _ result before after actual
    · simp only [SourcePruningOracle.oracle, ite_eq_right rejected] at actual
      split at actual
      · exact pure_sameClass_forward _ result before after actual
      · change Success (expandPartial graph fuel fragment >>= fun term =>
          pending.mapM (SourcePruningResume.resume fuel uv term) >>= fun results =>
            pure (SourcePruningTemplates.finishChecks results (SourcePruningTemplates.startMatches templates term)))
              before result after at actual
        obtain ⟨term, middle, rendered, continued⟩ := (success_bind _ _ _ _ _).mp actual
        obtain ⟨results, last, traversed, finished⟩ := (success_bind _ _ _ _ _).mp continued
        have renderedAliases := partial_render_sameClass_forward graph fuel fragment before middle term rendered
        let invariant := fun state : Core => ∀ left right,
          UnionFind.SameClass before.representatives left right →
            UnionFind.SameClass state.representatives left right
        have step : ∀ group ∈ pending, ∀ previous output next,
            invariant previous →
            Success (SourcePruningResume.resume fuel uv term group) previous output next → invariant next := by
          intro group _member previous output next previousAliases reading left right same
          exact resume_sameClass_forward fuel uv term group previous next output reading left right
            (previousAliases left right same)
        have resumed := mapM_invariant (SourcePruningResume.resume fuel uv term) invariant pending step
          middle last results renderedAliases traversed
        intro left right same
        exact pure_sameClass_forward _ result last after finished left right (resumed left right same)

private theorem record_types_sameClass_forward (graph : Graph Symbol EnumGuard)
    (templates : List (Template.Pattern Symbol)) (fuel : Nat)
    (metadata : SourcePruningRecordTypes.Metadata Typing) (uv : Nat)
    (input : Sum (Fragments.Fragment Symbol) Nat) (before after : Core)
    (result : Bool × SourcePruningRecordTypes.Metadata Typing)
    (actual : Success (SourcePruningRecordTypes.recordTypes graph templates fuel metadata uv input)
      before result after) :
    ∀ left right, UnionFind.SameClass before.representatives left right →
      UnionFind.SameClass after.representatives left right := by
  unfold SourcePruningRecordTypes.recordTypes at actual
  split at actual
  · obtain ⟨observed, middle, read, finished⟩ := (success_bind _ _ _ _ _).mp actual
    intro left right same
    exact pure_sameClass_forward _ result middle after finished left right
      (pure_sameClass_forward _ observed before middle read left right same)
  · obtain ⟨observed, middle, read, finished⟩ := (success_bind _ _ _ _ _).mp actual
    intro left right same
    exact pure_sameClass_forward _ result middle after finished left right
      (oracle_sameClass_forward graph templates fuel metadata.pending uv input before middle observed read left right same)

/-- Finalization retains every entry raw alias at its actual returned cache. -/
theorem finalize_sameClass_forward
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (indexFuel target : Nat) (fragment : Fragments.Fragment Symbol)
    (before finished : Cached)
    (observed : SourcePruningEnumerationFinalize.run heap indexFuel target fragment before = some finished) :
    ∀ (left right : Nat), UnionFind.SameClass before.core.representatives left right →
      UnionFind.SameClass finished.core.representatives left right
 := by
  have core := EnumerationDischargeHistory.finalize_core_of_run heap indexFuel target fragment before finished observed
  rw [core]
  exact fun _ _ same => same

/-- The actual false fragment callback retains aliases at its framed returned cache. -/
theorem false_recordTypes_sameClass_forward
    (graph : Graph Symbol EnumGuard) (templates : List (Template.Pattern Symbol))
    (callbackFuel uv : Nat) (metadata updated : SourcePruningRecordTypes.Metadata Typing)
    (fragment : Fragments.Fragment Symbol) (before : Cached) (after : Core)
    (observed : ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates callbackFuel metadata uv
      (.inl fragment) before.core) = [.ok ((false, updated), after)]) :
    ∀ (left right : Nat), UnionFind.SameClass before.core.representatives left right →
      UnionFind.SameClass (EnumerationExpandableIndex.frame after before).core.representatives left right
 := by
  have successful : Success (SourcePruningRecordTypes.recordTypes graph templates callbackFuel metadata uv
      (.inl fragment)) before.core (false, updated) after := by
    rw [Success, observed]
    exact List.mem_singleton_self _
  exact record_types_sameClass_forward graph templates callbackFuel metadata uv
    (.inl fragment) before.core after (false, updated) successful

end MicroCFTA.SourcePruningEnumerationCapturedFinalizeRawAliases

#print axioms MicroCFTA.SourcePruningEnumerationCapturedFinalizeRawAliases.finalize_sameClass_forward
#print axioms MicroCFTA.SourcePruningEnumerationCapturedFinalizeRawAliases.false_recordTypes_sameClass_forward
