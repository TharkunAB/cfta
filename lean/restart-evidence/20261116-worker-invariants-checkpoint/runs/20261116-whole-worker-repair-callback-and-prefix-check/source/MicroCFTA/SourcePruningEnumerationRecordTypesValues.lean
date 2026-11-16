import MicroCFTA.SourcePruningEnumerationSharedEagerNoneBuckets
import MicroCFTA.SourcePruningRecordTypes
import MicroCFTA.EnumerationPartialObservation

namespace MicroCFTA.SourcePruningEnumerationRecordTypesValues
open EnumerationState EnumerationCorrectness EnumerationSchedule
open SourcePruningEnumerationSharedEagerNoneBuckets
open SourcePruningPartialMatch
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Core" => EnumerationState.State Symbol Constraint
attribute [local instance] FormulaExecutable.formulaDecidableEq
set_option autoImplicit false
variable {Typing : Type}

local instance valuesMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

private theorem pure_values {α : Type} (value result : α) (before after : Core)
    (actual : Success (pure value) before result after) : after.values = before.values :=
  (EnumerationCompressionFrame.pure_frame value result before after actual).values

private theorem representative_values (fuel uv root : Nat) (before after : Core)
    (actual : Success (representative fuel uv) before root after) : after.values = before.values := by
  obtain ⟨found, _lookup, _rootSame, rfl⟩ :=
    (representative_success fuel uv before after root).mp actual
  rfl

private theorem get_value_values (fuel uv : Nat) (value : UVarValue Symbol) (before after : Core)
    (actual : Success (getValue fuel uv) before value after) : after.values = before.values := by
  obtain ⟨found, _lookup, _stored, rfl⟩ := (getValue_success fuel uv before after value).mp actual
  rfl

/-- Successful partial rendering changes no stored slot, even for a nontotal forest. -/
theorem partial_render_values (graph : Graph Symbol Constraint) (fuel : Nat)
    (fragment : Fragments.Fragment Symbol) (before after : Core)
    (term : Language.Term (PartialSymbol Symbol))
    (actual : Success (expandPartial graph fuel fragment) before term after) :
    after.values = before.values := by
  induction fuel generalizing fragment before after term with
  | zero => exact (success_failure .fuelExhausted before after term actual).elim
  | succ fuel ih =>
      cases fragment with
      | node symbol children =>
          change Success (children.mapM (expandPartial graph fuel) >>= fun terms =>
            pure (.node (.concrete symbol) terms)) before term after at actual
          obtain ⟨terms, middle, traversed, final⟩ := (success_bind _ _ _ _ _).mp actual
          have step : ∀ child ∈ children, ∀ previous output next,
              previous.values = before.values →
              Success (expandPartial graph fuel child) previous output next →
              next.values = before.values := by
            intro child _ previous output next previousValues childSuccess
            exact (ih child previous next output childSuccess).trans previousValues
          have rendered := mapM_invariant (expandPartial graph fuel)
            (fun state => state.values = before.values) children step before middle terms rfl traversed
          exact (pure_values _ term middle after final).trans rendered
      | hole uv =>
          rw [expandPartial] at actual
          obtain ⟨value, middle, reading, final⟩ := (success_bind _ _ _ _ _).mp actual
          have readValues := get_value_values (fuel + 1) uv value before middle reading
          cases value with
          | eliminated => exact (pure_values _ term middle after final).trans readValues
          | enumerated stored => exact (ih stored middle after term final).trans readValues
          | unenumerated node scs =>
              cases node with
              | none => exact (pure_values _ term middle after final).trans readValues
              | some node =>
                  cases scs with
                  | cons first rest => exact (pure_values _ term middle after final).trans readValues
                  | nil =>
                      cases view : graph.node node <;> simp only [view] at final <;>
                        exact (pure_values _ term middle after final).trans readValues

/-- Successful pending-group reads change no stored slot. -/
theorem resume_values (fuel current : Nat) (term : Language.Term (PartialSymbol Symbol))
    (pending : SourcePruningPartialMatch.Pending Symbol) (before after : Core)
    (result : Option (SourcePruningPartialMatch.Pending Symbol))
    (actual : Success (SourcePruningResume.resume fuel current term pending) before result after) :
    after.values = before.values := by
  let part : Template.Pattern Symbol × Nat →
      EnumerateM Symbol Constraint (Option (Pending Symbol)) := fun entry => do
    let root ← representative fuel entry.2
    pure (if root = current then matchPartial entry.1 term else some [(entry.1, root)])
  change Success (pending.mapM part >>= fun results =>
    pure ((results.mapM id : Option (List (Pending Symbol))).map (fun pieces => pieces.flatMap id)))
      before result after at actual
  obtain ⟨results, middle, traversed, final⟩ := (success_bind _ _ _ _ _).mp actual
  have step : ∀ entry ∈ pending, ∀ previous output next,
      previous.values = before.values → Success (part entry) previous output next →
      next.values = before.values := by
    intro entry _ previous output next previousValues reading
    change Success (representative fuel entry.2 >>= fun root =>
      pure (if root = current then matchPartial entry.1 term else some [(entry.1, root)]))
        previous output next at reading
    obtain ⟨root, between, compressed, finished⟩ := (success_bind _ _ _ _ _).mp reading
    exact (pure_values _ output between next finished).trans
      ((representative_values fuel entry.2 root previous between compressed).trans previousValues)
  have readValues := mapM_invariant part (fun state => state.values = before.values)
    pending step before middle results rfl traversed
  exact (pure_values _ result middle after final).trans readValues

/-- Every actual successful template oracle result retains the stored array. -/
theorem oracle_values (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (fuel : Nat) (pending : List (SourcePruningPartialMatch.Pending Symbol)) (uv : Nat)
    (input : Sum (Fragments.Fragment Symbol) Nat) (before after : Core)
    (result : Bool × List (SourcePruningPartialMatch.Pending Symbol))
    (actual : Success (SourcePruningOracle.oracle graph templates fuel pending uv input) before result after) :
    after.values = before.values := by
  cases input with
  | inr node => exact pure_values _ result before after actual
  | inl fragment =>
      by_cases rejected : SourcePruningTemplates.rejectEarly templates fragment = true
      · simp only [SourcePruningOracle.oracle, ite_eq_left rejected] at actual
        exact pure_values _ result before after actual
      · simp only [SourcePruningOracle.oracle, ite_eq_right rejected] at actual
        split at actual
        · exact pure_values _ result before after actual
        · change Success (expandPartial graph fuel fragment >>= fun term =>
            pending.mapM (SourcePruningResume.resume fuel uv term) >>= fun results =>
              pure (SourcePruningTemplates.finishChecks results (SourcePruningTemplates.startMatches templates term)))
                before result after at actual
          obtain ⟨term, middle, rendered, continued⟩ := (success_bind _ _ _ _ _).mp actual
          obtain ⟨results, last, traversed, finished⟩ := (success_bind _ _ _ _ _).mp continued
          have renderValues := partial_render_values graph fuel fragment before middle term rendered
          have step : ∀ group ∈ pending, ∀ (previous : Core)
              (output : Option (Pending Symbol)) (next : Core),
              previous.values = middle.values →
              Success (SourcePruningResume.resume fuel uv term group) previous output next →
              next.values = middle.values := by
            intro group _ previous output next previousValues reading
            exact (resume_values fuel uv term group previous next output reading).trans previousValues
          have groupValues := mapM_invariant (SourcePruningResume.resume fuel uv term)
            (fun state => state.values = middle.values) pending step middle last results rfl traversed
          exact (pure_values _ result last after finished).trans (groupValues.trans renderValues)

/-- Actual type recording retains the stored array without a root-totality premise. -/
theorem record_types_values (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (fuel : Nat) (metadata : SourcePruningRecordTypes.Metadata Typing) (uv : Nat)
    (input : Sum (Fragments.Fragment Symbol) Nat) (before after : Core)
    (result : Bool × SourcePruningRecordTypes.Metadata Typing)
    (actual : Success (SourcePruningRecordTypes.recordTypes graph templates fuel metadata uv input)
      before result after) :
    after.values = before.values := by
  unfold SourcePruningRecordTypes.recordTypes at actual
  split at actual
  · obtain ⟨observed, middle, read, finished⟩ := (success_bind _ _ _ _ _).mp actual
    exact (pure_values _ result middle after finished).trans (pure_values _ observed before middle read)
  · obtain ⟨observed, middle, read, finished⟩ := (success_bind _ _ _ _ _).mp actual
    exact (pure_values _ result middle after finished).trans
      (oracle_values graph templates fuel metadata.pending uv input before middle observed read)

/-- Every actual type-recording result retains the missing-domain bucket property. -/
theorem record_types_none_buckets (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (fuel : Nat) (metadata : SourcePruningRecordTypes.Metadata Typing) (uv : Nat)
    (input : Sum (Fragments.Fragment Symbol) Nat) (before after : Core)
    (result : Bool × SourcePruningRecordTypes.Metadata Typing) (initial : NoneBucketsEmpty before)
    (actual : Success (SourcePruningRecordTypes.recordTypes graph templates fuel metadata uv input)
      before result after) :
    NoneBucketsEmpty after := by
  exact none_buckets_of_values_eq before after initial
    (record_types_values graph templates fuel metadata uv input before after result actual)

end MicroCFTA.SourcePruningEnumerationRecordTypesValues

#print axioms MicroCFTA.SourcePruningEnumerationRecordTypesValues.partial_render_values
#print axioms MicroCFTA.SourcePruningEnumerationRecordTypesValues.resume_values
#print axioms MicroCFTA.SourcePruningEnumerationRecordTypesValues.oracle_values
#print axioms MicroCFTA.SourcePruningEnumerationRecordTypesValues.record_types_values
#print axioms MicroCFTA.SourcePruningEnumerationRecordTypesValues.record_types_none_buckets
