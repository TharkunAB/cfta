import MicroCFTA.SourcePruningEnumerationPathStorage
import MicroCFTA.SourcePruningRecordTypes

/-!
# Successful recording preserves stored values

The laws do not require a total representative forest.
-/

namespace MicroCFTA.SourcePruningEnumerationPathRecordingValues
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule
open SourcePruningPartialMatch SourcePruningTemplates SourcePruningEnumerationPathTransport
attribute [local instance] FormulaExecutable.formulaDecidableEq

local instance recordingValuesMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

private theorem pure_values {Symbol Guard α : Type} (value result : α)
    (before after : State Symbol Guard)
    (success : Success (pure value) before result after) : after.values = before.values := by
  obtain ⟨_, rfl⟩ := (success_pure value result before after).mp success
  rfl

private theorem representative_values {Symbol Guard : Type} (fuel uv root : Nat)
    (before after : State Symbol Guard)
    (success : Success (representative fuel uv) before root after) :
    after.values = before.values := by
  obtain ⟨_found, _, _, rfl⟩ := (representative_success fuel uv before after root).mp success
  rfl

private theorem getValue_values {Symbol Guard : Type} (fuel uv : Nat)
    (before after : State Symbol Guard) (value : UVarValue Symbol)
    (success : Success (getValue fuel uv) before value after) : after.values = before.values := by
  obtain ⟨_found, _, _, rfl⟩ := (getValue_success fuel uv before after value).mp success
  rfl

private theorem expandPartial_values {Symbol Guard : Type} (graph : Graph Symbol Guard)
    (fuel : Nat) (fragment : Fragment Symbol) (before after : State Symbol Guard)
    (term : Term (PartialSymbol Symbol))
    (success : Success (expandPartial graph fuel fragment) before term after) :
    after.values = before.values := by
  induction fuel generalizing fragment before after term with
  | zero => exact (success_failure .fuelExhausted before after term success).elim
  | succ fuel ih =>
      cases fragment with
      | node symbol children =>
          change Success (children.mapM (expandPartial graph fuel) >>= fun terms =>
            pure (.node (.concrete symbol) terms)) before term after at success
          obtain ⟨terms, middle, traversed, final⟩ := (success_bind _ _ _ _ _).mp success
          have step : ∀ child ∈ children,
              ∀ (previous : State Symbol Guard) output (next : State Symbol Guard),
              previous.values = before.values →
              Success (expandPartial graph fuel child) previous output next →
              next.values = before.values := by
            intro child _ previous output next previousValues reading
            exact (ih child previous next output reading).trans previousValues
          have rendered := mapM_invariant (expandPartial graph fuel)
            (fun state => state.values = before.values) children step
            before middle terms (Eq.refl _) traversed
          exact (pure_values _ term middle after final).trans rendered
      | hole uv =>
          change Success (getValue (fuel + 1) uv >>= fun value => match value with
            | .enumerated stored => expandPartial graph fuel stored
            | .unenumerated (some node) [] => match graph.node node with
              | .recursive _ => pure (.node .truncated [])
              | _ => pure (.node (.hole uv) [])
            | _ => pure (.node (.hole uv) [])) before term after at success
          obtain ⟨value, middle, reading, final⟩ := (success_bind _ _ _ _ _).mp success
          have readValues := getValue_values (fuel + 1) uv before middle value reading
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

private theorem resume_values {Symbol Guard : Type} [DecidableEq Symbol]
    (fuel current : Nat) (term : Term (PartialSymbol Symbol)) (pending : Pending Symbol)
    (before after : State Symbol Guard) (result : Option (Pending Symbol))
    (success : Success (SourcePruningResume.resume fuel current term pending) before result after) :
    after.values = before.values := by
  let part : Template.Pattern Symbol × Nat → EnumerateM Symbol Guard (Option (Pending Symbol)) :=
    fun entry => do
      let root ← representative fuel entry.2
      pure (if root = current then matchPartial entry.1 term else some [(entry.1, root)])
  change Success (pending.mapM part >>= fun results =>
    pure ((results.mapM id : Option (List (Pending Symbol))).map (fun pieces => pieces.flatMap id)))
    before result after at success
  obtain ⟨results, middle, traversed, final⟩ := (success_bind _ _ _ _ _).mp success
  have step : ∀ entry ∈ pending,
      ∀ (previous : State Symbol Guard) output (next : State Symbol Guard),
      previous.values = before.values → Success (part entry) previous output next →
      next.values = before.values := by
    intro entry _ previous output next previousValues reading
    change Success (representative fuel entry.2 >>= fun root =>
      pure (if root = current then matchPartial entry.1 term else some [(entry.1, root)]))
      previous output next at reading
    obtain ⟨root, resolved, read, finished⟩ := (success_bind _ _ _ _ _).mp reading
    exact (pure_values _ output resolved next finished).trans
      ((representative_values fuel entry.2 root previous resolved read).trans previousValues)
  have middleValues := mapM_invariant part (fun state => state.values = before.values)
    pending step before middle results (Eq.refl _) traversed
  exact (pure_values _ result middle after final).trans middleValues

local notation "Symbol" => SourcePruningTemplates.Symbol

private theorem oracle_values {Guard : Type} (graph : Graph Symbol Guard)
    (templates : List (Template.Pattern Symbol)) (fuel : Nat) (pending : List (Pending Symbol))
    (uv : Nat) (input : Sum (Fragment Symbol) Nat) (before after : State Symbol Guard)
    (result : Bool × List (Pending Symbol))
    (success : Success (SourcePruningOracle.oracle graph templates fuel pending uv input)
      before result after) : after.values = before.values := by
  cases input with
  | inr node => exact pure_values _ result before after success
  | inl fragment =>
      simp only [SourcePruningOracle.oracle] at success
      split at success
      · exact pure_values _ result before after success
      · split at success
        · exact pure_values _ result before after success
        · change Success (expandPartial graph fuel fragment >>= fun term =>
            pending.mapM (SourcePruningResume.resume fuel uv term) >>= fun resumed =>
            pure (finishChecks resumed (startMatches templates term))) before result after at success
          obtain ⟨term, middle, rendered, continued⟩ := (success_bind _ _ _ _ _).mp success
          obtain ⟨resumed, last, traversed, final⟩ := (success_bind _ _ _ _ _).mp continued
          have renderedValues := expandPartial_values graph fuel fragment before middle term rendered
          have step : ∀ group ∈ pending,
              ∀ (previous : State Symbol Guard) output (next : State Symbol Guard),
              previous.values = middle.values →
              Success (SourcePruningResume.resume fuel uv term group) previous output next →
              next.values = middle.values := by
            intro group _ previous output next previousValues reading
            exact (resume_values fuel uv term group previous next output reading).trans previousValues
          have groupValues := mapM_invariant (SourcePruningResume.resume fuel uv term)
            (fun state => state.values = middle.values) pending step
            middle last resumed (Eq.refl _) traversed
          exact (pure_values _ result last after final).trans (groupValues.trans renderedValues)

/-- Every successful recording preserves the complete stored value list. -/
theorem recordTypes_values {Guard Typing : Type} (graph : Graph Symbol Guard)
    (templates : List (Template.Pattern Symbol)) (fuel : Nat)
    (metadata : SourcePruningRecordTypes.Metadata Typing) (uv : Nat)
    (input : Sum (Fragment Symbol) Nat) (before after : State Symbol Guard)
    (result : Bool × SourcePruningRecordTypes.Metadata Typing)
    (success : Success (SourcePruningRecordTypes.recordTypes graph templates fuel metadata uv input)
      before result after) : after.values = before.values := by
  cases templates with
  | nil =>
      rw [SourcePruningRecordTypes.recordTypes_empty] at success
      exact pure_values _ result before after success
  | cons first rest =>
      change Success (SourcePruningOracle.oracle graph (first :: rest) fuel metadata.pending uv input >>=
        fun observed => pure (observed.1, {metadata with pending := observed.2, types := SourcePruningRecordTypes.updatedTypes metadata uv input}))
        before result after at success
      obtain ⟨observed, middle, read, finished⟩ := (success_bind _ _ _ _ _).mp success
      exact (pure_values _ result middle after finished).trans
        (oracle_values graph (first :: rest) fuel metadata.pending uv input before middle observed read)

/-- Every successful recording preserves the supplied stored path predicate. -/
theorem recordTypes_paths {Guard Typing : Type} {P : EqualityTrie.Path → Prop}
    (graph : Graph Symbol Guard) (templates : List (Template.Pattern Symbol)) (fuel : Nat)
    (metadata : SourcePruningRecordTypes.Metadata Typing) (uv : Nat)
    (input : Sum (Fragment Symbol) Nat) (before after : State Symbol Guard)
    (result : Bool × SourcePruningRecordTypes.Metadata Typing)
    (paths : StatePaths P before)
    (success : Success (SourcePruningRecordTypes.recordTypes graph templates fuel metadata uv input)
      before result after) : StatePaths P after := by
  exact SourcePruningEnumerationPathStorage.values_paths paths
    (recordTypes_values graph templates fuel metadata uv input before after result success)

end MicroCFTA.SourcePruningEnumerationPathRecordingValues
