import MicroCFTA.SourcePruningEnumerationStorageCallbackProgress
import MicroCFTA.SourcePruningEnumerationPathRecordingValues

/-!
# Actual neutral recording control

Recording retains the stored slot and recursion-history inputs to control.
The bound on the number of neutral transitions remains open.
-/
namespace MicroCFTA.SourcePruningEnumerationNeutralControl
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule
open SourcePruningPartialMatch SourcePruningTemplates SourcePruningEnumerationPathTransport
attribute [local instance] FormulaExecutable.formulaDecidableEq

local instance recordingControlMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

private def controlView {Symbol Guard : Type} (state : State Symbol Guard) :
    Nat × List (UVarValue Symbol) × (Nat → List RecursionKey) × List RecursionKey :=
  (state.counter, state.values, state.recursionAncestry, state.expansionAncestry)

private theorem pure_controlView {Symbol Guard α : Type} (value result : α)
    (before after : State Symbol Guard)
    (success : Success (pure value) before result after) : (controlView after) = (controlView before) := by
  obtain ⟨_, rfl⟩ := (success_pure value result before after).mp success
  rfl

private theorem representative_controlView {Symbol Guard : Type} (fuel uv root : Nat)
    (before after : State Symbol Guard)
    (success : Success (representative fuel uv) before root after) :
    (controlView after) = (controlView before) := by
  obtain ⟨_found, _, _, rfl⟩ := (representative_success fuel uv before after root).mp success
  rfl

private theorem getValue_controlView {Symbol Guard : Type} (fuel uv : Nat)
    (before after : State Symbol Guard) (value : UVarValue Symbol)
    (success : Success (getValue fuel uv) before value after) : (controlView after) = (controlView before) := by
  obtain ⟨_found, _, _, rfl⟩ := (getValue_success fuel uv before after value).mp success
  rfl

private theorem expandPartial_controlView {Symbol Guard : Type} (graph : Graph Symbol Guard)
    (fuel : Nat) (fragment : Fragment Symbol) (before after : State Symbol Guard)
    (term : Term (PartialSymbol Symbol))
    (success : Success (expandPartial graph fuel fragment) before term after) :
    (controlView after) = (controlView before) := by
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
              (controlView previous) = (controlView before) →
              Success (expandPartial graph fuel child) previous output next →
              (controlView next) = (controlView before) := by
            intro child _ previous output next previousControl reading
            exact (ih child previous next output reading).trans previousControl
          have rendered := mapM_invariant (expandPartial graph fuel)
            (fun state => (controlView state) = (controlView before)) children step
            before middle terms (Eq.refl _) traversed
          exact (pure_controlView _ term middle after final).trans rendered
      | hole uv =>
          change Success (getValue (fuel + 1) uv >>= fun value => match value with
            | .enumerated stored => expandPartial graph fuel stored
            | .unenumerated (some node) [] => match graph.node node with
              | .recursive _ => pure (.node .truncated [])
              | _ => pure (.node (.hole uv) [])
            | _ => pure (.node (.hole uv) [])) before term after at success
          obtain ⟨value, middle, reading, final⟩ := (success_bind _ _ _ _ _).mp success
          have readControl := getValue_controlView (fuel + 1) uv before middle value reading
          cases value with
          | eliminated => exact (pure_controlView _ term middle after final).trans readControl
          | enumerated stored => exact (ih stored middle after term final).trans readControl
          | unenumerated node scs =>
              cases node with
              | none => exact (pure_controlView _ term middle after final).trans readControl
              | some node =>
                  cases scs with
                  | cons first rest => exact (pure_controlView _ term middle after final).trans readControl
                  | nil =>
                      cases view : graph.node node <;> simp only [view] at final <;>
                        exact (pure_controlView _ term middle after final).trans readControl

private theorem resume_controlView {Symbol Guard : Type} [DecidableEq Symbol]
    (fuel current : Nat) (term : Term (PartialSymbol Symbol)) (pending : Pending Symbol)
    (before after : State Symbol Guard) (result : Option (Pending Symbol))
    (success : Success (SourcePruningResume.resume fuel current term pending) before result after) :
    (controlView after) = (controlView before) := by
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
      (controlView previous) = (controlView before) → Success (part entry) previous output next →
      (controlView next) = (controlView before) := by
    intro entry _ previous output next previousControl reading
    change Success (representative fuel entry.2 >>= fun root =>
      pure (if root = current then matchPartial entry.1 term else some [(entry.1, root)]))
      previous output next at reading
    obtain ⟨root, resolved, read, finished⟩ := (success_bind _ _ _ _ _).mp reading
    exact (pure_controlView _ output resolved next finished).trans
      ((representative_controlView fuel entry.2 root previous resolved read).trans previousControl)
  have middleControl := mapM_invariant part (fun state => (controlView state) = (controlView before))
    pending step before middle results (Eq.refl _) traversed
  exact (pure_controlView _ result middle after final).trans middleControl

local notation "Symbol" => SourcePruningTemplates.Symbol

private theorem oracle_controlView {Guard : Type} (graph : Graph Symbol Guard)
    (templates : List (Template.Pattern Symbol)) (fuel : Nat) (pending : List (Pending Symbol))
    (uv : Nat) (input : Sum (Fragment Symbol) Nat) (before after : State Symbol Guard)
    (result : Bool × List (Pending Symbol))
    (success : Success (SourcePruningOracle.oracle graph templates fuel pending uv input)
      before result after) : (controlView after) = (controlView before) := by
  cases input with
  | inr node => exact pure_controlView _ result before after success
  | inl fragment =>
      simp only [SourcePruningOracle.oracle] at success
      split at success
      · exact pure_controlView _ result before after success
      · split at success
        · exact pure_controlView _ result before after success
        · change Success (expandPartial graph fuel fragment >>= fun term =>
            pending.mapM (SourcePruningResume.resume fuel uv term) >>= fun resumed =>
            pure (finishChecks resumed (startMatches templates term))) before result after at success
          obtain ⟨term, middle, rendered, continued⟩ := (success_bind _ _ _ _ _).mp success
          obtain ⟨resumed, last, traversed, final⟩ := (success_bind _ _ _ _ _).mp continued
          have renderedControl := expandPartial_controlView graph fuel fragment before middle term rendered
          have step : ∀ group ∈ pending,
              ∀ (previous : State Symbol Guard) output (next : State Symbol Guard),
              (controlView previous) = (controlView middle) →
              Success (SourcePruningResume.resume fuel uv term group) previous output next →
              (controlView next) = (controlView middle) := by
            intro group _ previous output next previousControl reading
            exact (resume_controlView fuel uv term group previous next output reading).trans previousControl
          have groupControl := mapM_invariant (SourcePruningResume.resume fuel uv term)
            (fun state => (controlView state) = (controlView middle)) pending step
            middle last resumed (Eq.refl _) traversed
          exact (pure_controlView _ result last after final).trans (groupControl.trans renderedControl)

private theorem recordTypes_controlView {Guard Typing : Type} (graph : Graph Symbol Guard)
    (templates : List (Template.Pattern Symbol)) (fuel : Nat)
    (metadata : SourcePruningRecordTypes.Metadata Typing) (uv : Nat)
    (input : Sum (Fragment Symbol) Nat) (before after : State Symbol Guard)
    (result : Bool × SourcePruningRecordTypes.Metadata Typing)
    (success : Success (SourcePruningRecordTypes.recordTypes graph templates fuel metadata uv input)
      before result after) : (controlView after) = (controlView before) := by
  cases templates with
  | nil =>
      rw [SourcePruningRecordTypes.recordTypes_empty] at success
      exact pure_controlView _ result before after success
  | cons first rest =>
      change Success (SourcePruningOracle.oracle graph (first :: rest) fuel metadata.pending uv input >>=
        fun observed => pure (observed.1, {metadata with pending := observed.2, types := SourcePruningRecordTypes.updatedTypes metadata uv input}))
        before result after at success
      obtain ⟨observed, middle, read, finished⟩ := (success_bind _ _ _ _ _).mp success
      exact (pure_controlView _ result middle after finished).trans
        (oracle_controlView graph (first :: rest) fuel metadata.pending uv input before middle observed read)

/-- Every successful recording retains stored slots, the counter and both recursion histories. -/
theorem recordTypes_control {Guard Typing : Type}
    (graph : Graph Symbol Guard) (templates : List (Template.Pattern Symbol))
    (fuel : Nat) (metadata : SourcePruningRecordTypes.Metadata Typing) (uv : Nat)
    (input : Sum (Fragment Symbol) Nat) (before after : State Symbol Guard)
    (result : Bool × SourcePruningRecordTypes.Metadata Typing)
    (success : Success (SourcePruningRecordTypes.recordTypes graph templates fuel metadata uv input)
      before result after) :
    after.counter = before.counter ∧ after.values = before.values ∧
      after.recursionAncestry = before.recursionAncestry ∧
      after.expansionAncestry = before.expansionAncestry := by
  have control := recordTypes_controlView graph templates fuel metadata uv input before after result success
  exact ⟨congrArg Prod.fst control,
    congrArg (fun view => view.2.1) control,
    congrArg (fun view => view.2.2.1) control,
    congrArg (fun view => view.2.2.2) control⟩

/-- The actual singleton callback retains the same stored control fields. -/
theorem singleton_control {Guard Typing : Type}
    (graph : Graph Symbol Guard) (templates : List (Template.Pattern Symbol))
    (fuel : Nat) (metadata : SourcePruningRecordTypes.Metadata Typing) (uv : Nat)
    (input : Sum (Fragment Symbol) Nat) (before after : State Symbol Guard)
    (result : Bool × SourcePruningRecordTypes.Metadata Typing)
    (observed : ExceptT.run (SourcePruningRecordTypes.recordTypes
      graph templates fuel metadata uv input before) = [.ok (result, after)]) :
    after.counter = before.counter ∧ after.values = before.values ∧
      after.recursionAncestry = before.recursionAncestry ∧
      after.expansionAncestry = before.expansionAncestry := by
  apply recordTypes_control graph templates fuel metadata uv input before after result
  change Except.ok (result, after) ∈ ExceptT.run (SourcePruningRecordTypes.recordTypes
    graph templates fuel metadata uv input before)
  rw [observed]
  exact List.mem_singleton_self _

/-- Every successful recording retains the chosen-term cost without a total forest premise. -/
theorem recordTypes_pendingSize {Guard Typing : Type}
    (graph : Graph Symbol Guard) (templates : List (Template.Pattern Symbol))
    (fuel : Nat) (metadata : SourcePruningRecordTypes.Metadata Typing) (uv : Nat)
    (input : Sum (Fragment Symbol) Nat) (before after : State Symbol Guard)
    (result : Bool × SourcePruningRecordTypes.Metadata Typing)
    (assignment : Nat → Term Symbol)
    (success : Success (SourcePruningRecordTypes.recordTypes graph templates fuel metadata uv input)
      before result after) :
    EnumerationStorageProgress.pendingSize after assignment =
      EnumerationStorageProgress.pendingSize before assignment := by
  have values := (recordTypes_control graph templates fuel metadata uv input before after result success).2.1
  unfold EnumerationStorageProgress.pendingSize
  rw [values]

end MicroCFTA.SourcePruningEnumerationNeutralControl
