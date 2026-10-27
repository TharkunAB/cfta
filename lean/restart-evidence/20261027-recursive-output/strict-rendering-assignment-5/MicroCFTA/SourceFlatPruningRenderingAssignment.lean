import MicroCFTA.SourceFlatPruningRendering
import MicroCFTA.EnumerationFlatSemantics

/-!
# Assignments from actual flat output rendering

The original safe ordered packet constructs the fragment assignment.
Actual direct-root rendering determines the root term and all residual terms.
Discharge and residual checks remain explicit. Reads retain the entire flat state.
-/
namespace MicroCFTA.SourceFlatPruningRendering
open Language Fragments EnumerationFlatState
open EnumerationCorrectness (NodeLanguage heap slot guardsHold)
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {NativeGuard EnumGuard α β : Type}
attribute [local instance] SourcePruningEnumerationTerminalPrefix.terminalPrefixMonadList
  SourcePruningEnumerationTerminalPrefix.terminalPrefixLawfulMonadList

/-- Remaining pending slots are unrestricted equality variables. -/
def Discharged (state : State Symbol EnumGuard) : Prop :=
  ∀ (uv : Nat) (node : Option Nat) (scs : List EnumerationState.Suspended), state.values[uv]? = some (.unenumerated node scs) → node = none ∧ scs = []

private abbrev Success (action : Action Symbol EnumGuard α) (before : State Symbol EnumGuard)
    (value : α) (after : State Symbol EnumGuard) : Prop :=
  Except.ok (value, after) ∈ ExceptT.run (action before)

private theorem success_bind (action : Action Symbol EnumGuard α)
    (next : α → Action Symbol EnumGuard β) (before after : State Symbol EnumGuard) (value : β) :
    Success (action >>= next) before value after ↔
      ∃ middle intermediate, Success action before middle intermediate ∧
        Success (next middle) intermediate value after := by
  simp only [Success, EnumerationResultRelation.stateT_bind_rows,
    EnumerationCPSChecked.bindRows, ExceptT.run, List.mem_flatMap]
  constructor
  · rintro ⟨result, member, continued⟩
    cases result with
    | error error => simp at continued
    | ok pair => exact ⟨pair.1, pair.2, member, continued⟩
  · rintro ⟨middle, intermediate, member, continued⟩
    exact ⟨.ok (middle, intermediate), member, continued⟩

private theorem success_pure (value result : α) (before after : State Symbol EnumGuard) :
    Success (pure value) before result after ↔ result = value ∧ after = before := by
  simp [Success, pure, StateT.pure, ExceptT.pure, ExceptT.mk, ExceptT.run, eq_comm]

private theorem mapM_read (action : α → Action Symbol EnumGuard β) (function : α → β)
    (state : State Symbol EnumGuard)
    (step : ∀ input result after, Success (action input) state result after →
      after = state ∧ result = function input)
    (inputs : List α) (outputs : List β) (after : State Symbol EnumGuard)
    (observed : Success (inputs.mapM action) state outputs after) :
    after = state ∧ outputs = inputs.map function := by
  induction inputs generalizing outputs after with
  | nil =>
      obtain ⟨rfl, rfl⟩ := (success_pure [] outputs state after).mp observed
      exact ⟨rfl, rfl⟩
  | cons input rest ih =>
      rw [List.mapM_cons] at observed
      obtain ⟨output, middle, first, continued⟩ := (success_bind _ _ _ _ _).mp observed
      obtain ⟨middleSame, same⟩ := step input output middle first
      subst middle
      obtain ⟨tail, last, remaining, final⟩ := (success_bind _ _ _ _ _).mp continued
      obtain ⟨lastSame, tailSame⟩ := ih tail last remaining
      subst last
      obtain ⟨outputsSame, afterSame⟩ := (success_pure (output :: tail) outputs state after).mp final
      subst outputs after
      exact ⟨rfl, by simp only [List.map_cons, same, tailSame]⟩

private def Valid (language : NodeLanguage Symbol) (assignment : Nat → Term Symbol)
    (state : State Symbol EnumGuard) : Prop :=
  FlatUnionFind.Valid state.representatives ∧
    (FlatUnionFind.Satisfies state.representatives assignment ∧
      heapSatisfies (heap language state.values) assignment) ∧ Discharged state

private theorem read_sound (language : NodeLanguage Symbol) (assignment : Nat → Term Symbol)
    (uv : Nat) (before after : State Symbol EnumGuard) (value : EnumerationState.UVarValue Symbol)
    (valid : Valid language assignment before)
    (observed : Success (getValue uv) before value after) :
    after = before ∧ slotSatisfies assignment uv (slot language value) ∧
      ∀ node scs, value = .unenumerated node scs → node = none ∧ scs = [] := by
  have rows : ExceptT.run (getValue uv before) =
      (match before.values[FlatUnionFind.root before.representatives uv]? with
        | none => [Except.error EnumerationState.Error.invalidSlot]
        | some stored => [Except.ok (stored, before)]) := by
    simp [EnumerationFlatState.getValue, EnumerationFlatState.representative,
      EnumerationFlatState.rawValue, FlatUnionFind.find, bind, StateT.bind,
      ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.run]
    split <;> cases before <;> rfl
  change Except.ok (value, after) ∈ ExceptT.run (getValue uv before) at observed
  rw [rows] at observed
  cases stored : before.values[FlatUnionFind.root before.representatives uv]? with
  | none => simp only [stored, List.mem_singleton] at observed; cases observed
  | some current =>
      have same : value = current ∧ after = before := by
        simpa only [stored, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] using observed
      obtain ⟨valueSame, afterSame⟩ := same
      subst value after
      have assigned := valid.2.1.1 uv (FlatUnionFind.root before.representatives uv)
        (FlatUnionFind.root_root valid.1 uv).symm
      have satisfied := valid.2.1.2 (FlatUnionFind.root before.representatives uv)
      have atRoot : slotSatisfies assignment (FlatUnionFind.root before.representatives uv)
          (slot language current) := by simpa only [heap, stored, Option.getD_some] using satisfied
      refine ⟨rfl, ?_, ?_⟩
      · cases current <;> simp_all [slot, slotSatisfies]
      · intro node scs same
        exact valid.2.2 _ node scs (by simpa only [same] using stored)

private theorem fragment_sound (native : InternedConstructorTemplates.State Symbol NativeGuard)
    (language : NodeLanguage Symbol) (assignment : Nat → Term Symbol) (marker : Symbol)
    (fuel : Nat) (fragment : Fragment Symbol) (before after : State Symbol EnumGuard)
    (term : Term Symbol) (valid : Valid language assignment before)
    (observed : Success (expandFragment native marker fuel fragment) before term after) :
    after = before ∧ term = fill assignment fragment := by
  induction fuel generalizing fragment after term with
  | zero => simp [Success, expandFragment, EnumerationFlatState.failure, ExceptT.run] at observed
  | succ fuel ih =>
      cases fragment with
      | node symbol children =>
          obtain ⟨terms, middle, traversed, final⟩ := (success_bind _ _ _ _ _).mp observed
          obtain ⟨middleSame, termsSame⟩ := mapM_read (expandFragment native marker fuel)
            (fill assignment) before (fun child result next current => ih child next result current)
            children terms middle traversed
          subst middle
          obtain ⟨termSame, afterSame⟩ := (success_pure (.node symbol terms) term before after).mp final
          subst term after
          exact ⟨rfl, by simp only [fill, termsSame]⟩
      | hole uv =>
          obtain ⟨value, middle, reading, continued⟩ := (success_bind _ _ _ _ _).mp observed
          obtain ⟨middleSame, equation, free⟩ := read_sound language assignment uv before middle value valid reading
          subst middle
          cases value with
          | eliminated => simp [Success, EnumerationFlatState.failure, ExceptT.run] at continued
          | unenumerated node scs =>
              obtain ⟨rfl, rfl⟩ := free node scs rfl
              simp [Success, EnumerationFlatState.failure, ExceptT.run] at continued
          | enumerated stored =>
              obtain ⟨same, termSame⟩ := ih stored after term continued
              exact ⟨same, by simpa only [fill, slot, slotSatisfies] using termSame.trans equation⟩

private theorem root_sound (native : InternedConstructorTemplates.State Symbol NativeGuard)
    (language : NodeLanguage Symbol) (assignment : Nat → Term Symbol) (marker : Symbol)
    (fuel uv : Nat) (before after : State Symbol EnumGuard) (term : Term Symbol)
    (valid : Valid language assignment before)
    (observed : Success (expandUVar native marker fuel uv) before term after) :
    after = before ∧ term = assignment uv := by
  obtain ⟨value, middle, reading, continued⟩ := (success_bind _ _ _ _ _).mp observed
  obtain ⟨middleSame, equation, free⟩ := read_sound language assignment uv before middle value valid reading
  subst middle
  cases value with
  | eliminated => exact (List.not_mem_nil continued).elim
  | unenumerated node scs =>
      obtain ⟨rfl, rfl⟩ := free node scs rfl
      exact (List.not_mem_nil continued).elim
  | enumerated fragment =>
      obtain ⟨same, termSame⟩ := fragment_sound native language assignment marker fuel fragment
        before after term valid continued
      exact ⟨same, termSame.trans equation⟩

/-- A safe ordered original packet and checked actual rendering construct a full flat assignment. -/
theorem render_assignment (native : InternedConstructorTemplates.State Symbol NativeGuard)
    (holds : NativeGuard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (meaning : EnumGuard → Term Symbol → Prop) (marker : Symbol) (fuel uv : Nat)
    (before after : State Symbol EnumGuard) (earlier : EnumerationState.State Symbol EnumGuard)
    (term : Term Symbol) (pending : List (EnumGuard × Term Symbol))
    (related : Related before earlier) (safe : EnumerationSchedule.Safe earlier)
    (level : Nat → Nat) (frontier : Nat) (ordered : EnumerationOrder.Stratified earlier level frontier)
    (discharged : Discharged before)
    (observed : Except.ok ((term, pending), after) ∈ ExceptT.run (render native marker fuel uv before))
    (checked : ∀ obligation ∈ pending, meaning obligation.1 obligation.2) :
    ∃ assignment : Nat → Term Symbol,
      Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient native) meaning assignment before ∧
      term = assignment uv ∧ after = before ∧
      Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient native) meaning assignment after := by
  let language := SourcePruningEnumerationNativeLanguage.handles holds ambient native
  have oldDischarged : SourcePruningEnumerationRendering.Discharged earlier := by
    intro held node scs stored
    exact discharged held node scs (by simpa only [related.values] using stored)
  obtain ⟨assignment, equations⟩ := EnumerationAssignment.stratified_assignment earlier safe
    level frontier ordered (.node marker []) language oldDischarged
  have flatEquations := (related_satisfies related language (fun _ _ => True) assignment).mp
    ⟨equations, by simp [guardsHold]⟩
  have valid : Valid language assignment before := ⟨related.valid, flatEquations.1, discharged⟩
  obtain ⟨rendered, middle, rendering, continued⟩ := (success_bind _ _ _ _ _).mp observed
  obtain ⟨middleSame, termSame⟩ := root_sound native language assignment marker fuel uv before middle rendered valid rendering
  subst middle
  obtain ⟨current, readAfter, reading, continued⟩ := (success_bind _ _ _ _ _).mp continued
  have readSame : current = before ∧ readAfter = before := by
    simpa only [Success, get, getThe, MonadStateOf.get, StateT.get, pure, ExceptT.pure, ExceptT.mk, ExceptT.run,
      List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] using reading
  rcases readSame with ⟨currentSame, readAfterSame⟩
  subst current readAfter
  obtain ⟨obligations, guarded, traversal, final⟩ := (success_bind _ _ _ _ _).mp continued
  let action : EnumGuard × Fragment Symbol → Action Symbol EnumGuard (EnumGuard × Term Symbol) :=
    fun obligation => do pure (obligation.1, ← expandFragment native marker fuel obligation.2)
  have step : ∀ obligation result next, Success (action obligation) before result next →
      next = before ∧ result = (obligation.1, fill assignment obligation.2) := by
    intro obligation result next success
    obtain ⟨subterm, reached, rendering, final⟩ := (success_bind _ _ _ _ _).mp success
    obtain ⟨reachedSame, exactTerm⟩ := fragment_sound native language assignment marker fuel obligation.2
      before reached subterm valid rendering
    subst reached
    obtain ⟨resultSame, nextSame⟩ := (success_pure (obligation.1, subterm) result before next).mp final
    subst result next
    exact ⟨rfl, by simp only [exactTerm]⟩
  obtain ⟨guardedSame, pendingSame⟩ := mapM_read action
    (fun obligation => (obligation.1, fill assignment obligation.2)) before step
    before.obligations obligations guarded traversal
  subst guarded
  obtain ⟨pairSame, afterSame⟩ := (success_pure (rendered, obligations) (term, pending) before after).mp final
  have termEq := congrArg Prod.fst pairSame
  have pendingEq := congrArg Prod.snd pairSame
  dsimp only at termEq pendingEq
  subst term pending after
  have satisfies : Satisfies language meaning assignment before := by
    refine ⟨flatEquations.1, ?_⟩
    intro obligation member
    apply checked (obligation.1, fill assignment obligation.2)
    rw [pendingSame]
    exact List.mem_map.mpr ⟨obligation, member, rfl⟩
  exact ⟨assignment, satisfies, termSame, rfl, satisfies⟩

end MicroCFTA.SourceFlatPruningRendering
