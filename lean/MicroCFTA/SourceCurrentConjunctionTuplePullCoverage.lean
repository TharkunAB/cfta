import MicroCFTA.SourceCurrentConjunctionTuplePullTotal
import MicroCFTA.SourceCurrentConjunctionTuplePullDriveEffects
import MicroCFTA.SourceCurrentConjunctionCompletionReads

/-!
# Accepted terms in completed physical tuple samples

The residual predicate follows the actual suspended cursor. A common term
either has an accepted tuple in the collected sample or remains possible
in that cursor. A completed stream cannot discard this alternative.
Only an actual demanded singleton read invokes the read acceptance law.
The final theorem takes no future view or read agreement certificate.
-/
namespace MicroCFTA.SourceCurrentConjunctionTuplePullCoverage
open Language InternedConstructorTemplates
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionRowsWorker (Outcome)
open SourceCurrentConjunctionTuplePull (step expose start)
open SourceCurrentConjunctionTuplePullEffects (Inputs)
open InternedGuardedLanguage (meaning)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol FullSyntax.Formula
local notation "Cursor" => SourceCurrentConjunctionTuplePull.Cursor Symbol FullSyntax.Formula
local notation "Event" => SourceCurrentConjunctionTuplePull.Event Symbol FullSyntax.Formula
local notation "Relation" => Node → Term Symbol → Prop

/-- The original common term is accepted by every member of a nonempty tuple. -/
def TupleAccepted (relation : Relation) (term : Term Symbol) (tuple : List Edge) : Prop :=
  tuple ≠ [] ∧ ∀ edge ∈ tuple, SourceCurrentConjunctionEmptinessRows.EdgeAccepts relation
    (SourceCurrentConjunctionCompletionReads.edgeView edge) term

private def RowAccepted (relation : Relation) (term : Term Symbol) (edge : Edge) : Prop :=
  SourceCurrentConjunctionEmptinessRows.EdgeAccepts relation
    (SourceCurrentConjunctionCompletionReads.edgeView edge) term

/-- Residual acceptance includes the current scan and its future inner tuples. -/
def Residual (relation : Relation) (term : Term Symbol) : Cursor → Prop
  | .empty => False
  | .seed node => relation node term
  | .seedRows rows => ∃ edge ∈ rows, RowAccepted relation term edge
  | .extend node inner => relation node term ∧ Residual relation term inner
  | .readOperand node inner tuple =>
      (TupleAccepted relation term tuple ∧ relation node term) ∨
        (relation node term ∧ Residual relation term inner)
  | .scanOperand node inner tuple remaining =>
      (TupleAccepted relation term tuple ∧ ∃ edge ∈ remaining, RowAccepted relation term edge) ∨
        (relation node term ∧ Residual relation term inner)

private def ClosedOperands : Cursor → Prop
  | .empty | .seedRows _ => True
  | .seed node => node.free = []
  | .extend node inner | .readOperand node inner _ | .scanOperand node inner _ _ =>
      node.free = [] ∧ ClosedOperands inner

private theorem next_closed {cursor next : Cursor}
    (actual : SourceCurrentConjunctionTuplePullProgress.Next next cursor)
    (closed : ClosedOperands cursor) : ClosedOperands next := by
  revert closed
  induction actual with
  | seed | seedTail => intro _; trivial
  | extendMore _ _ ih => intro closed; exact ⟨closed.1, ih closed.2⟩
  | extendYield _ _ _ ih => intro closed; exact ⟨closed.1, ih closed.2⟩
  | readScan | readReset | scanTail | scanReset => intro closed; exact closed

private theorem fold_closed (nodes : List Node) (cursor : Cursor) (base : ClosedOperands cursor)
    (closed : ClosedValues nodes) : ClosedOperands (nodes.foldr SourceCurrentConjunctionTuplePull.Cursor.extend cursor) := by
  revert closed
  induction nodes with
  | nil => intro _; exact base
  | cons node nodes ih =>
      intro closed
      exact ⟨closed node List.mem_cons_self, ih (fun node member => closed node (List.mem_cons_of_mem _ member))⟩

private theorem start_closed (nodes : List Node) (closed : ClosedValues nodes) : ClosedOperands (start nodes) := by
  cases nodes with
  | nil => trivial
  | cons first rest =>
      exact fold_closed rest (.seed first) (closed first List.mem_cons_self)
        (fun node member => closed node (List.mem_cons_of_mem _ member))

private theorem fold_residual (relation : Relation) (term : Term Symbol) (nodes : List Node) (cursor : Cursor)
    (base : Residual relation term cursor) (accepted : ∀ node ∈ nodes, relation node term) :
    Residual relation term (nodes.foldr SourceCurrentConjunctionTuplePull.Cursor.extend cursor) := by
  revert accepted
  induction nodes with
  | nil => intro _; exact base
  | cons node nodes ih =>
      intro accepted
      exact ⟨accepted node List.mem_cons_self, ih (fun node member => accepted node (List.mem_cons_of_mem _ member))⟩

private theorem start_residual (relation : Relation) (term : Term Symbol) (nodes : List Node)
    (accepted : SourceCurrentConjunctionEmptinessRows.Accepts relation nodes term) :
    Residual relation term (start nodes) := by
  cases nodes with
  | nil => exact False.elim (accepted.1 rfl)
  | cons first rest =>
      exact fold_residual relation term rest (.seed first) (accepted.2 first List.mem_cons_self)
        (fun node member => accepted.2 node (List.mem_cons_of_mem _ member))

private theorem accepted_shape (relation : Relation) (term : Term Symbol) (left right : Edge)
    (first : RowAccepted relation term left) (second : RowAccepted relation term right) :
    left.entry.key.symbol = right.entry.key.symbol ∧ left.children.length = right.children.length := by
  obtain ⟨leftTerms, leftShape, leftForest, _⟩ := first
  obtain ⟨rightTerms, rightShape, rightForest, _⟩ := second
  have same := Term.node.inj (leftShape.symm.trans rightShape)
  exact ⟨same.1, leftForest.length_eq.trans ((congrArg List.length same.2).trans rightForest.length_eq.symm)⟩

private theorem scan_yield (relation : Relation) (term : Term Symbol) (node : Node) (inner : Cursor)
    (first edge : Edge) (rest rows : List Edge)
    (residual : Residual relation term (.scanOperand node inner (first :: rest) (edge :: rows))) :
    TupleAccepted relation term (edge :: first :: rest) ∨
      Residual relation term (.scanOperand node inner (first :: rest) rows) := by
  rcases residual with ⟨prior, chosen, member, accepted⟩ | future
  · rcases List.mem_cons.mp member with rfl | member
    · left
      refine ⟨by simp, ?_⟩
      intro selected included
      rcases List.mem_cons.mp included with rfl | included
      · exact accepted
      · exact prior.2 selected included
    · exact Or.inr (Or.inl ⟨prior, chosen, member, accepted⟩)
  · exact Or.inr (Or.inr future)

private theorem scan_reject (relation : Relation) (term : Term Symbol) (node : Node) (inner : Cursor)
    (first edge : Edge) (rest rows : List Edge)
    (residual : Residual relation term (.scanOperand node inner (first :: rest) (edge :: rows)))
    (different : ¬(edge.entry.key.symbol = first.entry.key.symbol ∧ edge.children.length = first.children.length)) :
    Residual relation term (.scanOperand node inner (first :: rest) rows) := by
  rcases residual with ⟨prior, chosen, member, accepted⟩ | future
  · rcases List.mem_cons.mp member with same | member
    · have headAccepted : RowAccepted relation term edge := by simpa only [same] using accepted
      exact False.elim (different (accepted_shape relation term edge first headAccepted (prior.2 first List.mem_cons_self)))
    · exact Or.inl ⟨prior, chosen, member, accepted⟩
  · exact Or.inr future

private def EventResidual (relation : Relation) (term : Term Symbol) : Event → Prop
  | .more next => Residual relation term next
  | .yield tuple next => TupleAccepted relation term tuple ∨ Residual relation term next
  | .ended => False

private def Progress (relation : Relation) (term : Term Symbol) : Outcome Symbol FullSyntax.Formula Event → Prop
  | .done event _ => EventResidual relation term event
  | .failed _ _ => True

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

omit [DecidableEq Symbol] in
private theorem expose_read (h : Nat) (node : Node) (before after : Physical) (rows : List Edge)
    (actual : expose h node before = .done rows after) :
    SourceEqualityProjectionRead.Read node before.heap rows after.heap := by
  cases read : MergedFreshOrdinaryExposure.nodeEdges h node before.heap <;>
    simp only [expose, SourceCurrentConjunctionRowsWorker.exposures, read, Outcome.bind,
      List.headD_cons] at actual <;> cases actual
  exact .done h read

private theorem step_progress
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol) (h : Nat) (cursor : Cursor)
    (before : Physical) (ready : Ready before) (inputs : Inputs before.heap cursor)
    (closed : ClosedOperands cursor)
    (residual : Residual (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) term cursor) :
    Progress (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) term (step h cursor before) := by
  let relation := meaning (SourceEqualityPCSGuard.holds formulas solver) ambient
  induction cursor generalizing before with
  | empty => exact False.elim residual
  | seed node =>
      cases actual : expose h node before with
      | failed fault after => simp only [step, actual, Outcome.bind, Progress]
      | done rows after =>
          simp only [step, actual, Outcome.bind, Progress, EventResidual, Residual]
          exact SourceCurrentConjunctionCompletionReads.read_accepted (expose_read h node before after rows actual)
            ready.semantic inputs closed formulas solver ambient term residual
  | seedRows rows =>
      cases rows with
      | nil => obtain ⟨edge, member, _⟩ := residual; cases member
      | cons edge rows =>
          rcases residual with ⟨chosen, member, accepted⟩
          rcases List.mem_cons.mp member with rfl | member
          · left
            exact ⟨by simp, by intro selected included; simpa only [List.mem_singleton.mp included, RowAccepted] using accepted⟩
          · exact Or.inr ⟨chosen, member, accepted⟩
  | extend node inner ih =>
      have prior := ih before ready inputs.2 closed.2 residual.2
      cases actual : step h inner before with
      | failed fault after => simp only [step, actual, Outcome.bind, Progress]
      | done event after =>
          rw [actual] at prior
          cases event with
          | ended => exact False.elim prior
          | more next =>
              simp only [step, actual, Outcome.bind, Progress, EventResidual, Residual]
              exact ⟨residual.1, prior⟩
          | yield tuple next =>
              simp only [step, actual, Outcome.bind, Progress, EventResidual, Residual]
              rcases prior with accepted | future
              · exact Or.inl ⟨accepted, residual.1⟩
              · exact Or.inr ⟨residual.1, future⟩
  | readOperand node inner tuple _ih =>
      cases tuple with
      | nil =>
          rcases residual with ⟨impossible, _⟩ | future
          · exact False.elim (impossible.1 rfl)
          · exact future
      | cons first rest =>
          cases actual : expose h node before with
          | failed fault after => simp only [step, actual, Outcome.bind, Progress]
          | done rows after =>
              simp only [step, actual, Outcome.bind, Progress, EventResidual, Residual]
              rcases residual with ⟨prior, accepted⟩ | future
              · exact Or.inl ⟨prior, SourceCurrentConjunctionCompletionReads.read_accepted
                  (expose_read h node before after rows actual) ready.semantic inputs.1 closed.1
                  formulas solver ambient term accepted⟩
              · exact Or.inr future
  | scanOperand node inner tuple remaining _ih =>
      cases tuple with
      | nil =>
          rcases residual with ⟨impossible, _⟩ | future
          · exact False.elim (impossible.1 rfl)
          · exact future
      | cons first rest =>
          cases remaining with
          | nil =>
              rcases residual with ⟨_, edge, member, _⟩ | future
              · cases member
              · exact future
          | cons edge rows =>
              simp only [step]
              split
              · rename_i symbol
                split
                · exact scan_yield relation term node inner first edge rest rows residual
                · rename_i arity
                  exact scan_reject relation term node inner first edge rest rows residual (by
                    intro same; exact arity same.2)
              · rename_i symbol
                exact scan_reject relation term node inner first edge rest rows residual (by
                  intro same; exact symbol same.1)

private theorem step_residual
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol) (h : Nat) (cursor : Cursor)
    (before after : Physical) (event : Event) (ready : Ready before) (inputs : Inputs before.heap cursor)
    (closed : ClosedOperands cursor) (actual : step h cursor before = .done event after)
    (residual : Residual (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) term cursor) :
    EventResidual (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) term event := by
  simpa only [actual, Progress] using step_progress formulas solver ambient term h cursor before ready inputs closed residual

private def Witness (relation : Relation) (term : Term Symbol) (tuples : List (List Edge)) : Prop :=
  ∃ tuple ∈ tuples, TupleAccepted relation term tuple

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem witness_append (relation : Relation) (term : Term Symbol) (tuples : List (List Edge)) (tuple : List Edge)
    (prior : Witness relation term tuples) : Witness relation term (tuples ++ [tuple]) := by
  obtain ⟨chosen, member, accepted⟩ := prior
  exact ⟨chosen, List.mem_append.mpr (Or.inl member), accepted⟩

private theorem drive_fit
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol) (steps h budget : Nat)
    (cursor : Cursor) (collected : List (List Edge)) (before after : Physical) (tuples : List (List Edge))
    (ready : Ready before) (inputs : Inputs before.heap cursor) (closed : ClosedOperands cursor)
    (actual : SourceCurrentConjunctionTuplePullAdmission.drive steps h budget cursor collected before = .done (.fit tuples) after)
    (pending : Witness (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) term collected ∨
      Residual (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) term cursor) :
    Witness (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) term tuples := by
  let relation := meaning (SourceEqualityPCSGuard.holds formulas solver) ambient
  induction steps generalizing cursor collected before after tuples with
  | zero => cases actual
  | succ steps ih =>
      have physical := SourceCurrentConjunctionTuplePullEffects.step_effects h cursor before ready inputs
      cases observed : step h cursor before with
      | failed fault reached =>
          simp only [SourceCurrentConjunctionTuplePullAdmission.drive,
            SourceCurrentConjunctionTuplePullAdmission.advance, observed, Outcome.bind] at actual
          cases actual
      | done event reached =>
          have kept : Effects before reached := by simpa only [observed, Outcome.state] using physical.1
          have supported := physical.2 event reached observed
          cases event with
          | ended =>
              simp only [SourceCurrentConjunctionTuplePullAdmission.drive,
                SourceCurrentConjunctionTuplePullAdmission.advance, observed, Outcome.bind] at actual
              rcases pending with prior | residual
              · cases actual; exact prior
              · exact False.elim (step_residual formulas solver ambient term h cursor before reached .ended
                  ready inputs closed observed residual)
          | more next =>
              simp only [SourceCurrentConjunctionTuplePullAdmission.drive,
                SourceCurrentConjunctionTuplePullAdmission.advance, observed, Outcome.bind] at actual
              apply ih next collected reached after tuples kept.ready supported
                (next_closed (SourceCurrentConjunctionTuplePullProgress.step_next h cursor before reached (.more next) observed) closed) actual
              rcases pending with prior | residual
              · exact Or.inl prior
              · exact Or.inr (step_residual formulas solver ambient term h cursor before reached (.more next)
                  ready inputs closed observed residual)
          | yield tuple next =>
              by_cases full : budget < (collected ++ [tuple]).length
              · simp only [SourceCurrentConjunctionTuplePullAdmission.drive,
                  SourceCurrentConjunctionTuplePullAdmission.advance, observed, Outcome.bind, full, ite_true] at actual
                cases actual
              · simp only [SourceCurrentConjunctionTuplePullAdmission.drive,
                  SourceCurrentConjunctionTuplePullAdmission.advance, observed, Outcome.bind, full, ite_false] at actual
                apply ih next (collected ++ [tuple]) reached after tuples kept.ready supported.2
                  (next_closed (SourceCurrentConjunctionTuplePullProgress.step_next h cursor before reached
                    (.yield tuple next) observed) closed) actual
                rcases pending with prior | residual
                · exact Or.inl (witness_append relation term collected tuple prior)
                · rcases step_residual formulas solver ambient term h cursor before reached (.yield tuple next)
                    ready inputs closed observed residual with accepted | future
                  · exact Or.inl ⟨tuple, List.mem_append.mpr (Or.inr (List.mem_singleton_self tuple)), accepted⟩
                  · exact Or.inr future

/-- A fitting actual total sample contains a resident accepting tuple for every common input term. -/
theorem sample_fit
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol) (h budget : Nat)
    (nodes : List Node) (before after : Physical) (tuples : List (List Edge))
    (actual : SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before = .done (.fit tuples) after)
    (ready : Ready before) (available : Values before.heap nodes) (closed : ClosedValues nodes)
    (accepted : SourceCurrentConjunctionEmptinessRows.Accepts
      (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) nodes term) :
    ∃ tuple ∈ tuples, tuple ≠ [] ∧ Edges after.heap tuple ∧
      ∀ edge ∈ tuple, SourceCurrentConjunctionEmptinessRows.EdgeAccepts
        (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient)
        (SourceCurrentConjunctionCompletionReads.edgeView edge) term := by
  obtain ⟨steps, observed⟩ := SourceCurrentConjunctionTuplePullTotal.sample_observation h budget nodes before
  have done := observed 0
  simp only [Nat.add_zero, actual, SourceCurrentConjunctionTuplePullTotal.observe,
    SourceCurrentConjunctionTuplePullTotal.Result.toStatus] at done
  have witness := drive_fit formulas solver ambient term steps h budget (start nodes) [] before after tuples
    ready (SourceCurrentConjunctionTuplePullEffects.start_inputs before.heap nodes available)
    (start_closed nodes closed) done (Or.inr (start_residual _ term nodes accepted))
  obtain ⟨tuple, member, common⟩ := witness
  have physical := SourceCurrentConjunctionTuplePullDriveEffects.sample_effects steps h budget nodes before ready available
  have resident := physical.2 (.fit tuples) after done
  exact ⟨tuple, member, common.1, resident tuple member, common.2⟩

end MicroCFTA.SourceCurrentConjunctionTuplePullCoverage
