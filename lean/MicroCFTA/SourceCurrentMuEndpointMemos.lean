import MicroCFTA.SourceCurrentMuEndpoint

/-!
# Actual memo calls at the new closed Mu endpoint

The constrained branch first reads the unconstrained predicate memo.
It does not call the descendant memo or the global unfolding memo.
The receipts retain completed entries. They do not model lazy publication,
concurrent cache access, or demand on earlier Haskell producer thunks.
-/
namespace MicroCFTA.SourceCurrentMuEndpointMemos
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open SourceObservations SourceSymbolicIndex EqualityNormalize
open InternedFreshOrdinaryMemoGateTrace (Ready)
open EndpointMemoGateTrace (Memos Valid Keeps)
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source

/-- Execute the predicate call before returning the mode at a constrained closed Mu. -/
noncomputable def closedMu (belowEnd : Bool) (entry : Interned InternedBinderProtocol.NodeKey)
    (body depth ordinary : Value Symbol Guard) (memos : Memos) : Bool × Memos :=
  let actual := SourceUnconstrainedMemo.run (.mu entry body depth ordinary) memos.query.predicate
  (if actual.1 then false else belowEnd,
    {memos with query := {memos.query with predicate := actual.2}})

/-- The closed Mu receipt records the actual predicate hit or miss and returned tables. -/
inductive ClosedMuRead (belowEnd : Bool) (entry : Interned InternedBinderProtocol.NodeKey)
    (body depth ordinary : Value Symbol Guard) (memos : Memos) : Bool → Memos → Prop where
  | done (closed : (Value.mu entry body depth ordinary).free = [])
      (called : SourceUnconstrainedMemo.run (.mu entry body depth ordinary) memos.query.predicate = (plain, savedPredicate)) :
      ClosedMuRead belowEnd entry body depth ordinary memos (if plain then false else belowEnd)
        {memos with query := {memos.query with predicate := savedPredicate}}

/-- Every closed Mu endpoint has its actual completed predicate-call receipt. -/
theorem closedMu_read (belowEnd : Bool) (entry : Interned InternedBinderProtocol.NodeKey)
    (body depth ordinary : Value Symbol Guard) (memos : Memos)
    (closed : (Value.mu entry body depth ordinary).free = []) :
    ClosedMuRead belowEnd entry body depth ordinary memos
      (closedMu belowEnd entry body depth ordinary memos).1 (closedMu belowEnd entry body depth ordinary memos).2 :=
  .done closed rfl

/-- The new branch derives its exact worker result and all three returned memo invariants. -/
theorem closedMu_checked [DecidableEq (EdgeKey Symbol Guard)]
    (belowEnd : Bool) (fuel : Nat) (entry : Interned InternedBinderProtocol.NodeKey)
    (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (closed : (Value.mu entry body depth ordinary).free = [])
    (ready : Ready state) (available : Available state (.mu entry body depth ordinary))
    (memos : Memos) (valid : Valid state memos) :
    ClosedMuRead belowEnd entry body depth ordinary memos
      (closedMu belowEnd entry body depth ordinary memos).1 (closedMu belowEnd entry body depth ordinary memos).2 ∧
    SourceCurrentMuEndpoint.nodeMeets belowEnd source reaches (fuel + 1) [] (.mu entry body depth ordinary) state =
      .done (some (closedMu belowEnd entry body depth ordinary memos).1) state ∧
    Keeps state state (closedMu belowEnd entry body depth ordinary memos).2 ∧
    (closedMu belowEnd entry body depth ordinary memos).2.unfolding = memos.unfolding ∧
    (closedMu belowEnd entry body depth ordinary memos).2.query.descendants = memos.query.descendants ∧
    SourceEndpointMemo.Keeps memos.query (closedMu belowEnd entry body depth ordinary memos).2.query := by
  have actual := SourceUnconstrainedMemo.run_exact (.mu entry body depth ordinary) state
    ready.1.normal.facts.coherent available memos.query.predicate valid.query.predicate
  have worker := SourceCurrentMuEndpoint.closed_mu belowEnd source reaches fuel entry body depth ordinary state closed
  rw [← actual.1] at worker
  refine ⟨closedMu_read belowEnd entry body depth ordinary memos closed, ?_, ?_, rfl, rfl, ?_⟩
  · simpa only [closedMu] using worker
  · exact ⟨ready, ⟨valid.unfolding, ⟨valid.query.descendants, actual.2⟩⟩, grows_refl _, extends_refl _⟩
  · exact ⟨extends_refl _, SourceEndpointMemo.predicate_extends _ _⟩

/-- Current completed primary scans retain the existing exact three-family memo receipts. -/
theorem primary_completed_class [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (values : List (Value Symbol Guard)) (paths : Class) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard)
    (actual : SourceCurrentMuEndpoint.classMeets true source reaches fuel values paths state = .done (some answer) final)
    (ready : Ready state) (available : ∀ value ∈ values, Available state value)
    (memos : Memos) (valid : Valid state memos) :
    ∃ trace : EndpointStatefulGateTrace.ClassTrace source reaches values paths state answer final,
      ∃ saved, EndpointMemoGateTrace.ClassReads trace memos saved ∧ Keeps state final saved := by
  rw [SourceCurrentMuEndpoint.primary_class] at actual
  exact EndpointMemoGateTrace.completed_class fuel values paths state answer final actual ready available memos valid

end MicroCFTA.SourceCurrentMuEndpointMemos
