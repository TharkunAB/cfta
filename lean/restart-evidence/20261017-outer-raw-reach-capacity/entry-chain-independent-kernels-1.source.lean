import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterResourceEntryReach

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200

namespace MicroCFTA.ResourceEntryIndependentKernels
open InternedConstructorTemplates
open SourceCurrentAllocatedPartialState (EdgeRequest)
open SourceCurrentAllocatedPartialGraph (EdgeBody)
open SourceCurrentAllocatedPartialSourceReads (EdgeBodyReads)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentAllocatedFiniteOrdinaryOuterEntries (Entry Reach)
open SourceCurrentAllocatedFiniteOrdinaryOuterResourceEntryDefs (Admitted)
open SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeState (Stored)
open SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeReturned (EdgeCertificate)
open SourceCurrentAllocatedFiniteOrdinaryActualOuterWork (WorkBounds)
open SourceCurrentAllocatedFiniteOrdinaryOuterResourceDefs (Headroom)
open SourceCurrentAllocatedFiniteOrdinaryParentUniformBudgets (nodeBudget edgeBudget)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

theorem arbitrary_raw_reached_parent {bits budget : Nat}
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {root : Entry (bits + 2)} (initial : Admitted bits formulas solver root)
    {request : EdgeRequest} {before after : Caller (bits + 2)} {result : EdgeValue Symbol Guard}
    (reached : Reach budget root (.edgeBody request before))
    (actual : EdgeBody budget request before result after) :
    ∃ (memos final : Memos), EdgeBodyReads formulas solver actual memos final ∧
      ∃ next, Post formulas solver next before after final ∧ Stored after ∧ EdgeCertificate request result ∧
        ∃ (rows arity bound : Nat) (limits : SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.Limits),
          WorkBounds before.checked.native.machine.heap after.checked.native.machine.heap
            (nodeBudget limits rows arity bound) (edgeBudget limits rows arity bound) ∧
          Headroom bits after.checked.native.machine.heap 0 0 := by
  have admitted := SourceCurrentAllocatedFiniteOrdinaryOuterResourceEntryReach.reach bits formulas solver reached initial
  have capacity := SourceCurrentAllocatedFiniteOrdinaryOuterResourceEntryReach.numeric_plan
    bits formulas solver (budget := budget) initial request before reached
  obtain ⟨inventory, memos, rows, arity, bound, limits, context, stored, inherited,
    resident, domain, profile, guards, heightBound, room, _active⟩ := admitted
  obtain ⟨final, reads⟩ := SourceCurrentAllocatedFiniteOrdinaryOuterParentReads.edge_body bits formulas solver actual
    inventory context inherited resident domain stored.structural capacity
  obtain ⟨_checks, next, post, _resident, _stored, _narrow, _law⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterVerification.edge_body formulas solver reads inventory context inherited
      resident domain stored.structural
  have produced := SourceCurrentAllocatedFiniteOrdinaryOuterEdgeShapes.edge_body formulas solver reads inventory
    context inherited resident domain stored
  have work := SourceCurrentAllocatedFiniteOrdinaryActualParentWork.edge_body formulas solver reads inventory
    context inherited resident stored limits rows arity bound guards profile heightBound
  have finalRoom : Headroom bits after.checked.native.machine.heap 0 0 :=
    (room.mono (by omega) (by omega)).after work
  exact ⟨memos, final, reads, next, post, produced.1, produced.2.2,
    rows, arity, bound, limits, work, finalRoom⟩

#print axioms arbitrary_raw_reached_parent
#check @arbitrary_raw_reached_parent

end MicroCFTA.ResourceEntryIndependentKernels
