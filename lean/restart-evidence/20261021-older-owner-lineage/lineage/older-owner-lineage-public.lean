import MicroCFTA.SourceCurrentActualChildRank
import MicroCFTA.SourceCurrentOuterOwnerPrefix
import MicroCFTA.SourceCurrentOuterInitialPrefix
import MicroCFTA.SourceCurrentAllocatedPartialCallSteps

namespace MicroCFTA.SourceCurrentOlderOwnerLineage
open Cache InternedConstructorTemplates
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialWorker
open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentOuterExecutionAncestry (Step Reached)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "caller" => SourceCurrentOuterActiveAncestry.caller
local notation "descend" => SourceCurrentAllocatedPartialGraph.descend

private def phaseFuel : Phase width → Nat
  | .node fuel .. | .body fuel .. | .rows fuel .. | .descendants fuel .. |
      .children fuel .. | .walk fuel .. => fuel

private theorem lex_trans {first middle last : Nat × Nat}
    (left : Prod.Lex Nat.lt Nat.lt first middle) (right : Prod.Lex Nat.lt Nat.lt middle last) :
    Prod.Lex Nat.lt Nat.lt first last := by
  cases left with
  | left _ _ smaller =>
      cases right with
      | left _ _ larger => exact .left _ _ (Nat.lt_trans smaller larger)
      | right _ _ => exact .left _ _ smaller
  | right _ smaller =>
      cases right with
      | left _ _ larger => exact .left _ _ larger
      | right _ larger => exact .right _ (Nat.lt_trans smaller larger)

private theorem same_request [DecidableEq (EdgeKey Symbol Guard)]
    {bits : Nat} {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {before : Caller (bits + 2)} {memos : Memos}
    (initial : Context formulas solver inventory before memos) (first second : NodeRequest)
    (left : SourceCurrentOuterPrefixInvariants.NodeReady before first)
    (right : SourceCurrentOuterPrefixInvariants.NodeReady before second) (same : first.key = second.key) :
    first = second := by
  have inherited := SourceEqualityConstraintMemoAllocation.ready_eq_of_identity _
    initial.ready.good.operations.constraints first.inherited second.inherited left.1 right.1 (congrArg Prod.fst same)
  have values := InternedFreshProbeKeys.resident_reference_injective _
    initial.ready.semantic.ready.semantic.1.normal.facts.coherent first.value second.value
    left.2.resident right.2.resident (congrArg Prod.snd same)
  cases first
  cases second
  cases inherited
  cases values
  rfl

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
variable {width bits g s r e p h m c n budget : Nat}

private theorem step_fuel {first last : Phase width}
    (actual : Step g s r e p h m c n budget first last) : phaseFuel last ≤ phaseFuel first := by
  cases actual <;> simp only [phaseFuel] <;> omega

private theorem reached_fuel {first last : Phase width}
    (actual : Reached g s r e p h m c n budget first last) : phaseFuel last ≤ phaseFuel first := by
  induction actual with
  | refl => exact Nat.le_refl _
  | snoc earlier last ih => exact Nat.le_trans (step_fuel last) ih

private theorem head_cases {first last : Phase width}
    (actual : Reached g s r e p h m c n budget first last) :
    first = last ∨ ∃ middle, Step g s r e p h m c n budget first middle ∧
      Reached g s r e p h m c n budget middle last := by
  induction actual with
  | refl => exact Or.inl rfl
  | snoc earlier step ih =>
      rcases ih with same | ⟨middle,head,tail⟩
      · cases same
        exact Or.inr ⟨_,step,.refl _⟩
      · exact Or.inr ⟨middle,head,tail.snoc step⟩

private theorem body_ordinary {ownerFuel candidateFuel : Nat} {owner candidate : NodeRequest}
    {running current : Caller width}
    (inside : Reached g s r e p h m c n budget (.body ownerFuel owner running)
      (.node candidateFuel candidate current)) :
    ∃ entry rows depth free, owner.value = .node entry rows depth free := by
  rcases head_cases inside with same | ⟨middle,step,remaining⟩
  · cases same
  · cases step with
    | body_rows ordinary => exact ⟨_,_,_,_,ordinary⟩

theorem body_rank_lt
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {g s r e p h m c n budget ownerFuel candidateFuel : Nat}
    {first : Phase (bits + 2)} {inventory : Inventory} {memos : Memos}
    (seed : List Guard × Profile)
    (initial : Context formulas solver inventory (caller first) memos)
    (frame : Frame formulas solver inventory (caller first).checked)
    (fits : Fits seed.2 (caller first).checked)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1)
      (caller first).checked.native.machine.heap)
    (inputs : SourceCurrentOuterPrefixInvariants.Inputs first)
    (room : Room bits (SourceCurrentOuterInitialPrefix.forecast budget first seed).2)
    (normal : SourceCurrentRequiredUnionNormal.UnionNormal (caller first).checked.native.machine.heap)
    (supported : SourceCurrentNativeRequestPositivePositions.Support
      (caller first).checked.native.machine.heap (caller first).checked.native)
    (causal : SourceCurrentNativeMuPublication.History empty (caller first).checked.native.machine.heap)
    (merged : SourceCurrentConstrainedCapMemoMerge.Stored
      (fun guard : Guard => SourceMemoGate.plain guard = true) (caller first).merge)
    (positiveMemo : SourceCurrentMergePositivePosition.Support (caller first).merge)
    (origins : SourceCurrentResourceParentWriters.Origins formulas solver (caller first))
    {owner candidate : NodeRequest} {running current : Caller (bits + 2)}
    (past : Reached g s r e p h m c n budget first (.body ownerFuel owner running))
    (inside : Reached g s r e p h m c n budget (.body ownerFuel owner running)
      (.node candidateFuel candidate current)) :
    Prod.Lex Nat.lt Nat.lt
      (SourceCurrentPositiveQuotientCount.count (candidate.inherited.payload.getD []) candidate.value,
        InternedValueMass.value candidate.value)
      (SourceCurrentPositiveQuotientCount.count (owner.inherited.payload.getD []) owner.value,
        InternedValueMass.value owner.value)
 := by
  induction ownerFuel using Nat.strongRecOn generalizing candidateFuel owner candidate running current with
  | ind ownerFuel ih =>
      rcases owner with ⟨inherited,ownerValue⟩
      obtain ⟨ownerEntry,ownerRows,ownerDepth,ownerFree,ordinary⟩ := body_ordinary inside
      change ownerValue = .node ownerEntry ownerRows ownerDepth ownerFree at ordinary
      subst ownerValue
      obtain ⟨skipped,original,parented,rest,rowBefore,afterParent,start,slot,childFuel,combined,
          earlier,child,split,cut,parent,combinedAt,live,previous,selected,tail⟩ :=
        SourceCurrentOuterOwnerPrefix.first_child inside
      have member : original ∈ ownerRows := by
        rw [split]
        exact List.mem_append.mpr (.inr List.mem_cons_self)
      obtain ⟨childReached,childRank⟩ :=
        SourceCurrentActualChildRank.dispatch formulas solver
          (ownerEntry := ownerEntry) (ownerDepth := ownerDepth) (ownerFree := ownerFree)
          seed initial frame fits known inputs room normal supported causal merged positiveMemo origins
          (past.trans cut) member parent combinedAt live previous selected
      rcases tail with direct | ⟨handle,captured,activated,started,remaining⟩
      · cases direct
        exact childRank
      · have bound := reached_fuel cut
        change childFuel + slot + 2 ≤ ownerFuel at bound
        have smaller : childFuel < ownerFuel := by omega
        let request : NodeRequest := ⟨(descend start combined slot).1,child⟩
        let before := (descend start combined slot).2
        obtain ⟨next,final,currentSeed,_trace,post,_frame,_fits,_known,currentInputs,
            _below,_alphabet,_room,_bounds,_carrier,_need⟩ :=
          SourceCurrentOuterInitialPrefix.reached formulas solver seed childReached initial frame fits known inputs room
        have ready : SourceCurrentOuterPrefixInvariants.NodeReady before request := currentInputs
        obtain ⟨activatedContext,capturedGood,key,_cell⟩ :=
          SourceCurrentAllocatedPartialCallSteps.node_start formulas solver post.context ready.1 ready.2 started
        have checked := (beginNode_components request before).1
        rw [started] at checked
        dsimp only at checked
        have requested : SourceCurrentOuterPrefixInvariants.NodeReady activated request := by
          simpa only [SourceCurrentOuterPrefixInvariants.NodeReady,checked] using ready
        have capturedReady : SourceCurrentOuterPrefixInvariants.NodeReady activated captured :=
          ⟨capturedGood.inherited,capturedGood.input⟩
        have same := same_request activatedContext captured request capturedReady requested key
        have activationPast : Reached g s r e p h m c n budget first (.body childFuel captured activated) :=
          childReached.snoc (.node_evaluate started)
        have deeper := ih childFuel smaller (candidateFuel := candidateFuel) (owner := captured)
          (candidate := candidate) (running := activated) (current := current) activationPast remaining
        rw [same] at deeper
        exact lex_trans deeper childRank

end MicroCFTA.SourceCurrentOlderOwnerLineage

set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.SourceCurrentOlderOwnerLineage.body_rank_lt
#print MicroCFTA.SourceCurrentOlderOwnerLineage.body_rank_lt
#print axioms MicroCFTA.SourceCurrentOlderOwnerLineage.body_rank_lt
