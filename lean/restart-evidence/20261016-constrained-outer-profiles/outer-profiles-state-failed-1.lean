import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterState
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterVerification
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOutputStored
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache
import MicroCFTA.SourceCurrentAllocatedPartialActual

/-!
# Strong lower profile stores through all actual outer families

The induction follows each supplied strict read graph in source order.
Parent reads produce the lower certificates before their actual return.
Raw rebuilds and equality prefixes retain the same native result tables.
Warm outer hits transport their exact captured owner's structural law.
The public endpoints derive their own reached checks from actual reads.
These results verify completed graphs. They assert no graph existence,
outer numeric output profile, hereditary guard bound, or root capacity.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterProfiles
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedPartialChecks SourceCurrentAllocatedPartialSourceReads
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow EdgeNarrow)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Resident" => InternedEdgeResidency.EdgeResident
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "DEdge" => SourceCurrentAllocatedFiniteOrdinaryDomain.Edge
local notation "DRows" => SourceCurrentAllocatedFiniteOrdinaryDomain.Rows
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width budget : Nat}
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "ReturnedStored" => SourceCurrentAllocatedFiniteOrdinaryReturned.Stored

/-- The same outer state retains native output and Merge profiles with its structural certificates. -/
structure Stored (state : Caller width) : Prop where
  native : NativeStored state.checked.native
  output : OutputStored state.checked.native
  profiles : Profiles state.merge
  returned : ReturnedStored state

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] in
/-- Strong lower stores derive the existing structural outer invariant. -/
def Stored.structural {state : Caller width} (stored : Stored state) :
    SourceCurrentAllocatedFiniteOrdinaryOuterState.Stored state :=
  ⟨stored.native, stored.profiles.domain, stored.returned⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] in
/-- Fresh outer tables retain the supplied actual lower certificates. -/
theorem initial (checked : SourceEqualityNativeDemand.State width)
    (memo : SourceCurrentMemoMergeGraph.Memo Symbol Guard) (fourth : SourceCurrentEmptinessMemo.Memo)
    (native : NativeStored checked.native) (output : OutputStored checked.native) (profiles : Profiles memo) :
    Stored (SourceCurrentAllocatedPartialState.initial checked memo fourth) :=
  ⟨native, output, profiles, SourceCurrentAllocatedFiniteOrdinaryReturned.initial checked memo fourth⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] in
/-- An actual lower return retains outer cells and replaces the proved lower certificates. -/
theorem Stored.advance {before : Caller width} (stored : Stored before)
    (checked : SourceEqualityNativeDemand.State width) (fourth : SourceCurrentEmptinessMemo.Memo)
    (memo : SourceCurrentMemoMergeGraph.Memo Symbol Guard) (native : NativeStored checked.native)
    (output : OutputStored checked.native) (profiles : Profiles memo) :
    Stored (advance before checked fourth memo) :=
  ⟨native, output, profiles, stored.returned.advance checked fourth memo⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] in
/-- Constructor and equality-operation advances retain both lower certificate tables. -/
theorem Stored.advancePhysical {before : Caller width} (stored : Stored before)
    (physical : SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula) :
    Stored (advance before (SourceCurrentAllocatedQueryMemo.advancePhysical before.checked physical)
      before.fourth before.merge) :=
  stored.advance _ _ _ (SourceCurrentAllocatedFiniteOrdinaryStored.advance_stored _ _ stored.native)
    (SourceCurrentAllocatedFiniteOrdinaryOutputStored.advance_stored _ _ stored.output) stored.profiles

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] in
/-- Node publication and demand create no completed lower result. -/
theorem Stored.beginNode {before : Caller width} (stored : Stored before) (request : NodeRequest) :
    Stored (beginNode request before).2.2 :=
  ⟨stored.native, stored.output, stored.profiles, stored.returned.beginNode request⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] in
/-- Edge publication and demand retain both lower result families. -/
theorem Stored.beginEdge {before : Caller width} (stored : Stored before) (request : EdgeRequest) :
    Stored (beginEdge request before).2.2 :=
  ⟨stored.native, stored.output, stored.profiles, stored.returned.beginEdge request⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] in
/-- Node finish installs its actual owner law and retains the same lower certificates. -/
theorem Stored.finishNode {before : Caller width} (stored : Stored before)
    {handle : Nat} {owner : NodeRequest} (result : Node)
    (running : before.nodeResults.cells handle = some ⟨owner, .evaluating⟩)
    (law : DNode owner.value → NodeNarrow owner.value result) : Stored (finishNode handle result before) :=
  ⟨stored.native, stored.output, stored.profiles, stored.returned.finishNode result running law⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] in
/-- Edge finish installs its actual owner law and retains the same lower certificates. -/
theorem Stored.finishEdge {before : Caller width} (stored : Stored before)
    {handle : Nat} {owner : EdgeRequest} (result : Edge)
    (running : before.edgeResults.cells handle = some ⟨owner, .evaluating⟩)
    (law : DEdge owner.value → EdgeNarrow owner.value result) : Stored (finishEdge handle result before) :=
  ⟨stored.native, stored.output, stored.profiles, stored.returned.finishEdge result running law⟩

variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)


end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterProfiles
