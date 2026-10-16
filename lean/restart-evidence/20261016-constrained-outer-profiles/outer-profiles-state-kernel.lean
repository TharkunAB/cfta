import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterState
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterVerification
import MicroCFTA.SourceCurrentAllocatedPartialInitialization
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
variable {width budget : Nat}
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "ReturnedStored" => SourceCurrentAllocatedFiniteOrdinaryReturned.Stored

/-- The same outer state retains native output and Merge profiles with its structural certificates. -/
structure Stored (state : Caller width) : Prop where
  /-- Native cells retain their captured domain and height laws. -/
  native : NativeStored state.checked.native
  /-- Native cells retain their conditional output profiles. -/
  output : OutputStored state.checked.native
  /-- Completed Merge entries retain their captured output profiles. -/
  profiles : Profiles state.merge
  /-- Outer cells retain their captured domain and height laws. -/
  returned : ReturnedStored state

/-- Strong lower stores derive the existing structural outer invariant. -/
theorem Stored.structural {state : Caller width} (stored : Stored state) :
    SourceCurrentAllocatedFiniteOrdinaryOuterState.Stored state :=
  ⟨stored.native, stored.profiles.domain, stored.returned⟩

/-- Fresh outer tables retain the supplied actual lower certificates. -/
theorem initial (checked : SourceEqualityNativeDemand.State width)
    (memo : SourceCurrentMemoMergeGraph.Memo Symbol Guard) (fourth : SourceCurrentEmptinessMemo.Memo)
    (native : NativeStored checked.native) (output : OutputStored checked.native) (profiles : Profiles memo) :
    Stored (SourceCurrentAllocatedPartialState.initial checked memo fourth) :=
  ⟨native, output, profiles, SourceCurrentAllocatedFiniteOrdinaryReturned.initial checked memo fourth⟩

/-- Literal logical initialization derives strong stores over the actual retained constructor heap. -/
theorem caller_stored (width : Nat) (cache : Cache.State SourceEqualityPartialConstraintKey.Key)
    (heap : InternedConstructorTemplates.State Symbol Guard) :
    Stored (SourceCurrentAllocatedPartialInitialization.caller width cache heap) :=
  initial _ _ _
    (SourceCurrentAllocatedFiniteOrdinaryStored.initial_stored width ⟨heap, Cache.emptyState⟩)
    (SourceCurrentAllocatedFiniteOrdinaryOutputStored.initial_stored width ⟨heap, Cache.emptyState⟩)
    SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.empty_stored

/-- An actual lower return retains outer cells and replaces the proved lower certificates. -/
theorem Stored.advance {before : Caller width} (stored : Stored before)
    (checked : SourceEqualityNativeDemand.State width) (fourth : SourceCurrentEmptinessMemo.Memo)
    (memo : SourceCurrentMemoMergeGraph.Memo Symbol Guard) (native : NativeStored checked.native)
    (output : OutputStored checked.native) (profiles : Profiles memo) :
    Stored (SourceCurrentAllocatedPartialState.advance before checked fourth memo) :=
  ⟨native, output, profiles, stored.returned.advance checked fourth memo⟩

/-- Constructor and equality-operation advances retain both lower certificate tables. -/
theorem Stored.advancePhysical {before : Caller width} (stored : Stored before)
    (physical : SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula) :
    Stored (SourceCurrentAllocatedPartialState.advance before (SourceCurrentAllocatedQueryMemo.advancePhysical before.checked physical)
      before.fourth before.merge) :=
  stored.advance _ _ _ (SourceCurrentAllocatedFiniteOrdinaryStored.advance_stored _ _ stored.native)
    (SourceCurrentAllocatedFiniteOrdinaryOutputStored.advance_stored _ _ stored.output) stored.profiles

/-- Node publication and demand create no completed lower result. -/
theorem Stored.beginNode {before : Caller width} (stored : Stored before) (request : NodeRequest) :
    Stored (beginNode request before).2.2 :=
  ⟨stored.native, stored.output, stored.profiles, stored.returned.beginNode request⟩

/-- Edge publication and demand retain both lower result families. -/
theorem Stored.beginEdge {before : Caller width} (stored : Stored before) (request : EdgeRequest) :
    Stored (beginEdge request before).2.2 :=
  ⟨stored.native, stored.output, stored.profiles, stored.returned.beginEdge request⟩

/-- Node finish installs its actual owner law and retains the same lower certificates. -/
theorem Stored.finishNode {before : Caller width} (stored : Stored before)
    {handle : Nat} {owner : NodeRequest} (result : Node)
    (running : before.nodeResults.cells handle = some ⟨owner, .evaluating⟩)
    (law : DNode owner.value → NodeNarrow owner.value result) : Stored (finishNode handle result before) :=
  ⟨stored.native, stored.output, stored.profiles, stored.returned.finishNode result running law⟩

/-- Edge finish installs its actual owner law and retains the same lower certificates. -/
theorem Stored.finishEdge {before : Caller width} (stored : Stored before)
    {handle : Nat} {owner : EdgeRequest} (result : Edge)
    (running : before.edgeResults.cells handle = some ⟨owner, .evaluating⟩)
    (law : DEdge owner.value → EdgeNarrow owner.value result) : Stored (finishEdge handle result before) :=
  ⟨stored.native, stored.output, stored.profiles, stored.returned.finishEdge result running law⟩

variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)


end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterProfiles
