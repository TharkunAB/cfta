import MicroCFTA.SourceCurrentAllocatedNativeStoredIncoming
import MicroCFTA.SourcePruningEnumerationIncomingCacheAdapter

/-!
# Native structural certificates through the actual incoming cache adapter

The adapter retains the complete observed caller before it attaches an index candidate.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeStoredIncomingCacheAdapter
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceCurrentAllocatedFiniteOrdinaryStored (Stored)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- The actual cache adapter retains native certificates at every returned observation. -/
theorem incoming_cache_adapter_stored (profile : Profile) (checkEmpty : Bool)
    (representativeFuel nativeFuel p h indexFuel : Nat)
    (beforeCaller : Caller (bits + 2)) (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (target : Nat) (incoming : Node) (incomingScs : List EnumerationState.Suspended) (queries : Queries)
    (ready : SourceCurrentConjunctionClassScan.Ready beforeCaller.checked)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (available : Available beforeCaller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (fits : Fits profile beforeCaller.checked) (room : Room bits profile)
    (stored : Stored beforeCaller.checked.native) :
    Stored (SourcePruningEnumerationIncomingCacheAdapter.run checkEmpty representativeFuel nativeFuel p h indexFuel
      beforeCaller before target incoming incomingScs queries).1.2.1.checked.native := by
  change Stored (SourcePruningEnumerationIncomingNode.run checkEmpty representativeFuel nativeFuel p h
    beforeCaller before.core target incoming incomingScs queries).2.1.checked.native
  exact SourceCurrentAllocatedNativeStoredIncoming.incoming_run_stored profile checkEmpty
    representativeFuel nativeFuel p h beforeCaller before.core target incoming incomingScs queries
    ready realized available closed fits room stored

end MicroCFTA.SourceCurrentAllocatedNativeStoredIncomingCacheAdapter
