import MicroCFTA.SourceCurrentIncomingReachedReadRealized
import MicroCFTA.SourceCurrentIncomingReadStorage
import MicroCFTA.SourcePruningEnumerationRecursivePacket

/-! Actual successful incoming calls derive validity for their literal native writer input frame. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentIncomingReadFrame
open EnumerationState EnumerationSchedule InternedConstructorTemplates
open SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationNativeBranchCompletion (CacheValid)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable {bits : Nat}

/-- Original cache and caller facts derive validity of the actual reached read frame. -/
theorem incoming_ok_frame_valid (symbolEquality : DecidableEq Symbol)
    (edgeEquality : DecidableEq (EdgeKey Symbol Constraint)) (nodeEquality : DecidableEq Node)
    (profile : Profile) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller (bits + 2)) (before : Cached) (memos : Memos)
    (checkEmpty : Bool) (r n p h target : Nat) (incoming : Node) (scs : List Suspended)
    (inside : target < before.core.counter) :
    letI : DecidableEq Symbol := symbolEquality
    letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
    letI : DecidableEq Node := nodeEquality
    Context formulas solver inventory caller memos → CacheValid caller before →
    InternedProbeProvenance.Available caller.checked.native.machine.heap incoming → incoming.free = [] →
    Fits profile caller.checked → Room bits profile →
    let actual := SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
      caller before.core target incoming scs memos.query
    match actual.1 with
    | .ok _ => ∃ next final, Post formulas solver next caller actual.2.1 final ∧
        final.query = actual.2.2.1 ∧
        CacheValid actual.2.1 (EnumerationExpandableIndex.frame actual.2.2.2 before)
    | .error _ => True := by
  letI : DecidableEq Symbol := symbolEquality
  letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
  letI : DecidableEq Node := nodeEquality
  intro initial valid available closed fits room
  obtain ⟨roots, paths, storage, realized, _counts, _flags⟩ := valid
  have callerFacts := SourceCurrentIncomingReachedReadRealized.incoming_ok_read_realized
    symbolEquality edgeEquality nodeEquality profile formulas solver inventory caller before.core memos
    checkEmpty r n p h target incoming scs roots paths initial realized available closed fits room
  have readStorage := SourceCurrentIncomingReadStorage.incoming_read_storage symbolEquality edgeEquality
    nodeEquality checkEmpty r n p h caller before.core target incoming scs memos storage inside
  change (let actual := SourcePruningEnumerationIncomingNode.run checkEmpty r n p h caller before.core target incoming scs memos.query;
    match actual.1 with
    | .ok _ => ∃ next final, Post formulas solver next caller actual.2.1 final ∧
        final.query = actual.2.2.1 ∧
        PendingRealized actual.2.1.checked.native.machine.heap actual.2.2.2
    | .error _ => True) at callerFacts
  dsimp only at callerFacts readStorage ⊢
  generalize observed : SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
    caller before.core target incoming scs memos.query = actual at callerFacts readStorage ⊢
  rcases actual with ⟨result, reached, savedQueries, read⟩
  cases result with
  | error fault => trivial
  | ok output =>
      obtain ⟨next, final, post, querySame, readRealized⟩ := callerFacts
      have retained := SourcePruningEnumerationNativeBranchCompletion.cacheValid_post
        caller reached before ⟨roots, paths, storage, realized, _counts, _flags⟩ post
      obtain ⟨retainedRoots, retainedPaths, _retainedStorage, _retainedRealized, retainedCounts, retainedFlags⟩ := retained
      have readFacts := SourceCurrentIncomingReadRoots.incoming_read_roots symbolEquality edgeEquality
        nodeEquality checkEmpty r n p h caller before.core target incoming scs memos retainedRoots retainedPaths
      dsimp only at readFacts
      rw [observed] at readFacts
      dsimp only at readFacts
      refine ⟨next, final, post, querySame, retainedRoots, ?_, ?_, ?_, ?_, ?_⟩
      · exact readFacts.1
      · exact readStorage
      · exact readRealized
      · simpa only [EnumerationExpandableIndex.frame, readFacts.2.1] using retainedCounts
      · simpa only [EnumerationExpandableIndex.frame, readFacts.2.1] using retainedFlags

end MicroCFTA.SourceCurrentIncomingReadFrame
