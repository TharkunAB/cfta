import MicroCFTA.SourceCurrentIncomingSomeCacheValid
import MicroCFTA.SourcePruningEnumerationRecursivePacket

/-! Actual incoming endpoints share one caller post, saved query, and captured packet. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentIncomingCapturedPost
open EnumerationState EnumerationSchedule InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationNativeBranchCompletion (CacheValid)
open SourcePruningEnumerationRecursive (Packet)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable {bits : Nat} {Typing : Type}

/-- Original packet and input facts derive both cache conclusions at the same actual successful endpoint. -/
theorem incoming_ok_captured_post (symbolEquality : DecidableEq Symbol)
    (edgeEquality : DecidableEq (EdgeKey Symbol Constraint)) (nodeEquality : DecidableEq Node)
    (profile : Profile) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller (bits + 2)) (before captured : Cached) (memos : Memos)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (checkEmpty : Bool) (r n p h k target : Nat) (incoming : Node) (scs : List Suspended)
    (rooted : IsRoot before.core.representatives target) (inside : target < before.core.counter)
    (incomingBound : ∀ sc ∈ scs, sc.var < before.core.counter) :
    letI : DecidableEq Symbol := symbolEquality
    letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
    letI : DecidableEq Node := nodeEquality
    Packet formulas solver inventory caller memos metadata captured → CacheValid caller before →
    Available caller.checked.native.machine.heap incoming → incoming.free = [] →
    Fits profile caller.checked → Room bits profile →
    let actual := SourcePruningEnumerationIncomingCacheAdapter.run checkEmpty r n p h k caller before
      target incoming scs memos.query
    match actual.1.1 with
    | .ok _ => ∃ next final, Post formulas solver next caller actual.1.2.1 final ∧
        final.query = actual.1.2.2.1 ∧
        Packet formulas solver next actual.1.2.1 final metadata captured ∧
        ∀ after, actual.2 = some after → CacheValid actual.1.2.1 after
    | .error _ => True := by
  letI : DecidableEq Symbol := symbolEquality
  letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
  letI : DecidableEq Node := nodeEquality
  intro original valid available closed fits room
  have callerFacts := SourceCurrentIncomingReadFrame.incoming_ok_frame_valid symbolEquality edgeEquality
    nodeEquality profile formulas solver inventory caller before memos checkEmpty r n p h target incoming
    scs inside original.context valid available closed fits room
  change (let actual := SourcePruningEnumerationIncomingNode.run checkEmpty r n p h caller before.core target incoming scs memos.query;
    match actual.1 with
    | .ok _ => ∃ next final, Post formulas solver next caller actual.2.1 final ∧
        final.query = actual.2.2.1 ∧ CacheValid actual.2.1 (EnumerationExpandableIndex.frame actual.2.2.2 before)
    | .error _ => True) at callerFacts
  have freshFacts : ∀ after, (SourcePruningEnumerationIncomingCacheAdapter.run checkEmpty r n p h k
      caller before target incoming scs memos.query).2 = some after →
      CacheValid (SourcePruningEnumerationIncomingCacheAdapter.run checkEmpty r n p h k
        caller before target incoming scs memos.query).1.2.1 after := by
    intro after observed
    exact SourceCurrentIncomingSomeCacheValid.some_cache_valid symbolEquality edgeEquality nodeEquality
      profile formulas solver inventory caller before after memos checkEmpty r n p h k target incoming
      scs rooted incomingBound original.context valid available closed fits room observed
  simp only [SourcePruningEnumerationIncomingCacheAdapter.run] at freshFacts ⊢
  dsimp only at callerFacts
  generalize incomingObserved : SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
    caller before.core target incoming scs memos.query = actual at callerFacts freshFacts ⊢
  rcases actual with ⟨result, reached, savedQueries, read⟩
  cases result with
  | error fault => trivial
  | ok output =>
      dsimp only at callerFacts freshFacts ⊢
      obtain ⟨next, final, post, querySame, _frameValid⟩ := callerFacts
      exact ⟨next, final, post, querySame,
        SourcePruningEnumerationRecursive.captured_post original post, freshFacts⟩

end MicroCFTA.SourceCurrentIncomingCapturedPost
