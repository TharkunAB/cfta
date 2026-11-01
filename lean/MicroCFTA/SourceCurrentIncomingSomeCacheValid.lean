import MicroCFTA.SourceCurrentIncomingSomeAdmission
import MicroCFTA.SourceCurrentIncomingEmptyCacheValid

/-! Actual optional cache returns derive full validity without supplied output-shape admissions. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentIncomingSomeCacheValid
open EnumerationState EnumerationSchedule InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
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

/-- Original inputs derive all five fields for every actual optional Some cache. -/
theorem some_cache_valid (symbolEquality : DecidableEq Symbol)
    (edgeEquality : DecidableEq (EdgeKey Symbol Constraint)) (nodeEquality : DecidableEq Node)
    (profile : Profile) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller (bits + 2)) (before after : Cached) (memos : Memos)
    (checkEmpty : Bool) (r n p h k target : Nat) (incoming : Node) (scs : List Suspended)
    (rooted : IsRoot before.core.representatives target)
    (incomingBound : ∀ sc ∈ scs, sc.var < before.core.counter) :
    letI : DecidableEq Symbol := symbolEquality
    letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
    letI : DecidableEq Node := nodeEquality
    let actual := SourcePruningEnumerationIncomingCacheAdapter.run checkEmpty r n p h k caller before
      target incoming scs memos.query
    Context formulas solver inventory caller memos → CacheValid caller before →
    Available caller.checked.native.machine.heap incoming → incoming.free = [] →
    Fits profile caller.checked → Room bits profile →
    actual.2 = some after → CacheValid actual.1.2.1 after := by
  letI : DecidableEq Symbol := symbolEquality
  letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
  letI : DecidableEq Node := nodeEquality
  dsimp only
  intro initial valid available closed fits room cacheSome
  obtain ⟨oldNode, oldScs, stored⟩ := SourceCurrentIncomingSomeAdmission.some_stored symbolEquality
    edgeEquality nodeEquality checkEmpty r n p h k target caller before after incoming scs memos.query
    rooted cacheSome
  have storage := valid
  obtain ⟨_roots, _paths, originalStorage, _realized, _counts, _flags⟩ := storage
  obtain ⟨inside, bounded⟩ := SourceCurrentIncomingSomeAdmission.stored_admissions before.core
    target oldNode scs oldScs originalStorage stored incomingBound
  have rows := SourceCurrentIncomingSomeAdmission.some_rows symbolEquality edgeEquality nodeEquality
    checkEmpty r n p h k target caller before after incoming scs memos.query cacheSome
  generalize actualRun : SourcePruningEnumerationIncomingCacheAdapter.run checkEmpty r n p h k
    caller before target incoming scs memos.query = actual at cacheSome rows ⊢
  rcases actual with ⟨⟨result, reached, savedQueries, read⟩, returnedCache⟩
  dsimp only at cacheSome rows ⊢
  have callSame : SourcePruningEnumerationIncomingCacheAdapter.run checkEmpty r n p h k
      caller before target incoming scs memos.query = ((result, reached, savedQueries, read), some after) := by
    rw [actualRun, cacheSome]
  rcases rows with emptyRows | ⟨returned, singletonRows⟩
  · have observed : SourcePruningEnumerationIncomingCacheAdapter.run checkEmpty r n p h k
        caller before target incoming scs memos.query = ((.ok (some []), reached, savedQueries, read), some after) := by
      simpa only [emptyRows] using callSame
    exact SourceCurrentIncomingEmptyCacheValid.empty_cache_valid symbolEquality edgeEquality nodeEquality
      profile formulas solver inventory caller reached before after memos checkEmpty r n p h k target
      incoming scs oldScs oldNode stored inside bounded savedQueries read initial valid available closed fits room observed
  · have observed : SourcePruningEnumerationIncomingCacheAdapter.run checkEmpty r n p h k
        caller before target incoming scs memos.query =
          ((.ok (some [.ok ((), returned)]), reached, savedQueries, read), some after) := by
      simpa only [singletonRows] using callSame
    exact SourceCurrentIncomingSingletonCacheValid.singleton_cache_valid symbolEquality edgeEquality nodeEquality
      profile formulas solver inventory caller reached before after memos checkEmpty r n p h k target incoming
      scs oldScs oldNode rooted stored inside bounded savedQueries read returned initial valid available closed fits room observed

end MicroCFTA.SourceCurrentIncomingSomeCacheValid
