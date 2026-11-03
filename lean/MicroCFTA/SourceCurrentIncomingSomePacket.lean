import MicroCFTA.SourceCurrentIncomingCapturedPost
import MicroCFTA.SourceCurrentIncomingSomeCounter
import MicroCFTA.SourceCurrentIncomingSomePredicates
import MicroCFTA.SourceCurrentIncomingSomeSafe

/-! Original current-cache Packets and staged inputs derive actual fresh optional-cache Packets. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentIncomingSomePacket
open EnumerationState EnumerationSchedule EnumerationDependencies InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationRecursive (Packet)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable {bits : Nat} {Typing : Type}

/-- Every actual Some cache receives all six Packet fields at the same actual Caller and saved query. -/
theorem incoming_some_packet (symbolEquality : DecidableEq Symbol)
    (edgeEquality : DecidableEq (EdgeKey Symbol Constraint)) (nodeEquality : DecidableEq Node)
    (profile : Profile) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller (bits + 2)) (before after : Cached) (memos : Memos)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (checkEmpty : Bool) (r n p h k target : Nat) (incoming : Node) (scs : List Suspended)
    (rooted : IsRoot before.core.representatives target)
    (incomingBound : ∀ sc ∈ scs, sc.var < before.core.counter) :
    letI : DecidableEq Symbol := symbolEquality
    letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
    letI : DecidableEq Node := nodeEquality
    let actual := SourcePruningEnumerationIncomingCacheAdapter.run checkEmpty r n p h k caller before
      target incoming scs memos.query
    Packet formulas solver inventory caller memos metadata before →
    Available caller.checked.native.machine.heap incoming → incoming.free = [] →
    Fits profile caller.checked → Room bits profile → InputsPending before.core scs →
    actual.2 = some after → ∃ next final,
      Post formulas solver next caller actual.1.2.1 final ∧ final.query = actual.1.2.2.1 ∧
      Packet formulas solver next actual.1.2.1 final metadata after := by
  letI : DecidableEq Symbol := symbolEquality
  letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
  letI : DecidableEq Node := nodeEquality
  dsimp only
  intro packet available closed fits room pending observed
  obtain ⟨oldNode, oldScs, stored⟩ := SourceCurrentIncomingSomeAdmission.some_stored symbolEquality
    edgeEquality nodeEquality checkEmpty r n p h k target caller before after incoming scs memos.query rooted observed
  have originalValid := packet.valid
  obtain ⟨_roots, _paths, storage, _realized, _counts, _flags⟩ := originalValid
  obtain ⟨inside, _combinedBound⟩ := SourceCurrentIncomingSomeAdmission.stored_admissions before.core
    target oldNode scs oldScs storage stored incomingBound
  have callerFacts := SourceCurrentIncomingCapturedPost.incoming_ok_captured_post symbolEquality edgeEquality
    nodeEquality profile formulas solver inventory caller before before memos metadata checkEmpty r n p h k
    target incoming scs rooted inside incomingBound packet packet.valid available closed fits room
  have safeFacts := SourceCurrentIncomingSomeSafe.some_cache_safe symbolEquality edgeEquality nodeEquality
    profile formulas solver inventory caller before after memos checkEmpty r n p h k target incoming scs
    rooted incomingBound packet.context packet.valid available closed fits room packet.safe observed
  have predicateFacts := SourceCurrentIncomingSomePredicates.some_cache_predicates symbolEquality edgeEquality
    nodeEquality profile formulas solver inventory caller before after memos metadata checkEmpty r n p h k
    target incoming scs rooted incomingBound packet available closed fits room pending observed
  have boundFacts := SourceCurrentIncomingSomeCounter.some_packet_bounds symbolEquality edgeEquality
    nodeEquality profile formulas solver inventory caller before after memos metadata checkEmpty r n p h k
    target incoming scs rooted incomingBound packet available closed fits room observed
  have rows := SourceCurrentIncomingSomeAdmission.some_rows symbolEquality edgeEquality nodeEquality
    checkEmpty r n p h k target caller before after incoming scs memos.query observed
  dsimp only at callerFacts rows
  generalize actualRun : SourcePruningEnumerationIncomingCacheAdapter.run checkEmpty r n p h k
    caller before target incoming scs memos.query = actual at callerFacts rows observed ⊢
  rcases actual with ⟨⟨result, reached, savedQueries, read⟩, returnedCache⟩
  cases result with
  | error fault =>
      rcases rows with impossible | ⟨_returned, impossible⟩
      · cases impossible
      · cases impossible
  | ok output =>
      dsimp only at callerFacts observed ⊢
      obtain ⟨next, final, post, querySame, _capturedBefore, freshValid⟩ := callerFacts
      exact ⟨next, final, post, querySame,
        ⟨post.context, safeFacts, predicateFacts.1, freshValid after observed, predicateFacts.2, boundFacts⟩⟩

end MicroCFTA.SourceCurrentIncomingSomePacket
