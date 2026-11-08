import MicroCFTA.SourceCurrentIncomingPost
import MicroCFTA.SourceCurrentIncomingReadRoots
import MicroCFTA.SourceSizedPrefixKnownOrdinaryHeap

/-! Actual successful incoming outcomes derive realization at their reached caller heap. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentIncomingReachedReadRealized
open EnumerationState EnumerationSchedule InternedConstructorTemplates
open SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
attribute [local instance] FormulaExecutable.formulaDecidableEq
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos

private noncomputable def canonicalSymbol : DecidableEq Symbol := inferInstance
private noncomputable def canonicalNode : DecidableEq Node := fun a b => Classical.propDecidable (a = b)
variable {bits : Nat}

/-- Original caller facts derive Post and realization at the literal reached caller and outer read. -/
theorem incoming_ok_read_realized (symbolEquality : DecidableEq Symbol)
    (edgeEquality : DecidableEq (EdgeKey Symbol Constraint)) (nodeEquality : DecidableEq Node)
    (profile : Profile) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller (bits + 2)) (before : Core) (memos : Memos)
    (checkEmpty : Bool) (r n p h target : Nat) (incoming : Node) (scs : List Suspended)
    (roots : Nat → Nat) (paths : Roots before.representatives roots) :
    letI : DecidableEq Symbol := symbolEquality
    letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
    letI : DecidableEq Node := nodeEquality
    Context formulas solver inventory caller memos →
    PendingRealized caller.checked.native.machine.heap before →
    InternedProbeProvenance.Available caller.checked.native.machine.heap incoming → incoming.free = [] →
    Fits profile caller.checked → Room bits profile →
    let actual := SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
      caller before target incoming scs memos.query
    match actual.1 with
    | .ok _ => ∃ next final, Post formulas solver next caller actual.2.1 final ∧
        final.query = actual.2.2.1 ∧
        PendingRealized actual.2.1.checked.native.machine.heap actual.2.2.2
    | .error _ => True := by
  cases Subsingleton.elim symbolEquality canonicalSymbol
  cases Subsingleton.elim nodeEquality canonicalNode
  letI : DecidableEq Symbol := canonicalSymbol
  letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
  letI : DecidableEq Node := canonicalNode
  dsimp only
  intro initial realized available closed fits room
  have callerPost := SourceCurrentIncomingPost.incoming_ok_post profile formulas solver inventory caller before
    checkEmpty r n p h target incoming scs memos initial realized available closed fits (Or.inl room)
  have readFacts := SourceCurrentIncomingReadRoots.incoming_read_roots canonicalSymbol edgeEquality canonicalNode
    checkEmpty r n p h caller before target incoming scs memos roots paths
  change (let actual := SourcePruningEnumerationIncomingNode.run checkEmpty r n p h caller before target incoming scs memos.query;
    match actual.1 with
    | .ok _ => ∃ next final, Post formulas solver next caller actual.2.1 final ∧
        final.query = actual.2.2.1
    | .error _ => True) at callerPost
  dsimp only at callerPost readFacts ⊢
  generalize observed : SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
    caller before target incoming scs memos.query = actual at callerPost readFacts ⊢
  rcases actual with ⟨result, reached, savedQueries, read⟩
  cases result with
  | error fault => trivial
  | ok output =>
      obtain ⟨next, final, post, querySame⟩ := callerPost
      refine ⟨next, final, post, querySame, ?_⟩
      intro slot handle suspensions slotRead
      have oldRead : before.values[slot]? = some (.unenumerated (some handle) suspensions) := by
        rw [← readFacts.2.1]
        exact slotRead
      obtain ⟨node, present, nodeAvailable, nodeClosed⟩ := realized slot handle suspensions oldRead
      exact ⟨node, SourceSizedPrefixKnownOrdinaryHeap.post_lookupNode post handle node present,
        post.effects.keeps.available node nodeAvailable, nodeClosed⟩

end MicroCFTA.SourceCurrentIncomingReachedReadRealized
