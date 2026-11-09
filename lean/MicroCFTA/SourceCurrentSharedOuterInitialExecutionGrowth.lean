import MicroCFTA.SourceCurrentSharedOuterInitialPrefix
import MicroCFTA.SourceCurrentSharedOuterExecutionRuntime

/-!
# Initialized shared prefixes derive operation growth

The initial semantic and numeric facts supply each actual prefix Post.
The same initial Room also supplies the seed at a captured activation.
Its remaining body prefix then derives growth to the current reader.
No future Context, operation-growth certificate or successful whole call
is an input. Resource-free all-outcome growth remains a separate contract.
-/
namespace MicroCFTA.SourceCurrentSharedOuterInitialExecutionGrowth
open Cache InternedConstructorTemplates
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentSharedOuterExecutionAncestry (Reached caller)
open SourceCurrentSharedOuterExecutionRuntime (NodeValid Ancestor)
open SourceCurrentSharedOuterPrefixInvariants (Inputs)
open SourceEqualityConstraintMemoAllocation (Grows)
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "forecast" => SourceCurrentSharedOuterInitialPrefix.forecast

variable [DecidableEq (SourceObservations.Label FullSyntax.Formula)]
  [DecidableEq (EdgeKey (SourceObservations.Label FullSyntax.Formula) Guard)]
  [DecidableEq (Value (SourceObservations.Label FullSyntax.Formula) Guard)]

/-- The exact captured activation retains derived growth to the current caller. -/
def GrowingAncestor (g s r e p h m c n budget : Nat) (first current : Phase width)
    (handle : Nat) (owner : NodeRequest) : Prop :=
  ∃ fuel request before running,
    Reached g s r e p h m c n budget first (.node fuel request before) ∧
    beginNode request before = (handle, .evaluate owner, running) ∧
    owner.key = request.key ∧ NodeValid running ∧
    running.nodeResults.cells handle = some ⟨owner, .evaluating⟩ ∧
    Reached g s r e p h m c n budget (.body fuel owner running) current ∧
    Grows running.checked.operations (caller current).checked.operations

variable {bits : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula)
  (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- One initial reservation derives operation growth along any actual shared prefix. -/
theorem reached {g s r e p h m c n budget : Nat} {first last : Phase (bits+2)}
    {inventory : Inventory} {memos : Memos} (seed : List Guard × Profile)
    (actual : Reached g s r e p h m c n budget first last)
    (initial : Context formulas solver inventory (caller first) memos)
    (frame : Frame formulas solver inventory (caller first).checked)
    (fits : Fits seed.2 (caller first).checked)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1)
      (caller first).checked.native.machine.heap)
    (inputs : Inputs first) (room : Room bits (forecast budget first seed).2) :
    Grows (caller first).checked.operations (caller last).checked.operations := by
  obtain ⟨_next,_final,_current,_trace,post,_returned,_numeric,_carrier,_ready,
      _below,_subset,_room,_fits,_known,_need⟩ :=
    SourceCurrentSharedOuterInitialPrefix.reached formulas solver seed actual
      initial frame fits known inputs room
  exact post.effects.grows

/-- The original reservation derives growth along each captured unfinished body. -/
theorem ancestor {g s r e p h m c n budget handle : Nat}
    {first current : Phase (bits+2)} {owner : NodeRequest}
    {inventory : Inventory} {memos : Memos} (seed : List Guard × Profile)
    (actual : Ancestor g s r e p h m c n budget first current handle owner)
    (initial : Context formulas solver inventory (caller first) memos)
    (frame : Frame formulas solver inventory (caller first).checked)
    (fits : Fits seed.2 (caller first).checked)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1)
      (caller first).checked.native.machine.heap)
    (inputs : Inputs first) (room : Room bits (forecast budget first seed).2) :
    GrowingAncestor g s r e p h m c n budget first current handle owner := by
  obtain ⟨fuel,request,before,running,earlier,started,key,valid,present,later⟩ := actual
  have activated := Reached.snoc earlier (.node_evaluate started)
  obtain ⟨_next,_final,bodySeed,_trace,post,returned,numeric,carrier,ready,
      _below,_subset,bodyRoom,_fits,_known,_need⟩ :=
    SourceCurrentSharedOuterInitialPrefix.reached formulas solver seed activated
      initial frame fits known inputs room
  have grows := reached formulas solver bodySeed later post.context returned
    numeric carrier ready bodyRoom
  exact ⟨fuel,request,before,running,earlier,started,key,valid,present,later,grows⟩

end MicroCFTA.SourceCurrentSharedOuterInitialExecutionGrowth
