import MicroCFTA.SourceCurrentConstrainedCapSourceHistory
import MicroCFTA.SourceCurrentConstrainedCapGuardHeap
import MicroCFTA.SourceCurrentConstrainedCapGuardSemantics
import MicroCFTA.SourceCurrentConstrainedCapGuardNormalization
import MicroCFTA.SourceCurrentConstrainedCapGuardReadback

/-!
# Guard observations through actual source construction

The syntax induction retains the causal guard heap at every stopping state.
Each actual earlier callback supplies its own observation before the next
callback starts. Fresh publication derives the body-to-probe equality.
Warm readback uses the earlier writer's retained certificate.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapGuardExecution
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance InternedNestedFacts
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request finish)
open InternedNestedProvenance (Values Edges depth_available ordinary_available)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedBinderProtocol (Reference NodeKey)
open SourceCurrentConstrainedCapGuardHeap (Heap Checked done_checked bind_checked preserve)
local notation "Context" => SourceCurrentConstrainedCapSourceHistory.Context
local notation "profile" => SourceCurrentConstrainedCapGuardDepth.profile
local notation "GShape" => SourceCurrentConstrainedCapGuardSemantics.Shape
local notation "decode" => SourceCurrentConstrainedCapGuardSemantics.decode
local notation "evaluate" => SourceCurrentConstrainedCapGuardSemantics.evaluate
local notation "evaluateMany" => SourceCurrentConstrainedCapGuardSemantics.evaluateMany
local notation "evaluateEdges" => SourceCurrentConstrainedCapGuardSemantics.evaluateEdges
variable {Symbol Guard : Type}

/-- Each original child position retains its actual structural and guard observation. -/
def Observation (valid : Guard → Prop) (value : Value Symbol Guard) (shape : GShape Reference) : Prop :=
  InternedFreshOrdinaryDepthComposition.Observed value shape.shape ∧ profile valid value = shape.guardDepth

/-- Ordered source children retain both observations at every literal position. -/
abbrev Matches (valid : Guard → Prop) (values : List (Value Symbol Guard)) (shapes : List (GShape Reference)) :=
  InternedOccurrenceObservations.Paired (Observation valid) values shapes

private theorem matches_shape {valid : Guard → Prop} {values : List (Value Symbol Guard)} {shapes : List (GShape Reference)}
    (matched : Matches valid values shapes) :
    InternedFreshOrdinaryDepthComposition.Matches values (shapes.map SourceCurrentConstrainedCapGuardSemantics.Shape.shape) := by
  induction matched with
  | nil => exact .nil
  | cons first rest ih => exact .cons first.1 ih

private theorem matches_guard {valid : Guard → Prop} {values : List (Value Symbol Guard)} {shapes : List (GShape Reference)}
    (matched : Matches valid values shapes) :
    SourceCurrentConstrainedCapGuardDepth.children valid values =
      (SourceCurrentConstrainedCapGuardSemantics.combineMany shapes).guardDepth := by
  induction matched with
  | nil => simp [SourceCurrentConstrainedCapGuardDepth.children, SourceCurrentConstrainedCapGuardSemantics.combineMany]
  | cons first rest ih => simp only [SourceCurrentConstrainedCapGuardDepth.children,
      SourceCurrentConstrainedCapGuardSemantics.combineMany, SourceCurrentConstrainedCapGuardSemantics.combine,
      first.2, ih]

private theorem bind_heap (valid : Guard → Prop) (outcome : Outcome Symbol Guard A)
    (next : A → State Symbol Guard → Outcome Symbol Guard B) (heap : Heap valid outcome.state)
    (later : ∀ value after, outcome = .done value after → Heap valid after → Heap valid (next value after).state) :
    Heap valid (outcome.bind next).state := by
  cases outcome with
  | pending => exact heap
  | done value after => exact later value after rfl heap

private theorem request_heap [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (smart : Bool)
    (expression : Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (context : Context state environment) (heap : Heap valid state) (expected : Option Nat)
    (ordinarySame : profile valid ordinary = expected)
    (recurse : ∀ name current, Context current environment → Available current (.reference name) → Heap valid current →
      Checked valid (callback expression environment name current) (fun value => profile valid value = expected)) :
    Heap valid (request smart depth ordinary (callback expression environment) state).state := by
  cases installed : state.nodes.table (muKey depth ordinary) with
  | some entry =>
      cases present : state.nodeRecords (muKey depth ordinary) <;>
        simpa only [request, installed, present, Outcome.state] using heap
  | none =>
      let key := muKey depth ordinary
      let entry := Cache.intern state.nodes key
      let allocated := {state with nodes := entry.2}
      have reserved : Context allocated environment := context.reserve key
      have argument : Available allocated (.reference (.interned entry.1.identity)) :=
        (InternedConstructionProvenance.reserve_available key state context.base.normal.facts.coherent
          context.base.normal.facts.cached).2
      have actual := recurse (.interned entry.1.identity) allocated reserved argument heap
      simp only [request, installed]
      change Heap valid ((callback expression environment (.interned entry.1.identity) allocated).bind
        (fun value after => InternedNestedRequestFacts.complete smart entry.1 value depth ordinary after)).state
      apply bind_heap valid _ _ actual.heap
      intro value after done afterHeap
      exact SourceCurrentConstrainedCapGuardHeap.complete_heap valid smart entry.1 value depth ordinary after afterHeap
        ((actual.result value after done).trans ordinarySame.symm)

private theorem request_profile [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (smart : Bool)
    (depth ordinary : Value Symbol Guard) (call : Reference → State Symbol Guard → Outcome Symbol Guard (Value Symbol Guard))
    (state : State Symbol Guard) (value : Value Symbol Guard) (after : State Symbol Guard)
    (actual : request smart depth ordinary call state = .done value after)
    (facts : Facts after) (depthAvailable : Available after depth) (ordinaryAvailable : Available after ordinary)
    (depthHeap : InternedFreshOrdinaryDepthHeap.Heap after) (guardHeap : Heap valid after) :
    profile valid value = SourceCurrentConstrainedCapGuardReadback.decoded valid smart depth ordinary := by
  cases installed : state.nodes.table (muKey depth ordinary) with
  | some entry =>
      cases present : state.nodeRecords (muKey depth ordinary) with
      | none => simp only [request, installed, present] at actual; cases actual
      | some result =>
          simp only [request, installed, present] at actual
          cases actual
          exact SourceCurrentConstrainedCapGuardReadback.hit_profile valid smart depth ordinary result state
            facts depthAvailable ordinaryAvailable depthHeap guardHeap present
  | none =>
      let entry := Cache.intern state.nodes (muKey depth ordinary)
      let allocated := {state with nodes := entry.2}
      simp only [request, installed] at actual
      change (call (.interned entry.1.identity) allocated).bind _ = .done value after at actual
      cases called : call (.interned entry.1.identity) allocated with
      | pending key stopped => simp only [called, Outcome.bind] at actual; cases actual
      | done body middle =>
          simp only [called, Outcome.bind] at actual
          obtain ⟨winner, present⟩ := keepFirst_present middle.nodeRecords (muKey depth ordinary) (.mu entry.1 body depth ordinary)
          dsimp only [entry] at present
          simp only [present, Option.getD_some] at actual
          cases actual
          exact SourceCurrentConstrainedCapGuardReadback.hit_profile valid smart depth ordinary winner _
            facts depthAvailable ordinaryAvailable depthHeap guardHeap present

end MicroCFTA.SourceCurrentConstrainedCapGuardExecution
