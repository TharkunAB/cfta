import MicroCFTA.InternedFreshOrdinaryUnfoldMemo
import MicroCFTA.InternedFreshOrdinaryStatefulGateClasses

/-!
# Ordered gate graphs with a coherent unfolding memo

Each actual unfolding memo call retains its exact constructor readback.
Node, child, and edge traces pass the returned memo and constructor cache
together. A true result stops the scan and leaves the suffix unvisited.
-/
namespace MicroCFTA.InternedFreshOrdinaryMemoGateTrace
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedFreshOrdinaryContext
open InternedFreshOrdinaryGateRank (Node)
open InternedFreshOrdinaryUnfoldMemo (Memo Correct)
open EqualityNormalize

/-- A constructor cache retains every semantic invariant required by the source gate. -/
def Ready (state : State Symbol Guard) : Prop := Context state [] ∧
  InternedFreshOrdinaryDepthHeap.Heap state ∧ Covered [] state ∧ InternedFreshOrdinaryCostHeap.Heap state

/-- Every certified source node supplies the complete ready-cache invariant. -/
theorem node_ready (node : Node Symbol Guard) : Ready node.state :=
  ⟨node.context, node.depth, node.covered, node.costs⟩

/-- A ready cache and available queried value supply the existing certified source node. -/
def Ready.node {state : State Symbol Guard} (ready : Ready state) (value : Value Symbol Guard) (available : Available state value) : Node Symbol Guard :=
  ⟨state, value, ready.1, ready.2.1, ready.2.2.1, ready.2.2.2, available⟩

/-- A returned query cache retains semantic heaps, memo coherence, and both histories. -/
structure Keeps [DecidableEq (EdgeKey Symbol Guard)] (before after : State Symbol Guard) (memo : Memo Symbol Guard) : Prop where
  ready : Ready after
  correct : Correct after memo
  growth : Grows before after
  history : Extends before.nodes.issued after.nodes.issued

/-- A query without effects retains the initial ready cache and coherent memo. -/
theorem pure_keeps [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) (memo : Memo Symbol Guard)
    (ready : Ready state) (correct : Correct state memo) : Keeps state state memo :=
  ⟨ready, correct, grows_refl _, extends_refl _⟩

/-- Ordered queries compose their exact returned caches and reservation histories. -/
theorem prepend_keeps [DecidableEq (EdgeKey Symbol Guard)]
    {before middle after : State Symbol Guard} {firstMemo finalMemo : Memo Symbol Guard}
    (first : Keeps before middle firstMemo) (second : Keeps middle after finalMemo) : Keeps before after finalMemo :=
  ⟨second.ready, second.correct, grows_trans first.growth second.growth, extends_trans first.history second.history⟩

mutual
/-- A node trace records actual memo calls and exact constructor readback at every unfolding. -/
inductive NodeTrace [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool) :
    Path → Value Symbol Guard → Memo Symbol Guard → State Symbol Guard → Bool → Memo Symbol Guard → State Symbol Guard → Prop where
  | empty : NodeTrace unconstrained path .empty memo state false memo state
  | reference : NodeTrace unconstrained path (.reference name) memo state true memo state
  | union (members : List (Value Symbol Guard)) : NodeTrace unconstrained path (.union entry members depth free) memo state true memo state
  | finite (fast : (depth == 0 && free.isEmpty) = true) :
      NodeTrace unconstrained path (.node entry edges depth free) memo state false memo state
  | endpoint (slow : (depth == 0 && free.isEmpty) = false) :
      NodeTrace unconstrained [] (.node entry edges depth free) memo state (!free.isEmpty) memo state
  | branches (slow : (depth == 0 && free.isEmpty) = false)
      (trace : EdgesTrace unconstrained index rest edges memo state answer saved final) :
      NodeTrace unconstrained (index :: rest) (.node entry edges depth free) memo state answer saved final
  | constrained (blocked : unconstrained (.mu entry body depth ordinary) = false) :
      NodeTrace unconstrained path (.mu entry body depth ordinary) memo state true memo state
  | closed (plain : unconstrained (.mu entry body depth ordinary) = true)
      (closed : (Value.mu entry body depth ordinary).free.isEmpty = true) :
      NodeTrace unconstrained path (.mu entry body depth ordinary) memo state false memo state
  | unfold (plain : unconstrained (.mu entry body depth ordinary) = true)
      (opened : (Value.mu entry body depth ordinary).free.isEmpty = false)
      (actual : InternedFreshOrdinaryUnfoldMemo.run (.mu entry body depth ordinary) memo state = .done (next, afterMemo) after)
      (readback : InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) state = .done next after)
      (trace : NodeTrace unconstrained path next afterMemo after answer saved final) :
      NodeTrace unconstrained path (.mu entry body depth ordinary) memo state answer saved final

/-- Child lookup retains the exact selected record and both returned caches. -/
inductive ChildTrace [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool) :
    List (Value Symbol Guard) → Nat → Path → Memo Symbol Guard → State Symbol Guard → Bool → Memo Symbol Guard → State Symbol Guard → Prop where
  | missing (absent : values[index]? = none) : ChildTrace unconstrained values index path memo state false memo state
  | present (found : values[index]? = some value) (trace : NodeTrace unconstrained path value memo state answer saved final) :
      ChildTrace unconstrained values index path memo state answer saved final

/-- False edges pass both actual caches to the next edge; true edges stop. -/
inductive EdgesTrace [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool) :
    Nat → Path → List (EdgeValue Symbol Guard) → Memo Symbol Guard → State Symbol Guard → Bool → Memo Symbol Guard → State Symbol Guard → Prop where
  | nil : EdgesTrace unconstrained index path [] memo state false memo state
  | stop (head : ChildTrace unconstrained edge.children index path memo state true saved final) :
      EdgesTrace unconstrained index path (edge :: rest) memo state true saved final
  | next (head : ChildTrace unconstrained edge.children index path memo state false middleMemo middle)
      (tail : EdgesTrace unconstrained index path rest middleMemo middle answer saved final) :
      EdgesTrace unconstrained index path (edge :: rest) memo state answer saved final
end

/-- Removing memo receipts recovers the exact source node graph and complete constructor cache. -/
theorem erase_node [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (path : Path) (value : Value Symbol Guard) (memo : Memo Symbol Guard) (state : State Symbol Guard)
    (answer : Bool) (saved : Memo Symbol Guard) (final : State Symbol Guard)
    (trace : NodeTrace unconstrained path value memo state answer saved final) :
    InternedFreshOrdinaryStatefulGateTrace.NodeTrace unconstrained path value state answer final := by
  induction trace using NodeTrace.rec
      (motive_2 := fun values index path _ state answer _ final _ =>
        InternedFreshOrdinaryStatefulGateTrace.ChildTrace unconstrained values index path state answer final)
      (motive_3 := fun index path edges _ state answer _ final _ =>
        InternedFreshOrdinaryStatefulGateTrace.EdgesTrace unconstrained index path edges state answer final) with
  | empty => exact .empty
  | reference => exact .reference
  | union members => exact .union members
  | finite fast => exact .finite fast
  | endpoint slow => exact .endpoint slow
  | branches slow trace ih => exact .branches slow ih
  | constrained blocked => exact .constrained blocked
  | closed plain closed => exact .closed plain closed
  | unfold plain opened actual readback trace ih => exact .unfold plain opened readback ih
  | missing absent => exact .missing absent
  | present found trace ih => exact .present found ih
  | nil => exact .nil
  | stop head ih => exact .stop ih
  | next head tail headIH tailIH => exact .next headIH tailIH

end MicroCFTA.InternedFreshOrdinaryMemoGateTrace
