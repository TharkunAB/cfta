import MicroCFTA.InternedFreshOrdinaryActiveOrigins
import MicroCFTA.SourceCurrentStoredLiteralRowLineage

/-!
# Exact original slots for row-bearing source captures

Actual callback crossings add literal references before the original inputs.
A literal reference has no structural row. A row-bearing lookup therefore
retains its exact index in the original input suffix.
-/
namespace MicroCFTA.SourceCaptureOriginalSlotsPrototype
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryActiveOrigins (Crossing Path)
open SourceCurrentStoredLiteralRowLineage (RowAt)

private theorem reference_prefix [DecidableEq (EdgeKey Symbol Guard)]
    (crossings : List (Crossing Symbol Guard)) (initial : List (Value Symbol Guard))
    (captured : Value Symbol Guard) (row : EdgeValue Symbol Guard) (inside : RowAt captured row)
    (slot : Nat)
    (found : (crossings.map (fun crossing => Value.reference crossing.name) ++ initial)[slot]? = some captured) :
    ∃ originalSlot, slot = crossings.length + originalSlot ∧ initial[originalSlot]? = some captured := by
  induction crossings generalizing slot with
  | nil => exact ⟨slot,by simp,by simpa only [List.map_nil,List.nil_append] using found⟩
  | cons crossing crossings ih =>
      cases slot with
      | zero =>
          have same : Value.reference crossing.name = captured := by
            simpa only [List.map_cons,List.cons_append,List.getElem?_cons_zero,Option.some.injEq] using found
          subst captured
          cases inside
      | succ slot =>
          have tail : (crossings.map (fun crossing => Value.reference crossing.name) ++ initial)[slot]? = some captured := by
            simpa only [List.map_cons,List.cons_append,List.getElem?_cons_succ] using found
          obtain ⟨originalSlot,offset,selected⟩ := ih slot tail
          exact ⟨originalSlot,by simp only [List.length_cons]; omega,selected⟩

/-- A row-bearing capture retains its exact original index after the callback prefix. -/
theorem original_slot [DecidableEq (EdgeKey Symbol Guard)]
    {root expression : Syntax Symbol Guard} {initial inputs : List (Value Symbol Guard)}
    {crossings : List (Crossing Symbol Guard)}
    (path : Path root initial expression inputs crossings) (slot : Nat)
    (captured : Value Symbol Guard) (found : inputs[slot]? = some captured)
    (row : EdgeValue Symbol Guard) (inside : RowAt captured row) :
    ∃ originalSlot, slot = crossings.length + originalSlot ∧ initial[originalSlot]? = some captured := by
  apply reference_prefix crossings initial captured row inside slot
  simpa only [path.inputs] using found

/-- Empty original inputs exclude every row-bearing capture along the supplied source path. -/
theorem empty_initial [DecidableEq (EdgeKey Symbol Guard)]
    {root expression : Syntax Symbol Guard} {inputs : List (Value Symbol Guard)}
    {crossings : List (Crossing Symbol Guard)}
    (path : Path root [] expression inputs crossings) (slot : Nat)
    (captured : Value Symbol Guard) (found : inputs[slot]? = some captured)
    (row : EdgeValue Symbol Guard) : ¬ RowAt captured row := by
  intro inside
  obtain ⟨originalSlot,_offset,selected⟩ := original_slot path slot captured found row inside
  simp only [List.getElem?_nil] at selected
  cases selected

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option cbv.maxSteps 10000000
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryFacts (callback)
local notation "Node" => Value Nat Bool
local notation "Heap" => State Nat Bool
local notation "Row" => EdgeValue Nat Bool

private def leafSource : Syntax Nat Bool := .node [.mk 17 false []]
private def built := build leafSource [] (empty : Heap)
private def leaf : Node := match built with | .done value _ => value | .pending .. => .empty
private def heap : Heap := built.state
private def row : Row := (InternedEdgeResidency.nodeEdges leaf)[0]?.getD (run (makeEdge 0 false []) (empty : Heap)).1
private def body : Syntax Nat Bool := .var 1
private theorem built_done : build leafSource [] (empty : Heap) = .done leaf heap := by cbv
private theorem captured_context : InternedFreshOrdinaryContext.Context heap [leaf] := by
  have context : InternedFreshOrdinaryContext.Context heap [] := by
    simpa only [built,built_done,Outcome.state] using
      (InternedFreshOrdinaryContext.empty_context (Symbol := Nat) (Guard := Bool)).build leafSource
  have available : Available heap leaf :=
    (InternedFreshOrdinaryFacts.closed_verified leafSource).result leaf heap built_done
  refine {context with inputs := ?_}
  intro value member
  have same : value = leaf := by simpa only [List.mem_singleton] using member
  subst value
  exact available
private def crossing : Crossing Nat Bool where
  smart := false
  body := body
  environment := [leaf]
  before := heap
  name := .depth
  start := heap
  context := captured_context
  entered := .depth
private theorem callback_done : callback body [leaf] .depth heap = .done leaf heap := by cbv
private theorem actual_path : Path (.binder false body) [leaf] body [.reference .depth,leaf] [crossing] :=
  .binder crossing (.here body [.reference .depth,leaf])
private theorem inside : RowAt leaf row := by
  cbv
  exact .node (index := 0) rfl
private theorem checked_witness :
    build leafSource [] (empty : Heap) = .done leaf heap ∧
    callback body [leaf] .depth heap = .done leaf heap ∧
    Path (.binder false body) [leaf] body [.reference .depth,leaf] [crossing] ∧
    ([.reference .depth,leaf] : List Node)[1]? = some leaf ∧ RowAt leaf row ∧
    ∃ originalSlot, 1 = ([crossing] : List (Crossing Nat Bool)).length + originalSlot ∧
      ([leaf] : List Node)[originalSlot]? = some leaf := by
  refine ⟨built_done,callback_done,actual_path,rfl,inside,?_⟩
  exact original_slot actual_path 1 leaf rfl row inside

/-- An actual Depth callback retains its row-bearing capture at slot one and original slot zero. -/
theorem actual_callback :
    build leafSource [] (empty : Heap) = .done leaf heap ∧
    callback body [leaf] .depth heap = .done leaf heap ∧
    Path (.binder false body) [leaf] body [.reference .depth,leaf] [crossing] ∧
    ([.reference .depth,leaf] : List Node)[1]? = some leaf ∧ RowAt leaf row ∧
    ∃ originalSlot, 1 = ([crossing] : List (Crossing Nat Bool)).length + originalSlot ∧
      ([leaf] : List Node)[originalSlot]? = some leaf := checked_witness

end MicroCFTA.SourceCaptureOriginalSlotsPrototype

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.SourceCaptureOriginalSlotsPrototype.original_slot
#print MicroCFTA.SourceCaptureOriginalSlotsPrototype.original_slot
#print axioms MicroCFTA.SourceCaptureOriginalSlotsPrototype.original_slot
#check @MicroCFTA.SourceCaptureOriginalSlotsPrototype.empty_initial
#print MicroCFTA.SourceCaptureOriginalSlotsPrototype.empty_initial
#print axioms MicroCFTA.SourceCaptureOriginalSlotsPrototype.empty_initial
#check @MicroCFTA.SourceCaptureOriginalSlotsPrototype.actual_callback
#print MicroCFTA.SourceCaptureOriginalSlotsPrototype.actual_callback
#print axioms MicroCFTA.SourceCaptureOriginalSlotsPrototype.actual_callback
