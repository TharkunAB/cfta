import MicroCFTA.EqualityLeafProjectionClosedWorkers
import MicroCFTA.EqualityLeafProjectionEditAvailability

/-!
# Closed source edit requests

Completed edits expose exact ordered child and edge requests. The final
parent constructor replays the same complete record without allocation.
-/
namespace MicroCFTA.EqualityLeafProjectionEditClosed
open InternedConstructorTemplates InternedRecordCoherence
open EqualityLeafProjectionSyntax (Path descendEdits)
open EqualityLeafProjectionWorkers EqualityLeafProjectionPhysical
open EqualityLeafProjectionRepresentation EqualityLeafProjectionWorkerReadback
open EqualityLeafProjectionClosedWorkers

/-- A successful closed child edit retains the exact head and tail requests. -/
theorem children_decompose [DecidableEq (EdgeKey Symbol Guard)]
    (meet : Target → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (edits : List (Path × Target)) (index : Nat) (child : Value Symbol Guard) (rest : List (Value Symbol Guard))
    (state : State Symbol Guard) (valid : InternedConstructorTemplates.Valid state)
    (values : List (Value Symbol Guard))
    (closed : run (editChildren meet edits index (child :: rest)) state = (some values, state)) :
    ∃ value tail, values = value :: tail ∧ run (edit meet (descendEdits edits index) child) state = (some value, state) ∧
      run (editChildren meet edits (index + 1) rest) state = (some tail, state) := by
  rw [editChildren] at closed
  obtain ⟨value, headClosed, remaining⟩ := optional_bind_closed _ _ state valid values closed
  obtain ⟨tail, tailClosed, actual⟩ := optional_bind_closed _ _ state valid values remaining
  have same : value :: tail = values := Option.some.inj (congrArg Prod.fst actual)
  exact ⟨value, tail, same.symm, headClosed, tailClosed⟩

/-- A successful closed row edit retains its child, edge, and tail requests. -/
theorem edges_decompose [DecidableEq (EdgeKey Symbol Guard)]
    (meet : Target → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (edits : List (Path × Target)) (entry : Cache.Interned (EdgeKey Symbol Guard))
    (children : List (Value Symbol Guard)) (rest : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (valid : InternedConstructorTemplates.Valid state)
    (values : List (EdgeValue Symbol Guard))
    (closed : run (editEdges meet edits (.mk entry children :: rest)) state = (some values, state)) :
    ∃ nodes edge tail, values = edge :: tail ∧ run (editChildren meet edits 0 children) state = (some nodes, state) ∧
      run (makeEdge entry.key.symbol entry.key.constraint nodes) state = (edge, state) ∧
      run (editEdges meet edits rest) state = (some tail, state) := by
  rw [editEdges] at closed
  obtain ⟨nodes, childClosed, remaining⟩ := optional_bind_closed _ _ state valid values closed
  obtain ⟨edge, edgeClosed, tailRequest⟩ := bind_closed _ _ state valid (some values) remaining
  obtain ⟨tail, tailClosed, actual⟩ := optional_bind_closed _ _ state valid values tailRequest
  have same : edge :: tail = values := Option.some.inj (congrArg Prod.fst actual)
  exact ⟨nodes, edge, tail, same.symm, childClosed, edgeClosed, tailClosed⟩

/-- The source parent constructor replays the already returned complete record. -/
theorem parent_replay [DecidableEq (EdgeKey Symbol Guard)]
    (meet : Target → Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (first : Path × Target) (rest : List (Path × Target))
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Guard))
    (depth : Nat) (free : List InternedBinderProtocol.Reference) (ordinary : OrdinaryEdges edges)
    (noRoot : EqualityLeafProjectionSyntax.atRoot (first :: rest) = none)
    (before after : State Symbol Guard) (valid : InternedConstructorTemplates.Valid before)
    (value : Value Symbol Guard)
    (returned : (run (edit meet (first :: rest) (.node entry edges depth free)) before).1 = some value)
    (growth : Grows (run (edit meet (first :: rest) (.node entry edges depth free)) before).2 after) :
    run (makeNode (edges.map (rebuild after (editedChild meet (first :: rest) after)))) after = (value, after) := by
  let edited := run (editEdges meet (first :: rest) edges) before
  obtain ⟨rows, found⟩ := editEdges_returns meet (first :: rest) edges ordinary before
  have editedValid : InternedConstructorTemplates.Valid edited.2 :=
    (InternedConstructorTemplates.run_correct _ before valid).1
  have nodeGrowth : Grows (run (makeNode rows) edited.2).2 after := by
    simpa only [edit, noRoot, bindOptional, run_bind, found, run] using growth
  have edgeGrowth : Grows edited.2 after := grows_trans
    (InternedConstructorTemplates.run_correct _ edited.2 editedValid).2 nodeGrowth
  have readback := editEdges_readback meet (first :: rest) edges ordinary before after valid edgeGrowth
  have rowsSame : rows = edges.map (rebuild after (editedChild meet (first :: rest) after)) :=
    Option.some.inj (found.symm.trans readback)
  have repeated := replay (makeNode rows) edited.2 after editedValid nodeGrowth
  have actual : (run (makeNode rows) edited.2).1 = value := by
    apply Option.some.inj
    simpa only [edit, noRoot, bindOptional, run_bind, found, run] using returned
  rw [← rowsSame, repeated, actual]

end MicroCFTA.EqualityLeafProjectionEditClosed
