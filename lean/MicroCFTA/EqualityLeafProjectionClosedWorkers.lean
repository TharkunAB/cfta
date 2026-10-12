import MicroCFTA.EqualityLeafProjectionRequireCorrespondence

/-!
# Closed component requests in actual optional worker traces

A successful completed worker gives allocation-free component requests.
The final parent constructor replays the complete returned record and the
same cache, not only an equal decoded value.
-/
namespace MicroCFTA.EqualityLeafProjectionClosedWorkers
open InternedConstructorTemplates InternedRecordCoherence
open EqualityLeafProjectionSyntax (Path descend fits)
open EqualityLeafProjectionWorkers EqualityLeafProjectionPhysical
open EqualityLeafProjectionRepresentation EqualityLeafProjectionWorkerReadback

/-- Any actual completed request remains allocation-free after later cache growth. -/
theorem work_grows [DecidableEq (EdgeKey Symbol Guard)] (work : Work Symbol Guard Result)
    (before after : State Symbol Guard) (valid : InternedConstructorTemplates.Valid before)
    (result : Result) (closed : run work before = (result, before)) (growth : Grows before after) :
    run work after = (result, after) := by
  have requestGrowth : Grows (run work before).2 after := by rw [closed]; exact growth
  simpa only [closed] using replay work before after valid requestGrowth

/-- A successful closed optional bind forces a successful closed first request. -/
theorem optional_bind_closed [DecidableEq (EdgeKey Symbol Guard)]
    (first : Work Symbol Guard (Option First)) (next : First → Work Symbol Guard (Option Result))
    (state : State Symbol Guard) (valid : InternedConstructorTemplates.Valid state)
    (result : Result) (closed : run (bindOptional first next) state = (some result, state)) :
    ∃ value, run first state = (some value, state) ∧ run (next value) state = (some result, state) := by
  obtain ⟨value, firstClosed, nextClosed⟩ := bind_closed _ _ state valid (some result) closed
  cases value with
  | none =>
      have impossible := congrArg (fun pair : Option Result × State Symbol Guard => pair.1) nextClosed
      cases impossible
  | some value => exact ⟨value, firstClosed, nextClosed⟩

/-- Successful closed child requirements expose the exact original head and tail requests. -/
theorem children_decompose [DecidableEq (EdgeKey Symbol Guard)]
    (paths : List Path) (index : Nat) (child : Value Symbol Guard) (rest : List (Value Symbol Guard))
    (state : State Symbol Guard) (valid : InternedConstructorTemplates.Valid state)
    (values : List (Value Symbol Guard))
    (closed : run (requireChildren paths index (child :: rest)) state = (some values, state)) :
    ∃ value tail, values = value :: tail ∧ run (require (descend paths index) child) state = (some value, state) ∧
      run (requireChildren paths (index + 1) rest) state = (some tail, state) := by
  rw [requireChildren] at closed
  obtain ⟨value, headClosed, remaining⟩ := optional_bind_closed _ _ state valid values closed
  obtain ⟨tail, tailClosed, actual⟩ := optional_bind_closed _ _ state valid values remaining
  have same : value :: tail = values := Option.some.inj (congrArg Prod.fst actual)
  exact ⟨value, tail, same.symm, headClosed, tailClosed⟩

/-- A successful selected original row exposes its closed child, edge, and tail requests. -/
theorem edges_decompose [DecidableEq (EdgeKey Symbol Guard)]
    (paths : List Path) (entry : Cache.Interned (EdgeKey Symbol Guard)) (children : List (Value Symbol Guard))
    (rest : List (EdgeValue Symbol Guard)) (selected : fits paths children.length = true)
    (state : State Symbol Guard) (valid : InternedConstructorTemplates.Valid state)
    (values : List (EdgeValue Symbol Guard))
    (closed : run (requireEdges paths (.mk entry children :: rest)) state = (some values, state)) :
    ∃ nodes edge tail, values = edge :: tail ∧ run (requireChildren paths 0 children) state = (some nodes, state) ∧
      run (makeEdge entry.key.symbol entry.key.constraint nodes) state = (edge, state) ∧
      run (requireEdges paths rest) state = (some tail, state) := by
  rw [requireEdges, ite_eq_left selected] at closed
  obtain ⟨nodes, childClosed, remaining⟩ := optional_bind_closed _ _ state valid values closed
  obtain ⟨edge, edgeClosed, tailRequest⟩ := bind_closed _ _ state valid (some values) remaining
  obtain ⟨tail, tailClosed, actual⟩ := optional_bind_closed _ _ state valid values tailRequest
  have same : edge :: tail = values := Option.some.inj (congrArg Prod.fst actual)
  exact ⟨nodes, edge, tail, same.symm, childClosed, edgeClosed, tailClosed⟩

/-- The actual required parent constructor replays the already returned complete record
without allocation in every common cache retaining the completed worker. -/
theorem require_parent_replay [DecidableEq (EdgeKey Symbol Guard)]
    (paths : List Path) (proper : fits paths 0 = false)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Guard))
    (depth : Nat) (free : List InternedBinderProtocol.Reference) (ordinary : OrdinaryEdges edges)
    (before after : State Symbol Guard) (valid : InternedConstructorTemplates.Valid before)
    (value : Value Symbol Guard) (returned : (run (require paths (.node entry edges depth free)) before).1 = some value)
    (growth : Grows (run (require paths (.node entry edges depth free)) before).2 after) :
    run (makeNode ((edges.filter (fun edge => fits paths edge.children.length)).map
      (rebuild after (requiredChild paths after)))) after = (value, after) := by
  let required := run (requireEdges paths edges) before
  obtain ⟨rows, found⟩ := requireEdges_returns paths edges ordinary before
  have requiredValid : InternedConstructorTemplates.Valid required.2 :=
    (InternedConstructorTemplates.run_correct _ before valid).1
  have nodeGrowth : Grows (run (makeNode rows) required.2).2 after := by
    simpa only [require, proper, Bool.false_eq_true, ↓reduceIte, bindOptional, run_bind, found, run] using growth
  have edgeGrowth : Grows required.2 after := grows_trans
    (InternedConstructorTemplates.run_correct _ required.2 requiredValid).2 nodeGrowth
  have readback := requireEdges_readback paths edges ordinary before after valid edgeGrowth
  have rowsSame : rows = (edges.filter (fun edge => fits paths edge.children.length)).map (rebuild after (requiredChild paths after)) :=
    Option.some.inj (found.symm.trans readback)
  have repeated := replay (makeNode rows) required.2 after requiredValid nodeGrowth
  have actual : (run (makeNode rows) required.2).1 = value := by
    apply Option.some.inj
    simpa only [require, proper, Bool.false_eq_true, ↓reduceIte, bindOptional, run_bind, found, run] using returned
  rw [← rowsSame, repeated, actual]

end MicroCFTA.EqualityLeafProjectionClosedWorkers
