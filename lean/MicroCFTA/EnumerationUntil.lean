import MicroCFTA.EnumerationDriver

/-!
# Parameterized enumeration with narrowing and partial stopping

The actions use the existing graph, state, and bounded enumeration monad.
The scheduler is the existing modeled slot scan. Cached-source scheduling
requires a separate correspondence argument.
-/

namespace MicroCFTA.EnumerationUntil
open Language Fragments EnumerationState EnumerationDriver

variable {Symbol Guard OracleState : Type}

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- Expand a node with its actual suspended constraints. -/
abbrev NodeExpansion (Symbol Guard : Type) :=
  List Suspended → Nat → EnumerateM Symbol Guard (Fragment Symbol)

/-- Prepare every child in order and retain the selected edge's residual. -/
def enumerateEdgeWith (prepareAt : Nat → NodeExpansion Symbol Guard) :
    Nat → List Suspended → EnumerationState.Edge Symbol Guard →
      EnumerateM Symbol Guard (Fragment Symbol)
  | 0, _, _ => failure .fuelExhausted
  | fuel + 1, scs, edge => do
      require (arityAllows edge.children.length scs)
      let added ← edge.equalities.mapM suspend
      let children ← edge.children.zipIdx |>.mapM fun (node, index) =>
        prepareAt fuel (descendScs index (scs ++ added)) node
      let fragment := Fragment.node edge.symbol children
      match edge.residual with
      | none => pure ()
      | some guard => modify fun state =>
          {state with obligations := (guard, fragment) :: state.obligations}
      pure fragment

/-- Defer an ordinary child and install its complete suspended list. -/
def prepareShallowChild (graph : Graph Symbol Guard) : Nat → NodeExpansion Symbol Guard
  | 0, _, _ => failure .fuelExhausted
  | fuel + 1, scs, node => do
      match graph.node node with
      | .alternatives _ =>
          if scs.any (fun sc => EqualityTrie.isTerminal sc.trie) then
            enumerateNode graph (fuel + 1) scs node
          else
            let uv ← allocate (some node)
            setValue uv (.unenumerated (some node) scs)
            pure (.hole uv)
      | _ => enumerateNode graph (fuel + 1) scs node

/-- Expand the selected ordinary root once instead of deferring that root. -/
def enumerateShallowHere (graph : Graph Symbol Guard) : Nat → NodeExpansion Symbol Guard
  | 0, _, _ => failure .fuelExhausted
  | fuel + 1, scs, node => do
      match graph.node node with
      | .alternatives edges =>
          if scs.any (fun sc => EqualityTrie.isTerminal sc.trie) then
            enumerateNode graph (fuel + 1) scs node
          else
            enumerateEdgeWith (prepareShallowChild graph) fuel scs (← choose edges)
      | _ => enumerateNode graph (fuel + 1) scs node

/-- Retain ancestry and write the fragment to the captured representative. -/
def enumerateOutWith (graph : Graph Symbol Guard) (expand : NodeExpansion Symbol Guard)
    (fuel uv : Nat) : EnumerateM Symbol Guard (Fragment Symbol) := do
  match ← getValue (fuel + 1) uv with
  | .unenumerated (some node) scs =>
      let root ← representative (fuel + 1) uv
      let ancestry := (← get).recursionAncestry root
      modify fun state => {state with expansionAncestry := (
        match graph.node node with
        | .recursive _ => (recursionKey node scs :: ancestry).eraseDups
        | _ => ancestry)}
      let fragment ← expand scs
        (match graph.node node with | .recursive body => body | _ => node)
      modify fun state => {state with expansionAncestry := []}
      setValue root (.enumerated fragment)
      pure fragment
  | _ => reject

/-- List every candidate before blocked representatives are removed. -/
def remaining (graph : Graph Symbol Guard) (state : State Symbol Guard) : List Nat :=
  (state.values.zipIdx.filter fun entry => candidate graph entry.1).map Prod.snd

/-- Retain the full stop, narrowing, ancestry, and two-oracle control flow. -/
def enumerateUntil (graph : Graph Symbol Guard)
    (stop : Option (OracleState → Nat → Bool))
    (narrow : OracleState → Nat → Nat → Nat)
    (expandAt : Nat → NodeExpansion Symbol Guard)
    (order : OracleState → List Nat → Option Nat)
    (oracle : Oracle Symbol Guard OracleState) :
    Nat → OracleState → EnumerateM Symbol Guard (Option OracleState)
  | 0, _ => failure .fuelExhausted
  | fuel + 1, oracleState => do
      let step : EnumerateM Symbol Guard (Option OracleState) := do
        let next := pickNext (order oracleState) (← findExpandable graph (fuel + 1))
        match next with
        | .done => pure none
        | .stuck => reject
        | .expand uv =>
            match ← getValue (fuel + 1) uv with
            | .unenumerated (some node) scs =>
                let repeated ← checkRepeated graph (fuel + 1) uv node scs
                if repeated then
                  enumerateUntil graph stop narrow expandAt order oracle fuel oracleState
                else
                  let narrowed := narrow oracleState uv node
                  match graph.node narrowed with
                  | .empty => reject
                  | _ =>
                      if narrowed = node then pure ()
                      else
                        let root ← representative (fuel + 1) uv
                        setValue root (.unenumerated (some narrowed) scs)
                      let (beforeReject, beforeState) ← oracle oracleState uv (.inr narrowed)
                      require (!beforeReject)
                      let fragment ← enumerateOutWith graph (expandAt (fuel + 1)) (fuel + 1) uv
                      let (afterReject, afterState) ← oracle beforeState uv (.inl fragment)
                      require (!afterReject)
                      enumerateUntil graph stop narrow expandAt order oracle fuel afterState
            | _ => reject
      match stop with
      | none => step
      | some rule =>
          let pending := remaining graph (← get)
          if !pending.isEmpty && pending.all (rule oracleState) then
            pure (some oracleState)
          else step

/-- Read the root fragment and retain the original root hole on pending work. -/
def rootFragment (fuel : Nat) : EnumerateM Symbol Guard (Fragment Symbol) := do
  match ← getValue (fuel + 1) 0 with
  | .enumerated fragment => pure fragment
  | _ => pure (.hole 0)

/-! The same bound supplies the driver and partial renderer. The root lookup
uses that bound plus one, as the existing slot-expansion actions do. -/
/-- Execute the public shallow path and retain partial terms, errors, and states. -/
def partialRunsUntil (graph : Graph Symbol Guard)
    (stop : OracleState → Nat → Bool) (narrow : OracleState → Nat → Nat → Nat)
    (order : OracleState → List Nat → Option Nat) (oracle : Oracle Symbol Guard OracleState)
    (fuel root : Nat) (oracleState : OracleState) :
    List (Except Error (Term (PartialSymbol Symbol) × State Symbol Guard)) :=
  let action : EnumerateM Symbol Guard (Term (PartialSymbol Symbol)) := do
    let _ ← enumerateUntil graph (some stop) narrow (enumerateShallowHere graph) order oracle fuel oracleState
    let fragment ← rootFragment fuel
    expandPartial graph fuel fragment
  action (initial root)

/-- The parameterized worker retains the complete eager worker action. -/
theorem enumerateOutWith_eager (graph : Graph Symbol Guard) (fuel uv : Nat) :
    enumerateOutWith graph (enumerateNode graph fuel) fuel uv = enumerateOut graph fuel uv := rfl

/-- Eager child preparation retains the old edge action at the same bound. -/
theorem enumerateEdgeWith_eager (graph : Graph Symbol Guard) (fuel : Nat)
    (scs : List Suspended) (edge : EnumerationState.Edge Symbol Guard) :
    enumerateEdgeWith (fun remaining => enumerateNode graph remaining) fuel scs edge =
      enumerateEdge graph fuel scs edge := by
  cases fuel <;> rfl

/-- A positive bounded call stops before scheduling when all candidates pass the rule. -/
theorem stop_all (graph : Graph Symbol Guard) (rule : OracleState → Nat → Bool)
    (narrow : OracleState → Nat → Nat → Nat) (expandAt : Nat → NodeExpansion Symbol Guard)
    (order : OracleState → List Nat → Option Nat) (oracle : Oracle Symbol Guard OracleState)
    (fuel : Nat) (oracleState : OracleState) (before : State Symbol Guard)
    (nonempty : (remaining graph before).isEmpty = false)
    (accepted : (remaining graph before).all (rule oracleState) = true) :
    enumerateUntil graph (some rule) narrow expandAt order oracle (fuel + 1) oracleState before =
      [.ok (some oracleState, before)] := by
  simp only [enumerateUntil]
  rw [EnumerationCorrectness.bind_single (get : EnumerateM Symbol Guard (State Symbol Guard))
    _ before before before rfl]
  simp only [nonempty, accepted, Bool.not_false, Bool.true_and, ↓reduceIte]
  rfl

end MicroCFTA.EnumerationUntil
