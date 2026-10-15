import MicroCFTA.SourceEqualityProjectionGraph
import MicroCFTA.SourceEqualityRequiredWorker

/-!
# Instrumented source getPath execution

Worker and row-read bounds are proof parameters. Pending records, unresolved
references, and the two exhausted bounds retain different outcomes.
Closed union reads each operand and then constructs one ordinary node.
-/
namespace MicroCFTA.SourceEqualityProjectionWorker
open InternedConstructorTemplates SourceEqualityProjectionGraph
open SourceEqualityRequiredWorker (Result work head)

/-- Read every closed union operand in order with the same row-read bound. -/
def readAll [DecidableEq (EdgeKey Symbol Guard)] (readFuel : Nat) : List (Value Symbol Guard) →
    State Symbol Guard → Result Symbol Guard (List (EdgeValue Symbol Guard))
  | [], state => .done [] state
  | value :: values, state =>
      match MergedFreshOrdinaryExposure.nodeEdges readFuel value state with
      | .done edges middle => (readAll readFuel values middle).bind fun more after => .done (edges ++ more) after
      | .pending key after => .pending key after
      | .unresolved name after => .unresolved name after
      | .exhausted after => .exhausted .head after

/-- Execute the source union branch on closed operands. -/
def union [DecidableEq (EdgeKey Symbol Guard)] (readFuel : Nat) (values : List (Value Symbol Guard))
    (state : State Symbol Guard) : Result Symbol Guard (Value Symbol Guard) :=
  (readAll readFuel values state).bind fun edges after => work (makeNode edges) after

/-- Map only existing row children, in the original source row order. -/
def rows (recur : Value Symbol Guard → State Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (index : Int) : List (EdgeValue Symbol Guard) → State Symbol Guard → Result Symbol Guard (List (Value Symbol Guard))
  | [], state => .done [] state
  | edge :: edges, state => match select edge.children index with
    | none => rows recur index edges state
    | some child => (recur child state).bind fun value middle =>
        (rows recur index edges middle).bind fun values after => .done (value :: values) after

/-- Execute the actual source branches with separate worker and row-read proof bounds. -/
def project [DecidableEq (EdgeKey Symbol Guard)] : Nat → Nat → List Int → Value Symbol Guard →
    State Symbol Guard → Result Symbol Guard (Value Symbol Guard)
  | 0, _, _, _, state => .exhausted .worker state
  | _ + 1, _, [], value, state => .done value state
  | fuel + 1, readFuel, index :: path, value, state => match value with
    | .empty => .done .empty state
    | .reference name => .unresolved name state
    | .node _ edges _ _ => (rows (project fuel readFuel path) index edges state).bind fun values after => union readFuel values after
    | .mu .. | .union .. => (head readFuel value state).bind fun exposed after => project fuel readFuel (index :: path) exposed after

/-- Forest root projection executes union; an absent signed child returns EmptyNode. -/
def forest [DecidableEq (EdgeKey Symbol Guard)] (fuel readFuel : Nat) (path : List Int)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard) : Result Symbol Guard (Value Symbol Guard) :=
  match path with
  | [] => union readFuel values state
  | index :: path => match select values index with
    | none => .done .empty state
    | some value => project fuel readFuel path value state

end MicroCFTA.SourceEqualityProjectionWorker
