import MicroCFTA.SourceCurrentFilteredNonemptyFusion

namespace MicroCFTA.FilteredFusionSearch
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedStoredSubstitution (Environment)
open InternedBinderProtocol (Reference)

set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

private def val (outcome : Outcome Nat Bool (Value Nat Bool)) : Value Nat Bool :=
  match outcome with | .done value _ => value | .pending .. => .empty
private def done (outcome : Outcome Nat Bool (Value Nat Bool)) : Bool :=
  match outcome with | .done .. => true | .pending .. => false
private def n (children : List (Syntax Nat Bool)) : Syntax Nat Bool := .node [.mk 7 false children]
private def programs : List (Syntax Nat Bool) := [
  .binder true (n [.var 0,.var 1]),
  .binder true (.union [.var 0,n [.var 1]]),
  .binder true (.union [.var 0,n [.var 0,.var 1]]),
  .binder true (.union [n [.var 0],n [.var 1]]),
  .binder false (n [.var 0,.var 1]),
  .binder true (n [.var 0,.binder true (n [.var 0,.var 1,.var 2])]),
  .binder true (.union [.var 0,.binder true (n [.var 0,.var 1,.var 2])]),
  .binder true (.union [n [.var 0,.var 1],.binder true (.union [.var 0,n [.var 1,.var 2,.var 4]])])]
private def baseSource : Syntax Nat Bool := .binder false
  (.node [.mk 9 false [.binder false (n [.var 0,.var 1])]])
private def baseRun := build baseSource [] empty
private def base := baseRun.state
private def replacement := val baseRun
private def rootBody : Value Nat Bool := match replacement with | .mu _ body _ _ => body | _ => .empty
private def external : Reference := match replacement with | .mu entry _ _ _ => .interned entry.identity | _ => .depth
private def fixed : Value Nat Bool := (children rootBody)[0]?.getD .empty
private def names (pattern side : Nat) : Reference × Reference :=
  if pattern = 0 then (.uninterned (2*side),.uninterned (2*side+1))
  else (.depth,.uninterned (2*side))
private def lexical (pattern side : Nat) : List (Value Nat Bool) :=
  [.reference (names pattern side).1,.reference (names pattern side).2,fixed]
private def maps (pattern side mode : Nat) : Environment Nat Bool := fun name =>
  if name = (names pattern side).1 then some (if mode / 2 = 0 then .empty else replacement)
  else if name = (names pattern side).2 then some (if mode % 2 = 0 then .empty else replacement)
  else if name = external then some .empty else none
private def older : Syntax Nat Bool → Syntax Nat Bool
  | .binder smart body => .binder smart (.union [body,.empty])
  | expression => expression
private def mu (value : Value Nat Bool) : Bool := match value with | .mu .. => true | _ => false

private def test (expression : Syntax Nat Bool) (pattern mode : Nat) : Bool × Bool × Bool × Bool × Bool :=
  let seedFirst := build (older expression) (lexical pattern 0) base
  let seedSecond := build (older expression) (lexical pattern 1) seedFirst.state
  let first := build expression (lexical pattern 0) seedSecond.state
  let second := build expression (lexical pattern 1) first.state
  let filteredFirst := run (withoutSelfReference .depth (val first)) second.state
  let left := execute filteredFirst.1 (maps pattern 0 mode) filteredFirst.2
  let filteredSecond := run (withoutSelfReference .depth (val second)) left.state
  let right := execute filteredSecond.1 (maps pattern 1 mode) filteredSecond.2
  (done seedFirst && done seedSecond && done first && done second && done left && done right,
    (val left).referenceOf == .empty,(val right).referenceOf == .empty,
    (val seedFirst).referenceOf == (val first).referenceOf &&
      (val seedSecond).referenceOf == (val second).referenceOf,
    mu (val first) && mu (val second))

#eval (done baseRun, fixed.free.all (fun name => name == external))
#eval (0, 0, 0, test (programs[0]!) 0 0)
#eval (0, 0, 1, test (programs[0]!) 0 1)
#eval (0, 1, 0, test (programs[0]!) 1 0)
#eval (0, 1, 1, test (programs[0]!) 1 1)
#eval (3, 0, 0, test (programs[3]!) 0 0)
#eval (3, 0, 1, test (programs[3]!) 0 1)
#eval (3, 1, 0, test (programs[3]!) 1 0)
#eval (3, 1, 1, test (programs[3]!) 1 1)
#eval (5, 0, 0, test (programs[5]!) 0 0)
#eval (5, 0, 1, test (programs[5]!) 0 1)
#eval (5, 1, 0, test (programs[5]!) 1 0)
#eval (5, 1, 1, test (programs[5]!) 1 1)

end MicroCFTA.FilteredFusionSearch
