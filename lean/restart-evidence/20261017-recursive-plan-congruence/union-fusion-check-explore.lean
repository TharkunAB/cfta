import MicroCFTA.SourceCurrentStoredSubstitutionOrigins
import MicroCFTA.SourceCurrentStoredReconstructionReplay

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

namespace MicroCFTA.UnionFusionCheck
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome work)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedBinderProtocol (Reference)

def expression : Syntax Nat Bool :=
  .binder false (.binder false (.node [.mk 9 true
    [.union [.node [.mk 0 true []], .binder false (.var 2)],
     .var 0, .node [.mk 1 true []]]]))
def built := build expression [] empty
def root : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
def heap := built.state
def muBody : Value Nat Bool → Value Nat Bool | .mu _ body _ _ => body | _ => .empty
def own : Value Nat Bool → Reference | .mu entry _ _ _ => .interned entry.identity | _ => .depth
def children : List (Value Nat Bool) := match muBody (muBody root) with
  | .node _ (.mk _ values :: _) _ _ => values
  | _ => []
def members := children.take 2
def replacement : Value Nat Bool := children[2]?.getD .empty
def environment : InternedStoredSubstitution.Environment Nat Bool :=
  fun name => if name = own root then some replacement else none
def normalized := run (makeUnion members) heap
def first := execute normalized.1 environment normalized.2
def left : Value Nat Bool := match first with | .done value _ => value | .pending .. => .empty

def memberCalls (values : List (Value Nat Bool)) (state : State Nat Bool) : Outcome Nat Bool (List (Value Nat Bool)) :=
  match values with
  | [] => .done [] state
  | value :: rest => (execute value environment state).bind fun output middle =>
      (memberCalls rest middle).bind fun outputs after => .done (output :: outputs) after

def second := (memberCalls members first.state).bind fun outputs after => work (makeUnion outputs) after
def right : Value Nat Bool := match second with | .done value _ => value | .pending .. => .empty

def shape (value : Value Nat Bool) : List (Nat × List Nat) := (unionMembers value).map fun member =>
  match member with
  | .node _ rows _ _ => (0, rows.map fun row => row.entry.key.symbol)
  | .reference _ => (1, [])
  | .mu .. => (2, [])
  | .union .. => (3, [])
  | .empty => (4, [])

#eval (root.referenceOf, own root, children.length, shape normalized.1,
  left.referenceOf, right.referenceOf, shape left, shape right,
  normalized.2.nodes.next, first.state.nodes.next, second.state.nodes.next)
#eval (left, right)
end MicroCFTA.UnionFusionCheck
