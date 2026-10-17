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

namespace MicroCFTA.UnionFusionSmall
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome work)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedBinderProtocol (Reference)

private def expression : Syntax Nat Bool := .node [.mk 9 true
  [.union [.node [.mk 0 true []], .binder false (.var 1)],
   .var 1, .node [.mk 1 true []]]]
private def inputs : List (Value Nat Bool) := [.reference (.uninterned 0), .reference (.uninterned 1)]
private def children : Value Nat Bool → List (Value Nat Bool)
  | .node _ (.mk _ values :: _) _ _ => values
  | _ => []
private def calls (environment : InternedStoredSubstitution.Environment Nat Bool)
    (values : List (Value Nat Bool)) (state : State Nat Bool) : Outcome Nat Bool (List (Value Nat Bool)) :=
  match values with
  | [] => .done [] state
  | value :: rest => (execute value environment state).bind fun output middle =>
      (calls environment rest middle).bind fun outputs after => .done (output :: outputs) after
private def shape (value : Value Nat Bool) : List (Nat × List Nat) := (unionMembers value).map fun member =>
  match member with
  | .node _ rows _ _ => (0, rows.map fun row => row.entry.key.symbol)
  | .reference _ => (1, [])
  | .mu .. => (2, [])
  | .union .. => (3, [])
  | .empty => (4, [])
private def trial :=
  match build expression inputs empty with
  | .pending .. => none
  | .done root heap =>
      let original := (children root).take 2
      let replacement : Value Nat Bool := (children root)[2]?.getD Value.empty
      let environment := fun name => if name = Reference.uninterned 0 then some replacement else none
      let normalized := run (makeUnion original) heap
      match execute normalized.1 environment normalized.2 with
      | .pending .. => none
      | .done left middle =>
          match (calls environment original middle).bind fun values next => work (makeUnion values) next with
          | .pending .. => none
          | .done right after => some (shape normalized.1, shape left, shape right,
              left.referenceOf == right.referenceOf, normalized.2.nodes.next, middle.nodes.next, after.nodes.next)
#eval trial
end MicroCFTA.UnionFusionSmall
