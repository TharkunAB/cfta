import MicroCFTA.InternedFreshOrdinarySemanticOrigins
import MicroCFTA.InternedFreshOrdinaryDepthHeap
import MicroCFTA.SourceRecursiveIntersectionSourceProfile

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace MicroCFTA.BinderOriginsSearch
open InternedConstructorTemplates InternedNestedConstruction
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryDepthHeap
open InternedBinderProtocol

def leaf : Syntax Nat Unit := .node [.mk 0 () []]

def casesAt : Nat → Nat → List (Syntax Nat Unit)
  | 0, count => .empty :: leaf :: (List.range count).map Syntax.var
  | depth + 1, count =>
      let smaller := casesAt depth count
      let nested := casesAt depth (count + 1)
      smaller ++ smaller.map (fun child => .node [.mk 1 () [child]]) ++
        smaller.flatMap (fun child => [.union [child, leaf], .union [leaf, child]]) ++
        nested.flatMap (fun child => [.binder true child, .binder false child])

def errors (state : State Nat Unit) : List (Nat × NodeRef × NodeRef) :=
  (SourceRecursiveIntersectionSourceProfile.nodePayloads state).filterMap fun value =>
    match value with
    | .mu entry body depth ordinary =>
        if usesLocal depth ordinary then none else
        let expected := if ordinary.referenceOf == .ref (.uninterned (ordinaryLevel depth)) then
          NodeRef.empty else ordinary.referenceOf
        let actual := (finish true (.mu entry body depth ordinary)).referenceOf
        if actual == expected then none else some (entry.identity, actual, expected)
    | _ => none

def inspect (expression : Syntax Nat Unit) : Nat × Nat × List (Nat × NodeRef × NodeRef) :=
  let result := build expression [] empty
  let payloads := SourceRecursiveIntersectionSourceProfile.nodePayloads result.state
  (payloads.length, (payloads.filter fun value => match value with
    | .mu _ _ depth ordinary => !usesLocal depth ordinary
    | _ => false).length, errors result.state)

def summary (depth : Nat) : Nat × Nat × Nat × List (Nat × List (Nat × NodeRef × NodeRef)) :=
  let cases := casesAt depth 0
  let results := cases.map inspect
  (cases.length, (results.map (fun result => result.1)).sum,
    (results.map (fun result => result.2.1)).sum,
    (List.zipIdx results).filterMap fun (result, index) =>
      if result.2.2.isEmpty then none else some (index, result.2.2))

#eval summary 3
end MicroCFTA.BinderOriginsSearch
