import MicroCFTA.SourceRecursiveIntersectionNative
import MicroCFTA.SourceCurrentConstrainedCapGuardDepth
import MicroCFTA.SourceCurrentConstrainedCapNativeOccurrenceCompile

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace MicroCFTA.JointNativeProbe
open Cache InternedConstructorTemplates InternedNestedConstruction InternedProbeProvenance
open SourceRecursiveIntersectionCode SourceRecursiveIntersectionControl
local notation "Heap" => InternedConstructorTemplates.State Nat Bool
local notation "V" => Value Nat Bool
private abbrev S := Syntax Nat Bool
private def leaf (guard : Bool) : S := .node [.mk 0 guard []]
private def unary (guard : Bool) (child : S) : S := .node [.mk 1 guard [child]]
private def loops : List (S × S) :=
  [(.binder false (.var 0), leaf false),
   (.binder false (.union [leaf true, unary true (.var 0)]), unary false (leaf true))]
private def selected (index : Nat) := (loops[index]?).getD (.empty, .empty)
private def first (index : Nat) := InternedFreshOrdinaryConstruction.build (selected index).1 [] (empty : Heap)
private def left (index : Nat) : V := match first index with | .done value _ => value | .pending .. => .empty
private def second (index : Nat) := InternedFreshOrdinaryConstruction.build (selected index).2 [] (first index).state
private def right (index : Nat) : V := match second index with | .done value _ => value | .pending .. => .empty
private def source (index : Nat) := (second index).state
private def initial (index : Nat) := SourceRecursiveIntersectionThunks.initial 8
  (⟨source index, Cache.emptyState⟩ : SourceRecursiveIntersectionKernel.Machine Nat Bool)
private def code (index : Nat) := requestNode IntersectionEmptyDomain.emptyDomain (right index) (left index)
private def cold (index : Nat) := SourceRecursiveIntersectionNative.execute true Bool.and 128 (code index) (initial index)
private def tag {A} : SourceRecursiveIntersectionNative.Outcome 8 Nat Bool A → Nat
  | .done .. => 0 | .yielded .. => 1 | .failed .. => 2 | .blocked .. => 3
private def result (index : Nat) : V := match cold index with | .done value _ => value | _ => .empty
private def warm (index : Nat) := SourceRecursiveIntersectionNative.execute true Bool.and 2 (code index) (cold index).state
private def describe (index : Nat) :=
  (index, tag (cold index), (result index).referenceOf,
    (source index).nodes.next, (cold index).state.machine.heap.nodes.next,
    (cold index).state.nodes.next, (cold index).state.edges.next, tag (warm index))
#eval describe 0
#eval describe 1
end MicroCFTA.JointNativeProbe
