import MicroCFTA.InternedNestedProbeCostBoundary
import MicroCFTA.InternedNestedMissReadback

/-!
# Actual ordinary levels can change after a fresh captured input

One unused local shifts the existing nested cleanup example. An outer
fresh input changes the inner Depth callback's cached depth from zero to
one. The ordinary callback therefore receives a different Unint level.
The closed embedding completes. This example does not exhibit pending
readback.
-/
namespace MicroCFTA.InternedOrdinaryLevelBoundary
open InternedConstructorTemplates InternedNestedConstruction InternedNestedMissReadback
open InternedBinderProtocol (Reference NodeRef)

/-- The extra local is unused; the live inner binder reads the outer local. -/
def innerBody : Syntax Nat Unit := .union [
  .node [.mk 2 () [.binder true (.node [.mk 0 () [.var 3], .mk 0 () [.var 4]]), .empty]],
  .node [.mk 1 () [.binder true (.node [.mk 0 () [.var 0], .mk 0 () [.var 2], .mk 0 () [.var 3], .mk 0 () [.var 4]])]]]

/-- The two fixed captures are the ordinary source sentinels. -/
def captures : List (Value Nat Unit) := [.reference .depth, .reference (.uninterned 0)]

/-- Follow the actual outer probes and reservation, then observe the two inner Depth prefixes. -/
def comparedDepths : Option (Nat × Nat × Nat) :=
  match callback (.binder false innerBody) captures .depth empty with
  | .pending .. => none
  | .done depth afterDepth =>
      match callback (.binder false innerBody) captures (.uninterned depth.depth) afterDepth with
      | .pending .. => none
      | .done ordinary cut =>
          let key := muKey depth ordinary
          match cut.nodes.table key with
          | some _ => none
          | none =>
              let entry := Cache.intern cut.nodes key
              let allocated := {cut with nodes := entry.2}
              match callback innerBody (.reference .depth :: captures) .depth empty,
                  callback innerBody (.reference (.interned entry.1.identity) :: captures) .depth allocated with
              | .done first _, .done second _ => some (entry.1.identity, first.depth, second.depth)
              | _, _ => none

/-- The same inner source body sees only one fresh captured-name change, yet computes different ordinary levels. -/
theorem different_actual_levels : comparedDepths = some (9, 0, 1) := by
  set_option maxRecDepth 20000 in
  set_option cbv.maxSteps 20000000 in cbv

/-- The closed wrapper supplies both captures through actual outer probes. -/
def expression : Syntax Nat Unit := .binder true (.binder true
  (.node [.mk 3 () [.binder false (.binder false innerBody), .empty]]))

/-- Execute the complete closed source expression from empty caches. -/
def result := build expression [] (empty : State Nat Unit)

/-- Inspect the inner Depth callbacks stored in each of the outer raw Mu's three results. -/
def nestedDepths : Value Symbol Guard → Option (Nat × Nat × Nat)
  | .mu _ (.mu _ _ actualDepth _) (.mu _ _ depthDepth _) (.mu _ _ ordinaryDepth _) =>
      some (actualDepth.depth, depthDepth.depth, ordinaryDepth.depth)
  | _ => none

/-- Select the actual outer raw reservation made in the closed ordinary enclosing probe. -/
def selectedDepths : Option (Nat × Nat × Nat) := do
  let key ← result.state.nodes.issued 28
  let value ← result.state.nodeRecords key
  nestedDepths value

/-- The closed cache retains the same ordinary-level mismatch. -/
theorem closed_actual_levels : selectedDepths = some (1, 0, 1) := by
  set_option maxRecDepth 20000 in
  set_option cbv.maxSteps 40000000 in cbv

/-- Every variable belongs to the lexical scope in this closed fixture. -/
theorem expression_scoped : Scoped 0 expression := by
  simp [expression, innerBody, Scoped, EdgesScoped, ManyScoped]

/-- The example completes with an empty root after its discarded child has run. -/
theorem complete_empty : (match result with | .done value _ => some value.referenceOf | .pending .. => none) = some .empty := by
  set_option maxRecDepth 20000 in
  set_option cbv.maxSteps 40000000 in cbv

end MicroCFTA.InternedOrdinaryLevelBoundary
