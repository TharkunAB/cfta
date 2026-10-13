import MicroCFTA.InternedOrdinaryLevelBoundary

/-!
# A changed ordinary level can alias an original live capture

This closed fixture changes an inner computed level from zero to one.
The active ancestor's original Depth probe already contains Unint 1.
The expression completes. Probe support alone does not exclude the
ordinary alias case of the general pending proof.
-/
namespace MicroCFTA.InternedOrdinaryCaptureBoundary
open InternedConstructorTemplates InternedNestedConstruction InternedNestedMissReadback
open InternedBinderProtocol (Reference NodeRef)
open InternedOrdinaryLevelBoundary (innerBody)

/-- The active ancestor retains an extra captured ordinary name. -/
def ancestorBody : Syntax Nat Unit := .union [.binder false innerBody, .var 3]

/-- The outer raw binder gives the outer ordinary callback level one. -/
def expression : Syntax Nat Unit := .binder true (.union [
  .binder true (.binder true (.node [.mk 3 () [.binder false ancestorBody, .empty]])),
  .binder false (.var 0)])

/-- Execute the closed fixture from empty source caches. -/
def result := build expression [] (empty : State Nat Unit)

/-- Read the inner probe level retained by an outer union result. -/
def innerDepth : Value Symbol Guard → Option Nat
  | .union _ (.mu _ _ depth _ :: _) _ _ => some depth.depth
  | _ => none

/-- Read the changed levels and the original probe's support from one stored ancestor. -/
def observe : Value Symbol Guard → Option (Nat × Nat × Bool)
  | .mu _ body depth _ => do
      let first ← innerDepth depth
      let second ← innerDepth body
      pure (first, second, depth.free.contains (.uninterned second))
  | _ => none

/-- Slot 93 is the active ancestor in the completed closed ordinary route. -/
def selected : Option (Nat × Nat × Bool) := do
  let key ← result.state.nodes.issued 93
  let value ← result.state.nodeRecords key
  observe value

/-- The changed level aliases a name in the active ancestor's actual old Depth probe. -/
theorem closed_alias : selected = some (0, 1, true) := by
  set_option maxRecDepth 30000 in
  set_option cbv.maxSteps 100000000 in cbv

/-- The closed run completes after the ordinary alias occurs. -/
theorem complete : (match result with | .done _ _ => true | .pending .. => false) = true := by
  set_option maxRecDepth 30000 in
  set_option cbv.maxSteps 100000000 in cbv

/-- All references are in scope before closed execution. -/
theorem expression_scoped : Scoped 0 expression := by
  simp [expression, ancestorBody, innerBody, Scoped, EdgesScoped, ManyScoped]

end MicroCFTA.InternedOrdinaryCaptureBoundary
