import MicroCFTA.InternedPairedRouteBoundary

/-!
# Pending construction with supplied ordinary captures

The open source expression discards the crossed binder's result and returns
an existing ordinary capture. A later target uses that same complete pair.
The three supplied captures are not derived here from closed execution.
-/
namespace MicroCFTA.InternedPairedPendingBoundary
open InternedConstructorTemplates InternedNestedConstruction InternedNestedMissReadback
open InternedPairedRouteBoundary (crossedBody discarded target)
open InternedBinderProtocol (Reference)

/-- The discarded child retains its effects; the other operand supplies both ancestor probes. -/
def ancestor : Syntax Nat Unit := .union [.node [.mk 10 () [.binder false crossedBody, .empty]], .var 3]

/-- These are supplied open inputs, rather than a derived closed source environment. -/
def environment : List (Value Nat Unit) := [.reference .depth, .reference (.uninterned 0), .reference (.uninterned 1)]

/-- Execute the open binder from empty constructor caches. -/
def result := build (.binder false ancestor) environment empty

/-- Both components of the encountered pending key are the captured ordinary name one. -/
theorem pending :
    (match result with | .pending key _ => some key | _ => none) =
      some (muKey (.reference (.uninterned 1) : Value Nat Unit) (.reference (.uninterned 1))) := by
  set_option maxRecDepth 30000 in
  set_option cbv.maxSteps 100000000 in cbv

/-- The expression is scoped relative to its three explicitly supplied captures. -/
theorem expression_scoped : Scoped 3 (.binder false ancestor) := by
  simp [ancestor, crossedBody, discarded, target, InternedOrdinaryLevelBoundary.innerBody, Scoped, EdgesScoped, ManyScoped]

end MicroCFTA.InternedPairedPendingBoundary
