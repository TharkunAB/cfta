import MicroCFTA.InternedFreshOrdinarySourceHistory

/-!
# A repaired producer path does not preserve result liveness

The actual repaired source run completes a nested binder before an empty
child removes its edge. The stored nested record retains the ordinary name.
The enclosing producer returns empty. A source path cannot transfer the
nested capture to the producer result.
-/
namespace MicroCFTA.InternedFreshOrdinaryProducerPathBoundary
open Cache InternedConstructorTemplates
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction
open InternedFreshOrdinaryLiveInputs
open InternedFreshOrdinaryActiveOrigins (Path)
open InternedBinderProtocol (Reference)

/-- The nested raw binder reads its actual outer input. -/
def target : Syntax Nat Unit := .binder false (.var 1)

/-- The source executes the target before the empty child removes its edge. -/
def body : Syntax Nat Unit := .node [.mk 0 () [target, .empty]]

/-- A closed smart binder executes the nested target in its actual probe callbacks. -/
def expression : Syntax Nat Unit := .binder true body

/-- The actual repaired closed source run starts with empty constructor caches. -/
def result := build expression [] (empty : State Nat Unit)

/-- The actual descendant path crosses no extra binder before the target. -/
theorem source_path (environment : List (Value Nat Unit)) : Path body environment target environment [] :=
  .node (symbol := 0) (guard := ()) (children := [target, .empty]) (by simp) (by simp) (.here _ _)

/-- The varying outer slot remains live at the target binder. -/
theorem target_live : liveInputs target [(Sum.inr () : Sum (Value Nat Unit) Unit)] = [.inr ()] := by cbv

/-- That same slot is absent from the enclosing producer's result support. -/
theorem body_dead : liveInputs body [(Sum.inr () : Sum (Value Nat Unit) Unit)] = [] := by cbv

/-- The repaired closed producer completes with empty output. -/
theorem complete_empty : (match result with | .done .empty _ => true | _ => false) = true := by
  set_option maxRecDepth 10000 in cbv

/-- The completed nested target retains the ordinary capture despite the removed enclosing edge. -/
theorem retained_target :
    (result.state.nodeRecords (muKey (.reference (.uninterned 0) : Value Nat Unit) (.reference (.uninterned 0)))).map
      (fun value => value.free.contains (.uninterned 0)) = some true := by
  set_option maxRecDepth 10000 in cbv

end MicroCFTA.InternedFreshOrdinaryProducerPathBoundary
