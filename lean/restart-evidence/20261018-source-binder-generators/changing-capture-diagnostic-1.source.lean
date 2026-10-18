import MicroCFTA.SourceCurrentOpenObservationLanguage
import MicroCFTA.SourceCurrentStoredReconstruction
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000
namespace MicroCFTA.ChangingCaptureDiagnostic
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (unfold)
private def val (outcome : Outcome Nat Bool (Value Nat Bool)) : Value Nat Bool :=
  match outcome with | .done result _ => result | .pending .. => .empty
private def leaf : Syntax Nat Bool := .node [.mk 3 true []]
private def wrapped : Syntax Nat Bool := .binder false leaf
private def outer (capture : Syntax Nat Bool) : Syntax Nat Bool :=
  .binder true (.node [.mk 8 false [.var 0,
    .binder true (.node [.mk 9 true [.var 0,.var 1,capture]])]])
private def expression : Syntax Nat Bool :=
  .binder true (.node [.mk 8 false [.var 0,
    .binder true (.node [.mk 9 true [.var 0,.var 1,.var 2]])]])
private def source : Syntax Nat Bool := .node [.mk 0 true [leaf,wrapped,outer leaf,outer wrapped]]
private def built := build source [] empty
private def root := val built
private def base := built.state
private def a : Value Nat Bool := (children root)[0]?.getD .empty
private def b : Value Nat Bool := (children root)[1]?.getD .empty
private def x : Value Nat Bool := (children root)[2]?.getD .empty
private def y : Value Nat Bool := (children root)[3]?.getD .empty
private def ux := unfold x base
private def lx := val ux
private def uy := unfold y ux.state
private def ly := val uy
private def innerX : Value Nat Bool := (children lx)[1]?.getD .empty
private def innerY : Value Nat Bool := (children ly)[1]?.getD .empty
private def vx := unfold innerX uy.state
private def mx := val vx
private def vy := unfold innerY vx.state
private def my := val vy
private def ub := unfold b vy.state
private def reader := ub.state
private def fields (value : Value Nat Bool) :=
  (value.referenceOf, value.free, match value with | .mu _ _ d o => InternedFreshOrdinaryDepthHeap.usesLocal d o | _ => false)
#eval [a,b,x,y,lx,ly,innerX,innerY,mx,my].map fields
#eval [lx,ly,mx,my].map (fun value => (children value).map Value.referenceOf)
#eval (build expression [a] reader == .done x reader, build expression [b] reader == .done y reader)
#eval [x,y,innerX,innerY,b].map (fun value => (unfold value reader).state.nodes.next == reader.nodes.next)
end MicroCFTA.ChangingCaptureDiagnostic
