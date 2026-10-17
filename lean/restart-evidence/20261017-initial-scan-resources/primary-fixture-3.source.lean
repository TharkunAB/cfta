import MicroCFTA.SourceCurrentPrimaryGateNumericReplay
namespace MicroCFTA.PrimaryFixture
open InternedConstructorTemplates InternedNestedConstruction
private def expression : Syntax Nat Bool :=
  .binder false (.node [.mk 0 true [.binder false (.node [.mk 1 true [.var 0, .var 1]])]])
private def outcome := InternedFreshOrdinaryConstruction.build expression [] empty
private def before := outcome.state
private def original : Value Nat Bool := match outcome with | .done value _ => value | .pending _ _ => .empty
private def body : Value Nat Bool := match original with
  | .mu _ value _ _ => value
  | _ => .empty
private def selected : Value Nat Bool := match original with
  | .mu _ (.node _ [.mk _ [child]] _ _) _ _ => child
  | _ => .empty
#eval (before.nodes.next, before.edges.next, original.free.isEmpty, selected.free.isEmpty)
private theorem built : InternedFreshOrdinaryConstruction.build expression [] empty = .done original before := by cbv
private theorem selected_available : InternedProbeProvenance.Available before selected := by
  have originalAvailable := (InternedFreshOrdinaryFacts.closed_verified expression).result original before built
  have bodyAvailable := originalAvailable.children body (by cbv; exact List.mem_cons_self)
  exact bodyAvailable.children selected (by cbv; exact List.mem_cons_self)
private def values : List (Value Nat Bool) := [selected, .reference .depth]
private def paths : List (List Nat) := [[9], [0], [1]]
private def call := EndpointStatefulGate.classMeets (fun _ => true) (fun _ => false) 4 values paths before
private def after := call.state
#eval (after.nodes.next, after.edges.next)
private theorem cold : EndpointStatefulGate.classMeets (fun _ => true) (fun _ => false) 4 values paths before = .done (some true) after := by cbv
private theorem warm : EndpointStatefulGate.classMeets (fun _ => true) (fun _ => false) 4 values paths after = .done (some true) after := by cbv
private theorem allocated : before.nodes.next < after.nodes.next ∧ before.edges.next < after.edges.next := by decide +kernel
end MicroCFTA.PrimaryFixture
