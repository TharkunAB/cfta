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
  have bodyAvailable := originalAvailable.children body (by exact List.mem_cons_self)
  exact bodyAvailable.children selected (by exact List.mem_cons_self)
end MicroCFTA.PrimaryFixture
