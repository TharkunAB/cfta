import MicroCFTA.SourceCurrentNativeMuPublication
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

namespace MicroCFTA.MuPublicationKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome request finish)
open InternedFreshOrdinaryConstruction SourceCurrentNativeMuPublication
open InternedBinderProtocol (NodeKey)
local notation "Node" => Value Nat Bool

private def inner : Syntax Nat Bool := .binder false (.node [.mk 1 false [.var 1]])
private def expression : Syntax Nat Bool := .binder false (.node [.mk 0 true [inner,.var 0]])
private def built := build expression [] empty
private def root : Node := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def entryOf : Node → Interned NodeKey
  | .mu entry _ _ _ => entry
  | _ => ⟨0,.node []⟩
private def bodyOf : Node → Node
  | .mu _ body _ _ => body
  | _ => .empty
private def depthOf : Node → Node
  | .mu _ _ depth _ => depth
  | _ => .empty
private def ordinaryOf : Node → Node
  | .mu _ _ _ ordinary => ordinary
  | _ => .empty
private def nested := ((children (bodyOf root))[0]?).getD .empty
private theorem actual : built = .done root heap := by cbv
private theorem root_shape : root = .mu (entryOf root) (bodyOf root) (depthOf root) (ordinaryOf root) := by cbv
private theorem nested_shape : nested = .mu (entryOf nested) (bodyOf nested) (depthOf nested) (ordinaryOf nested) := by cbv
private theorem root_stored : heap.nodeRecords (muKey (depthOf root) (ordinaryOf root)) =
    some (.mu (entryOf root) (bodyOf root) (depthOf root) (ordinaryOf root)) := by cbv
private theorem nested_stored : heap.nodeRecords (muKey (depthOf nested) (ordinaryOf nested)) =
    some (.mu (entryOf nested) (bodyOf nested) (depthOf nested) (ordinaryOf nested)) := by cbv

/-- Actual nested publication order does not follow reservation identities. -/
theorem nested_order :
    build expression [] empty = .done root heap ∧
    root = .mu (entryOf root) (bodyOf root) (depthOf root) (ordinaryOf root) ∧
    nested = .mu (entryOf nested) (bodyOf nested) (depthOf nested) (ordinaryOf nested) ∧
    (entryOf root).identity < (entryOf nested).identity ∧
    Written empty (muKey (depthOf root) (ordinaryOf root)) root ∧
    Written empty (muKey (depthOf nested) (ordinaryOf nested)) nested := by
  refine ⟨actual,root_shape,nested_shape,?_,?_,?_⟩
  · cbv
  · rw [root_shape]
    exact closed_writer expression _ _ _ _ _ root_stored
  · rw [nested_shape]
    exact closed_writer expression _ _ _ _ _ nested_stored

/-- The produced winner supports both exact full-source replay and a smart warm hit. -/
theorem warm_selected :
    build expression [] heap = .done root heap ∧
    request true (depthOf root) (ordinaryOf root)
      (fun _ state => .pending (muKey (depthOf root) (ordinaryOf root)) state) heap =
      .done (finish true root) heap ∧
    ∃ event : Publication (Symbol := Nat) (Guard := Bool),
      root = event.candidate ∧ event.afterBody.nodeRecords event.key = none ∧
      Nonempty (History empty event.before) ∧
      Nonempty (History event.before event.afterDepth) ∧
      Nonempty (History event.afterDepth event.cut) ∧
      Nonempty (History event.allocated event.afterBody) ∧
      build (.binder event.smart event.expression) event.environment event.before =
        .done event.result event.after := by
  have selected := closed_warm expression true (depthOf root) (ordinaryOf root)
    (fun _ state => .pending (muKey (depthOf root) (ordinaryOf root)) state)
    (entryOf root) (bodyOf root) (depthOf root) (ordinaryOf root) root_stored
  have written : Written empty (muKey (depthOf root) (ordinaryOf root)) root := by
    rw [root_shape]
    exact selected.1
  obtain ⟨event,_key,sameValue,firstWrite,earlier,depthHistory,ordinaryHistory,bodyHistory⟩ := written
  refine ⟨?_,?_,event,sameValue,firstWrite,earlier,depthHistory,ordinaryHistory,bodyHistory,event.build_done⟩
  · cbv
  · simpa only [← root_shape] using selected.2

end MicroCFTA.MuPublicationKernels
#check @MicroCFTA.MuPublicationKernels.nested_order
#print MicroCFTA.MuPublicationKernels.nested_order
#print axioms MicroCFTA.MuPublicationKernels.nested_order
#check @MicroCFTA.MuPublicationKernels.warm_selected
#print MicroCFTA.MuPublicationKernels.warm_selected
#print axioms MicroCFTA.MuPublicationKernels.warm_selected
