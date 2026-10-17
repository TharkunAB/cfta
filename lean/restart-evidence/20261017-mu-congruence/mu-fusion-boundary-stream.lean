import MicroCFTA.SourceCurrentStoredReconstructionReplay
import MicroCFTA.InternedStoredSubstitutionRebind

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.proofs.threshold 254
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

namespace MicroCFTA.MuFusionBoundary
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction
open InternedBinderProtocol (NodeKey NodeRef)

/-- Closed sources exercise self filtering, dead rows, and nested union alternatives. -/
def expression (shape : Nat) : Syntax Nat Bool :=
  match shape with
  | 0 => .binder false (.union [.var 0,.var 0,
      .node [.mk 0 true [.var 0],.mk 0 true [.var 0],.mk 9 false [.empty]]])
  | 1 => .binder false (.union [.var 0,.node [.mk 0 true [.var 0]],
      .binder false (.union [.var 0,.var 1,.node [.mk 1 false [.var 1]]])])
  | _ => .binder false (.union [.var 0,.node [.mk 0 true [.var 0]],
      .binder false (.union [.var 0,.var 1,.node [.mk 1 false [.var 0,.var 1]]])])

/-- Extract the actual stored Mu fields. -/
def fields : Value Nat Bool → Interned NodeKey × Value Nat Bool × Value Nat Bool × Value Nat Bool
  | .mu entry body depth ordinary => (entry,body,depth,ordinary)
  | _ => (⟨0,.node []⟩,.empty,.empty,.empty)

/-- Select the first retained Mu among the stored body's root union alternatives. -/
def nested (root : Value Nat Bool) : Value Nat Bool :=
  ((unionMembers (fields root).2.1).find? fun value =>
    match value with | .mu .. => true | _ => false).getD .empty

/-- Choose a replacement from actual payloads and reserved names. -/
def replacement (kind : Nat) (root selected : Value Nat Bool) : Value Nat Bool :=
  let data := fields selected
  match kind with
  | 0 => .empty
  | 1 => .reference .depth
  | 2 => .reference (.uninterned (ordinaryLevel data.2.2.1))
  | 3 => .reference (.interned data.1.identity)
  | 4 => .reference (.interned (fields root).1.identity)
  | _ => root

/-- Execute the two actual repaired reconstructions at successive heaps. -/
def trial (shape : Nat) (inner : Bool) (kind : Nat) :
    Nat × Bool × Nat × Bool × Bool × Option (NodeRef × NodeRef × Nat × Nat) :=
  match build (expression shape) [] empty with
  | .pending .. => (shape,inner,kind,false,false,none)
  | .done root heap =>
    let selected := if inner then nested root else root
    let data := fields selected
    let target := replacement kind root selected
    let used := InternedFreshOrdinaryDepthHeap.usesLocal data.2.2.1 data.2.2.2
    let closed := selected.free.isEmpty
    match InternedFreshOrdinaryStoredSubstitution.execute data.2.1
      (InternedStoredSubstitutionRebind.replacement (.interned data.1.identity) target) heap with
    | .pending .. => (shape,inner,kind,used,closed,none)
    | .done left middle =>
      match InternedFreshOrdinaryStoredSubstitution.execute data.2.2.2
        (InternedStoredSubstitutionRebind.replacement (.uninterned (ordinaryLevel data.2.2.1)) target) middle with
      | .pending .. => (shape,inner,kind,used,closed,none)
      | .done right after =>
        (shape,inner,kind,used,closed,
          some (left.referenceOf,right.referenceOf,middle.nodes.next,after.nodes.next))

end MicroCFTA.MuFusionBoundary
#eval MicroCFTA.MuFusionBoundary.trial 0 false 0
#eval MicroCFTA.MuFusionBoundary.trial 0 false 1
#eval MicroCFTA.MuFusionBoundary.trial 1 false 2
#eval MicroCFTA.MuFusionBoundary.trial 1 true 4
#eval MicroCFTA.MuFusionBoundary.trial 2 false 0
#eval MicroCFTA.MuFusionBoundary.trial 2 true 1
#eval MicroCFTA.MuFusionBoundary.trial 2 true 4
