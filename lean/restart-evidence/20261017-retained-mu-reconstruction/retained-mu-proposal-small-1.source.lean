import MicroCFTA.SourceEqualityRequiredCache
import MicroCFTA.SourceCurrentNativeMuPublication
import MicroCFTA.InternedFreshOrdinaryStoredSubstitution
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

namespace MicroCFTA.RetainedMuProposalExplore
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction
open InternedBinderProtocol (Reference NodeKey NodeRef)

def expression (usedInner : Bool) : Syntax Nat Bool :=
  .binder false (.node [.mk 0 false [.var 0,
    .binder false (.node [.mk 1 true (if usedInner then [.var 1,.var 0] else [.var 1])])]])

def fields : Value Nat Bool → Interned NodeKey × Value Nat Bool × Value Nat Bool × Value Nat Bool
  | .mu entry body depth ordinary => (entry,body,depth,ordinary)
  | _ => (⟨0,.node []⟩,.empty,.empty,.empty)

def chosen (inner : Bool) (root : Value Nat Bool) : Value Nat Bool :=
  if inner then ((children (fields root).2.1)[1]?).getD .empty else root

def replacement (kind : Nat) (root selected : Value Nat Bool) : Value Nat Bool :=
  let data := fields selected
  match kind with
  | 0 => .empty
  | 1 => .reference .depth
  | 2 => .reference (.uninterned (ordinaryLevel data.2.2.1))
  | 3 => .reference (.interned data.1.identity)
  | 4 => root
  | 5 => data.2.2.2
  | 6 => data.2.1
  | 7 => .reference (.interned (fields root).1.identity)
  | 8 => .reference (.uninterned (ordinaryLevel (fields (chosen true root)).2.2.1))
  | _ => selected

def trial (usedInner inner : Bool) (kind : Nat) :
    Bool × Bool × Nat × Bool × Option (NodeRef × NodeRef × Nat × Nat) :=
  match build (expression usedInner) [] empty with
  | .pending .. => (usedInner,inner,kind,false,none)
  | .done root heap =>
    let selected := chosen inner root
    let data := fields selected
    let target := replacement kind root selected
    match InternedFreshOrdinaryStoredSubstitution.execute data.2.1
      (InternedStoredSubstitutionRebind.replacement (.interned data.1.identity) target) heap with
    | .pending .. => (usedInner,inner,kind,InternedFreshOrdinaryDepthHeap.usesLocal data.2.2.1 data.2.2.2,none)
    | .done left middle =>
      match InternedFreshOrdinaryStoredSubstitution.execute data.2.2.2
        (InternedStoredSubstitutionRebind.replacement (.uninterned (ordinaryLevel data.2.2.1)) target) middle with
      | .pending .. => (usedInner,inner,kind,InternedFreshOrdinaryDepthHeap.usesLocal data.2.2.1 data.2.2.2,none)
      | .done right after =>
        (usedInner,inner,kind,InternedFreshOrdinaryDepthHeap.usesLocal data.2.2.1 data.2.2.2,
          some (left.referenceOf,right.referenceOf,middle.nodes.next,after.nodes.next))
end MicroCFTA.RetainedMuProposalExplore

namespace MicroCFTA.RetainedMuProposalExplore

def agrees (data : Bool × Bool × Nat × Bool × Option (NodeRef × NodeRef × Nat × Nat)) : Prop :=
  match data.2.2.2.2 with
  | none => False
  | some (left,right,_,_) => left = right

 theorem empty_replacement : agrees (trial false false 0) := by cbv
end MicroCFTA.RetainedMuProposalExplore
#check @MicroCFTA.RetainedMuProposalExplore.empty_replacement
#print axioms MicroCFTA.RetainedMuProposalExplore.empty_replacement
