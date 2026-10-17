import MicroCFTA.SourceCurrentConstrainedCapCheckedJointRebase

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 1000000

namespace MicroCFTA.CapturedJointKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "Origins" => SourceCurrentConstrainedCapCheckedJointOrigins.Stored
local notation "Joint" => SourceCurrentConstrainedCapCheckedJointCache.Stored
variable {width : Nat} {Symbol Guard : Type}

/-- Actual node work retains both memo tables and rebases all captured joint laws to its returned heap. -/
theorem actual_node_work_rebase [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (source : State Symbol Guard) (before : Native width Symbol Guard)
    (sourceFacts : Facts source) (growth : Grows source before.machine.heap)
    (history : Extends source.nodes.issued before.machine.heap.nodes.issued)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before)
    (captured : Origins source before) (joint : Joint annotation source before)
    (rows : List (EdgeValue Symbol Guard)) (resident : ∀ row ∈ rows, EdgeResident before.machine.heap row) :
    let actual := run (makeNode rows) before.machine.heap
    let machine : Machine Symbol Guard := {before.machine with heap := actual.2}
    let after := advance before machine
    work (makeNode rows) before.machine = .done actual.1 machine ∧
      after.nodes = before.nodes ∧ after.edges = before.edges ∧
      SourceCurrentAllocatedNativePhysicalCache.Valid after ∧
      Joint annotation after.machine.heap after ∧ Origins after.machine.heap after := by
  dsimp only
  have built := InternedNestedFacts.node_verified rows before.machine.heap physical.machine.1 resident
  let machine : Machine Symbol Guard := {before.machine with heap := (run (makeNode rows) before.machine.heap).2}
  have extension : Extension before.machine machine := ⟨built.growth, built.history, extends_refl _⟩
  have valid : SourceRecursiveIntersectionKernel.Valid machine := ⟨built.facts, physical.machine.2⟩
  have afterPhysical := SourceCurrentAllocatedNativePhysicalCache.advance_valid before physical machine valid extension
  have afterOrigins := SourceCurrentConstrainedCapCheckedJointOrigins.advance_stored source before machine captured
  have afterJoint := SourceCurrentConstrainedCapCheckedJointCache.advance_stored annotation source before machine joint
  have transported := SourceCurrentConstrainedCapCheckedJointRebase.rebase annotation source (advance before machine)
    sourceFacts (grows_trans growth built.growth) (extends_trans history built.history) afterPhysical afterOrigins afterJoint
  exact ⟨rfl, rfl, rfl, afterPhysical, transported⟩

/-- An actual warm hit derives its new-source cap and classifier from captured old origins, without an old annotation premise. -/
theorem warm_hit_rebased (annotation : Guard → Prop) (source : State Symbol Guard)
    (before chosen after : Native width Symbol Guard) (request : NodeRequest Symbol Guard)
    (handle depth : Nat) (value : Value Symbol Guard)
    (sourceFacts : Facts source) (growth : Grows source before.machine.heap)
    (history : Extends source.nodes.issued before.machine.heap.nodes.issued)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before)
    (captured : Origins source before) (joint : Joint annotation source before)
    (ready : NodeReady before.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (selected : lookupNode width request before = (.memoized handle, chosen))
    (demanded : demandNode handle chosen = (.ready value, after))
    (bindings : SourceCurrentConstrainedCapNativeOccurrenceCache.OriginalBindings annotation before.machine.heap request.domain.key)
    (inputs : SourceCurrentConstrainedCapNativeOccurrenceCache.NodeInputs before.machine.heap request)
    (left : SourceCurrentConstrainedCap.Cap annotation depth request.left)
    (right : SourceCurrentConstrainedCap.Cap annotation depth request.right) :
    after = chosen ∧ Available after.machine.heap value ∧
      Joint annotation before.machine.heap after ∧
      SourceCurrentConstrainedCap.Cap annotation depth value ∧
      SourceCurrentConstrainedCapPairOccurrences.Classified
        (SourceCurrentConstrainedCapPairOccurrences.sourceWeight annotation before.machine.heap)
        (SourceCurrentConstrainedCapNonplainRank.pairRank annotation request.left request.right) value ∧
      SourceRecursiveIntersectionResultScope.Scope request.domain.key.seen value := by
  have rebased := SourceCurrentConstrainedCapCheckedJointRebase.rebase annotation source before sourceFacts growth history
    physical captured joint
  have observed := SourceCurrentConstrainedCapCheckedJointCache.node_observed_ready annotation before.machine.heap request
    before chosen after handle value physical rebased.1 ready safe selected demanded
  have law := observed.1 depth bindings inputs left right
  exact ⟨observed.2.2.1, observed.2.2.2, observed.2.1, law⟩

#print axioms actual_node_work_rebase
#check @actual_node_work_rebase
#print axioms warm_hit_rebased
#check @warm_hit_rebased
end MicroCFTA.CapturedJointKernels
