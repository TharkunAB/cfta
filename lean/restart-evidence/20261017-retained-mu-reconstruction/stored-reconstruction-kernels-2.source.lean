import MicroCFTA.SourceCurrentStoredReconstruction
import MicroCFTA.InternedFreshOrdinaryReplay
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
namespace MicroCFTA.StoredReconstructionKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction
open InternedBinderProtocol (Reference NodeKey)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentNativeMuPublication (History Written)
private def inner : Syntax Nat Bool := .binder false (.node [.mk 1 false [.var 1]])
private def expression : Syntax Nat Bool := .binder false (.node [.mk 0 true [inner,.var 0]])
private def built := build expression [] empty
private def original : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def fields : Value Nat Bool → Interned NodeKey × Value Nat Bool × Value Nat Bool × Value Nat Bool
  | .mu entry body depth ordinary => (entry,body,depth,ordinary)
  | _ => (⟨0,.node []⟩,.empty,.empty,.empty)
private def entry := (fields original).1
private def body := (fields original).2.1
private def depth := (fields original).2.2.1
private def ordinary := (fields original).2.2.2
private def key := InternedConstructorTemplates.muKey depth ordinary
private def bodyEnv : InternedStoredSubstitution.Environment Nat Bool :=
  fun name => if name = .interned entry.identity then some (.reference .depth) else none
private def ordinaryEnv : InternedStoredSubstitution.Environment Nat Bool :=
  fun name => if name = .uninterned (ordinaryLevel depth) then some (.reference .depth) else none
private theorem built_done : built = .done original heap := by cbv
private theorem present : heap.nodeRecords key = some (.mu entry body depth ordinary) := by cbv
private theorem nested : ∃ selected childBody childDepth childOrdinary,
    (.mu selected childBody childDepth childOrdinary : Value Nat Bool) ∈ children body := by
  let child : Value Nat Bool := ((children body)[0]?).getD .empty
  refine ⟨(fields child).1,(fields child).2.1,(fields child).2.2.1,(fields child).2.2.2,?_⟩
  cbv
  exact .head _
private theorem ready : Ready heap := SourceEqualityRequiredCache.constructed expression original heap built_done
private theorem produced_proof :
    (∃ selected childBody childDepth childOrdinary,
      (.mu selected childBody childDepth childOrdinary : Value Nat Bool) ∈ children body) ∧
    ∃ left middle right after,
      InternedFreshOrdinaryStoredSubstitution.execute body bodyEnv heap = .done left middle ∧
      InternedFreshOrdinaryStoredSubstitution.execute ordinary ordinaryEnv middle = .done right after ∧
      Keeps heap middle ∧ Keeps middle after ∧ Available after left ∧ Available after right ∧
      Nonempty (History heap middle) ∧ Nonempty (History middle after) ∧ Nonempty (History empty after) ∧
      after.nodeRecords key = some (.mu entry body depth ordinary) ∧
      Written empty key (.mu entry body depth ordinary) ∧
      InternedFreshOrdinaryStoredSubstitution.execute body bodyEnv after = .done left after ∧
      InternedFreshOrdinaryStoredSubstitution.execute ordinary ordinaryEnv after = .done right after := by
  obtain ⟨left,middle,right,after,firstDone,secondDone,first,second,leftAvailable,rightAvailable,
      firstHistory,secondHistory,retained⟩ :=
    SourceCurrentStoredReconstruction.mu key entry body depth ordinary (.reference .depth) heap ready present
      (InternedNestedProvenance.depth_available heap)
  obtain ⟨firstEvents⟩ := firstHistory
  obtain ⟨secondEvents⟩ := secondHistory
  have whole : History empty after := .trans (SourceCurrentNativeMuPublication.closed_history expression)
    (.trans firstEvents secondEvents)
  exact ⟨nested,left,middle,right,after,firstDone,secondDone,first,second,leftAvailable,rightAvailable,
    ⟨firstEvents⟩,⟨secondEvents⟩,⟨whole⟩,retained,whole.from_empty key entry body depth ordinary retained,
    InternedFreshOrdinaryReplay.build_replay (InternedStoredSubstitution.encode (InternedStoredSubstitution.leaves body) [] body)
      ((InternedStoredSubstitution.leaves body).map (InternedStoredSubstitution.input bodyEnv)) heap after left middle
      ready.semantic.1.normal.facts.coherent.valid firstDone second.growth,
    InternedFreshOrdinaryReplay.build_replay (InternedStoredSubstitution.encode (InternedStoredSubstitution.leaves ordinary) [] ordinary)
      ((InternedStoredSubstitution.leaves ordinary).map (InternedStoredSubstitution.input ordinaryEnv)) middle after right after
      first.ready.semantic.1.normal.facts.coherent.valid secondDone (grows_refl after)⟩

/-- A source-built nested Mu has both reconstructions and exact warm replays at their common final heap. -/
theorem produced :
    (∃ selected childBody childDepth childOrdinary,
      (.mu selected childBody childDepth childOrdinary : Value Nat Bool) ∈ children body) ∧
    ∃ left middle right after,
      InternedFreshOrdinaryStoredSubstitution.execute body bodyEnv heap = .done left middle ∧
      InternedFreshOrdinaryStoredSubstitution.execute ordinary ordinaryEnv middle = .done right after ∧
      Keeps heap middle ∧ Keeps middle after ∧ Available after left ∧ Available after right ∧
      Nonempty (History heap middle) ∧ Nonempty (History middle after) ∧ Nonempty (History empty after) ∧
      after.nodeRecords key = some (.mu entry body depth ordinary) ∧
      Written empty key (.mu entry body depth ordinary) ∧
      InternedFreshOrdinaryStoredSubstitution.execute body bodyEnv after = .done left after ∧
      InternedFreshOrdinaryStoredSubstitution.execute ordinary ordinaryEnv after = .done right after := produced_proof
end MicroCFTA.StoredReconstructionKernels
#check @MicroCFTA.StoredReconstructionKernels.produced
#print MicroCFTA.StoredReconstructionKernels.produced
#print axioms MicroCFTA.StoredReconstructionKernels.produced
