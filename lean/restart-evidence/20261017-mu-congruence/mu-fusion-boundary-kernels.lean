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

namespace MicroCFTA.MuFusionRootKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction
open InternedBinderProtocol (Reference NodeKey)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentNativeMuPublication (History Written)

private def expression (nested : Bool) : Syntax Nat Bool :=
  if nested then .binder false (.union [.var 0,.binder false (.union [.var 0,.var 1])])
  else .binder false (.union [.var 0,.var 0,
    .node [.mk 0 true [.var 0],.mk 0 true [.var 0],.mk 9 false [.empty]]])
private def built (nested : Bool) := build (expression nested) [] empty
private def root (nested : Bool) : Value Nat Bool :=
  match built nested with | .done value _ => value | .pending .. => .empty
private def heap (nested : Bool) := (built nested).state
private def fields : Value Nat Bool → Interned NodeKey × Value Nat Bool × Value Nat Bool × Value Nat Bool
  | .mu entry body depth ordinary => (entry,body,depth,ordinary)
  | _ => (⟨0,.node []⟩,.empty,.empty,.empty)
private def entry (nested : Bool) := (fields (root nested)).1
private def body (nested : Bool) := (fields (root nested)).2.1
private def depth (nested : Bool) := (fields (root nested)).2.2.1
private def ordinary (nested : Bool) := (fields (root nested)).2.2.2
private def key (nested : Bool) := muKey (depth nested) (ordinary nested)
private def target (nested : Bool) : Value Nat Bool :=
  if nested then .reference (.interned (entry nested).identity)
  else .reference (.uninterned (ordinaryLevel (depth nested)))
private def bodyEnv (nested : Bool) : InternedStoredSubstitution.Environment Nat Bool :=
  InternedStoredSubstitutionRebind.replacement (.interned (entry nested).identity) (target nested)
private def ordinaryEnv (nested : Bool) : InternedStoredSubstitution.Environment Nat Bool :=
  InternedStoredSubstitutionRebind.replacement (.uninterned (ordinaryLevel (depth nested))) (target nested)
private def firstRun (nested : Bool) :=
  InternedFreshOrdinaryStoredSubstitution.execute (body nested) (bodyEnv nested) (heap nested)
private def left (nested : Bool) : Value Nat Bool :=
  match firstRun nested with | .done value _ => value | .pending .. => .empty
private def middle (nested : Bool) := (firstRun nested).state
private def secondRun (nested : Bool) :=
  InternedFreshOrdinaryStoredSubstitution.execute (ordinary nested) (ordinaryEnv nested) (middle nested)
private def right (nested : Bool) : Value Nat Bool :=
  match secondRun nested with | .done value _ => value | .pending .. => .empty
private def after (nested : Bool) := (secondRun nested).state

private theorem built_done (nested : Bool) : built nested = .done (root nested) (heap nested) := by
  cases nested <;> cbv
private theorem present (nested : Bool) : (heap nested).nodeRecords (key nested) =
    some (.mu (entry nested) (body nested) (depth nested) (ordinary nested)) := by
  cases nested <;> cbv
private theorem ready (nested : Bool) : Ready (heap nested) :=
  SourceEqualityRequiredCache.constructed (expression nested) (root nested) (heap nested) (built_done nested)
private theorem target_available (nested : Bool) : Available (heap nested) (target nested) := by
  cases nested with
  | false =>
      apply reference_available
      intro identity member
      simp only [Value.free,List.mem_singleton] at member
      cases member
  | true =>
      apply reference_available
      intro identity member
      have same : identity = (entry true).identity := by
        simpa only [Value.free,List.mem_singleton,Reference.interned.injEq] using member
      subst identity
      exact ⟨key true,by cbv⟩

private def ResultFacts (nested : Bool) : Prop :=
  firstRun nested = .done (left nested) (middle nested) ∧
  secondRun nested = .done (right nested) (after nested) ∧
  Keeps (heap nested) (middle nested) ∧ Keeps (middle nested) (after nested) ∧
  Available (after nested) (left nested) ∧ Available (after nested) (right nested) ∧
  Nonempty (History empty (after nested)) ∧
  Written empty (key nested) (.mu (entry nested) (body nested) (depth nested) (ordinary nested)) ∧
  (after nested).nodeRecords (key nested) = some (.mu (entry nested) (body nested) (depth nested) (ordinary nested)) ∧
  InternedFreshOrdinaryStoredSubstitution.execute (body nested) (bodyEnv nested) (after nested) =
    .done (left nested) (after nested) ∧
  InternedFreshOrdinaryStoredSubstitution.execute (ordinary nested) (ordinaryEnv nested) (after nested) =
    .done (right nested) (after nested)

private theorem result_facts (nested : Bool)
    (firstDone : firstRun nested = .done (left nested) (middle nested))
    (secondDone : secondRun nested = .done (right nested) (after nested)) : ResultFacts nested := by
  obtain ⟨actualLeft,actualMiddle,actualRight,actualAfter,first,second,firstKeeps,secondKeeps,
      leftAvailable,rightAvailable,firstHistory,secondHistory,whole,retained,writer,firstWarm,secondWarm⟩ :=
    SourceCurrentStoredReconstructionReplay.mu (key nested) (entry nested) (body nested) (depth nested)
      (ordinary nested) (target nested) (heap nested) (ready nested) (present nested)
      (target_available nested) (SourceCurrentNativeMuPublication.closed_history (expression nested))
  have firstEq : .done (left nested) (middle nested) =
      (.done actualLeft actualMiddle : Outcome Nat Bool (Value Nat Bool)) := firstDone.symm.trans first
  rcases Outcome.done.inj firstEq with ⟨leftEq,middleEq⟩
  subst actualLeft actualMiddle
  have secondEq : .done (right nested) (after nested) =
      (.done actualRight actualAfter : Outcome Nat Bool (Value Nat Bool)) := secondDone.symm.trans second
  rcases Outcome.done.inj secondEq with ⟨rightEq,afterEq⟩
  subst actualRight actualAfter
  exact ⟨firstDone,secondDone,firstKeeps,secondKeeps,leftAvailable,rightAvailable,whole,writer,retained,firstWarm,secondWarm⟩

/-- Root self filtering, duplicate rows, and a dead row preserve this two-sided reconstruction equality. -/
theorem union_duplicate_dead_rows :
    build (expression false) [] empty = .done (root false) (heap false) ∧
    Ready (heap false) ∧ (root false).free = [] ∧
    InternedFreshOrdinaryDepthHeap.usesLocal (depth false) (ordinary false) = true ∧
    Available (heap false) (target false) ∧
    (∃ nodeEntry rows cachedDepth free, body false = .node nodeEntry rows cachedDepth free ∧ rows.length = 1) ∧
    ResultFacts false ∧ left false = right false := by
  have firstDone : firstRun false = .done (left false) (middle false) := by cbv
  have secondDone : secondRun false = .done (right false) (after false) := by cbv
  exact ⟨built_done false,ready false,by cbv,by cbv,target_available false,
    ⟨_,_,_,_,by cbv,by cbv⟩,result_facts false firstDone secondDone,by cbv⟩

/-- A root union with a raw unused inner binder normalizes both sides to the own self replacement. -/
theorem union_raw_unused_inner :
    build (expression true) [] empty = .done (root true) (heap true) ∧
    Ready (heap true) ∧ (root true).free = [] ∧
    InternedFreshOrdinaryDepthHeap.usesLocal (depth true) (ordinary true) = true ∧
    Available (heap true) (target true) ∧
    (∃ innerEntry innerBody innerDepth innerOrdinary,
      body true = .mu innerEntry innerBody innerDepth innerOrdinary ∧
      InternedFreshOrdinaryDepthHeap.usesLocal innerDepth innerOrdinary = false) ∧
    ResultFacts true ∧ left true = right true ∧ left true = target true := by
  have firstDone : firstRun true = .done (left true) (middle true) := by cbv
  have secondDone : secondRun true = .done (right true) (after true) := by cbv
  exact ⟨built_done true,ready true,by cbv,by cbv,target_available true,
    ⟨_,_,_,_,by cbv,by cbv⟩,result_facts true firstDone secondDone,by cbv,by cbv⟩

end MicroCFTA.MuFusionRootKernels
#check @MicroCFTA.MuFusionRootKernels.union_duplicate_dead_rows
#print axioms MicroCFTA.MuFusionRootKernels.union_duplicate_dead_rows
#check @MicroCFTA.MuFusionRootKernels.union_raw_unused_inner
#print axioms MicroCFTA.MuFusionRootKernels.union_raw_unused_inner
