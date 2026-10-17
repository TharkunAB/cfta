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

namespace MicroCFTA.RetainedMuProposalKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction
open InternedBinderProtocol (Reference NodeKey)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentNativeMuPublication (History Written)

private def expression (usedInner : Bool) : Syntax Nat Bool :=
  .binder false (.node [.mk 0 false [.var 0,
    .binder false (.node [.mk 1 true (if usedInner then [.var 1,.var 0] else [.var 1])])]])
private def built (used : Bool) := build (expression used) [] empty
private def root (used : Bool) : Value Nat Bool :=
  match built used with | .done value _ => value | .pending .. => .empty
private def heap (used : Bool) := (built used).state
private def fields : Value Nat Bool → Interned NodeKey × Value Nat Bool × Value Nat Bool × Value Nat Bool
  | .mu entry body depth ordinary => (entry,body,depth,ordinary)
  | _ => (⟨0,.node []⟩,.empty,.empty,.empty)
private def selected (used inner : Bool) : Value Nat Bool :=
  if inner then ((children (fields (root used)).2.1)[1]?).getD .empty else root used
private def entry (used inner : Bool) := (fields (selected used inner)).1
private def body (used inner : Bool) := (fields (selected used inner)).2.1
private def depth (used inner : Bool) := (fields (selected used inner)).2.2.1
private def ordinary (used inner : Bool) := (fields (selected used inner)).2.2.2
private def key (used inner : Bool) := muKey (depth used inner) (ordinary used inner)
private def target (used inner aliasOuter : Bool) : Value Nat Bool :=
  if aliasOuter then .reference (.interned (fields (root used)).1.identity)
  else .reference (.uninterned (ordinaryLevel (depth used inner)))
private def bodyEnv (used inner aliasOuter : Bool) : InternedStoredSubstitution.Environment Nat Bool :=
  InternedStoredSubstitutionRebind.replacement (.interned (entry used inner).identity)
    (target used inner aliasOuter)
private def ordinaryEnv (used inner aliasOuter : Bool) : InternedStoredSubstitution.Environment Nat Bool :=
  InternedStoredSubstitutionRebind.replacement (.uninterned (ordinaryLevel (depth used inner)))
    (target used inner aliasOuter)
private def firstRun (used inner aliasOuter : Bool) :=
  InternedFreshOrdinaryStoredSubstitution.execute (body used inner) (bodyEnv used inner aliasOuter) (heap used)
private def left (used inner aliasOuter : Bool) : Value Nat Bool :=
  match firstRun used inner aliasOuter with | .done value _ => value | .pending .. => .empty
private def middle (used inner aliasOuter : Bool) := (firstRun used inner aliasOuter).state
private def secondRun (used inner aliasOuter : Bool) :=
  InternedFreshOrdinaryStoredSubstitution.execute (ordinary used inner)
    (ordinaryEnv used inner aliasOuter) (middle used inner aliasOuter)
private def right (used inner aliasOuter : Bool) : Value Nat Bool :=
  match secondRun used inner aliasOuter with | .done value _ => value | .pending .. => .empty
private def finalHeap (used inner aliasOuter : Bool) := (secondRun used inner aliasOuter).state

private theorem built_done (used : Bool) : built used = .done (root used) (heap used) := by
  cases used <;> cbv
private theorem present (used inner : Bool) :
    (heap used).nodeRecords (key used inner) =
      some (.mu (entry used inner) (body used inner) (depth used inner) (ordinary used inner)) := by
  cases used <;> cases inner <;> cbv
private theorem ready (used : Bool) : Ready (heap used) :=
  SourceEqualityRequiredCache.constructed (expression used) (root used) (heap used) (built_done used)
private theorem target_available (used inner aliasOuter : Bool) :
    Available (heap used) (target used inner aliasOuter) := by
  cases aliasOuter with
  | false =>
      apply reference_available
      intro identity member
      simp only [Value.free, List.mem_singleton] at member
      cases member
  | true =>
      apply reference_available
      intro identity member
      have same : identity = (fields (root used)).1.identity := by simpa only [Value.free,
        List.mem_singleton, Reference.interned.injEq] using member
      subst identity
      refine ⟨muKey (fields (root used)).2.2.1 (fields (root used)).2.2.2, ?_⟩
      cases used <;> cbv

private theorem run_pair (used inner aliasOuter : Bool)
    (firstDone : firstRun used inner aliasOuter = .done (left used inner aliasOuter) (middle used inner aliasOuter))
    (secondDone : secondRun used inner aliasOuter = .done (right used inner aliasOuter) (finalHeap used inner aliasOuter)) :
    Keeps (heap used) (middle used inner aliasOuter) ∧
    Keeps (middle used inner aliasOuter) (finalHeap used inner aliasOuter) ∧
    Available (finalHeap used inner aliasOuter) (left used inner aliasOuter) ∧
    Available (finalHeap used inner aliasOuter) (right used inner aliasOuter) ∧
    Nonempty (History empty (finalHeap used inner aliasOuter)) ∧
    Written empty (key used inner) (.mu (entry used inner) (body used inner) (depth used inner) (ordinary used inner)) ∧
    (finalHeap used inner aliasOuter).nodeRecords (key used inner) =
      some (.mu (entry used inner) (body used inner) (depth used inner) (ordinary used inner)) ∧
    InternedFreshOrdinaryStoredSubstitution.execute (body used inner) (bodyEnv used inner aliasOuter)
      (finalHeap used inner aliasOuter) = .done (left used inner aliasOuter) (finalHeap used inner aliasOuter) ∧
    InternedFreshOrdinaryStoredSubstitution.execute (ordinary used inner) (ordinaryEnv used inner aliasOuter)
      (finalHeap used inner aliasOuter) = .done (right used inner aliasOuter) (finalHeap used inner aliasOuter) := by
  obtain ⟨actualLeft,actualMiddle,actualRight,actualAfter,first,second,firstKeeps,secondKeeps,
      leftAvailable,rightAvailable,firstHistory,secondHistory,whole,retained,writer,firstWarm,secondWarm⟩ :=
    SourceCurrentStoredReconstructionReplay.mu (key used inner) (entry used inner) (body used inner)
      (depth used inner) (ordinary used inner) (target used inner aliasOuter) (heap used)
      (ready used) (present used inner) (target_available used inner aliasOuter)
      (SourceCurrentNativeMuPublication.closed_history (expression used))
  have firstEq : .done (left used inner aliasOuter) (middle used inner aliasOuter) =
      (.done actualLeft actualMiddle : Outcome Nat Bool (Value Nat Bool)) := firstDone.symm.trans first
  have firstValues := Outcome.done.inj firstEq
  rcases firstValues with ⟨leftEq,middleEq⟩
  subst actualLeft actualMiddle
  have secondEq : .done (right used inner aliasOuter) (finalHeap used inner aliasOuter) =
      (.done actualRight actualAfter : Outcome Nat Bool (Value Nat Bool)) := secondDone.symm.trans second
  rcases Outcome.done.inj secondEq with ⟨rightEq,afterEq⟩
  subst actualRight actualAfter
  exact ⟨firstKeeps,secondKeeps,leftAvailable,rightAvailable,whole,writer,retained,firstWarm,secondWarm⟩

/-- Both reconstructed values agree in the raw-unused-inner example, with the own ordinary reference as replacement. -/
theorem raw_inner_reconstructed :
    build (expression false) [] empty = .done (root false) (heap false) ∧
    Ready (heap false) ∧
    (root false).free = [] ∧
    InternedFreshOrdinaryDepthHeap.usesLocal (depth false false) (ordinary false false) = true ∧
    Available (heap false) (target false false false) ∧
    firstRun false false false = .done (left false false false) (middle false false false) ∧
    secondRun false false false = .done (right false false false) (finalHeap false false false) ∧
    left false false false = right false false false ∧
    Keeps (heap false) (middle false false false) ∧
    Keeps (middle false false false) (finalHeap false false false) ∧
    Available (finalHeap false false false) (left false false false) ∧
    Available (finalHeap false false false) (right false false false) ∧
    Nonempty (History empty (finalHeap false false false)) ∧
    Written empty (key false false) (.mu (entry false false) (body false false) (depth false false) (ordinary false false)) ∧
    (finalHeap false false false).nodeRecords (key false false) =
      some (.mu (entry false false) (body false false) (depth false false) (ordinary false false)) ∧
    InternedFreshOrdinaryStoredSubstitution.execute (body false false) (bodyEnv false false false)
      (finalHeap false false false) = .done (left false false false) (finalHeap false false false) ∧
    InternedFreshOrdinaryStoredSubstitution.execute (ordinary false false) (ordinaryEnv false false false)
      (finalHeap false false false) = .done (right false false false) (finalHeap false false false) := by
  have one : firstRun false false false = .done (left false false false) (middle false false false) := by cbv
  have two : secondRun false false false = .done (right false false false) (finalHeap false false false) := by cbv
  exact ⟨built_done false,ready false,by cbv,by cbv,target_available false false false,one,two,
    by cbv,run_pair false false false one two⟩

/-- A nested used Mu has equal reconstructed values when replacement aliases its captured outer self. -/
theorem nested_used_capture_alias :
    build (expression true) [] empty = .done (root true) (heap true) ∧
    Ready (heap true) ∧
    (root true).free = [] ∧
    (selected true true).free ≠ [] ∧
    InternedFreshOrdinaryDepthHeap.usesLocal (depth true true) (ordinary true true) = true ∧
    Available (heap true) (target true true true) ∧
    firstRun true true true = .done (left true true true) (middle true true true) ∧
    secondRun true true true = .done (right true true true) (finalHeap true true true) ∧
    left true true true = right true true true ∧
    Keeps (heap true) (middle true true true) ∧
    Keeps (middle true true true) (finalHeap true true true) ∧
    Available (finalHeap true true true) (left true true true) ∧
    Available (finalHeap true true true) (right true true true) ∧
    Nonempty (History empty (finalHeap true true true)) ∧
    Written empty (key true true) (.mu (entry true true) (body true true) (depth true true) (ordinary true true)) ∧
    (finalHeap true true true).nodeRecords (key true true) =
      some (.mu (entry true true) (body true true) (depth true true) (ordinary true true)) ∧
    InternedFreshOrdinaryStoredSubstitution.execute (body true true) (bodyEnv true true true)
      (finalHeap true true true) = .done (left true true true) (finalHeap true true true) ∧
    InternedFreshOrdinaryStoredSubstitution.execute (ordinary true true) (ordinaryEnv true true true)
      (finalHeap true true true) = .done (right true true true) (finalHeap true true true) := by
  have one : firstRun true true true = .done (left true true true) (middle true true true) := by cbv
  have two : secondRun true true true = .done (right true true true) (finalHeap true true true) := by cbv
  refine ⟨built_done true,ready true,by cbv,?_,by cbv,target_available true true true,one,two,
    by cbv,run_pair true true true one two⟩
  intro impossible
  cbv at impossible
  cases impossible

end MicroCFTA.RetainedMuProposalKernels
#check @MicroCFTA.RetainedMuProposalKernels.raw_inner_reconstructed
#print axioms MicroCFTA.RetainedMuProposalKernels.raw_inner_reconstructed
#check @MicroCFTA.RetainedMuProposalKernels.nested_used_capture_alias
#print axioms MicroCFTA.RetainedMuProposalKernels.nested_used_capture_alias
