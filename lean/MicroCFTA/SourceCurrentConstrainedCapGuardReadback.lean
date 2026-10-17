import MicroCFTA.SourceCurrentConstrainedCapGuardHeap
import MicroCFTA.InternedFreshOrdinaryDepthHeap
import MicroCFTA.InternedProfileHeap

/-!
# Exact guard readback from the actual stored Mu probes

The depth observation identifies the actual cleanup branch. The retained
body-to-probe guard equality then determines the returned guard profile.
A warm request reads the earlier complete record and retains the same heap.
The actual source producer must supply the guard heap separately.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapGuardReadback
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedConstruction (finish request Outcome)
open InternedBinderProtocol (Reference NodeKey)
open InternedFreshOrdinaryDepthHeap (usesLocal)
variable {Symbol Guard : Type}

/-- The exact probes determine the guard profile for either literal binder form. -/
noncomputable def decoded (annotation : Guard → Prop) (smart : Bool) (depth ordinary : Value Symbol Guard) : Option Nat :=
  if !smart || usesLocal depth ordinary then
    if SourceCurrentConstrainedCapGuardDepth.profile annotation ordinary = some 0 then some 0 else none
  else SourceCurrentConstrainedCapGuardDepth.profile annotation ordinary

/-- The existing raw and smart depth equations identify the actual guard cleanup branch. -/
theorem finish_profile (annotation : Guard → Prop) (smart : Bool) (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard)
    (depthCorrect : InternedFreshOrdinaryDepthHeap.Correct entry body depth ordinary) :
    SourceCurrentConstrainedCapGuardDepth.profile annotation (finish smart (.mu entry body depth ordinary)) =
      if !smart || usesLocal depth ordinary then
        if SourceCurrentConstrainedCapGuardDepth.profile annotation body = some 0 then some 0 else none
      else SourceCurrentConstrainedCapGuardDepth.profile annotation body := by
  classical
  have bodyDepth : body.depth = depth.depth := by
    simpa only [finish, Value.depth, InternedFreshOrdinaryDepthHeap.decodedDepth, Bool.not_false,
      Bool.true_or, Bool.false_eq_true, ↓reduceIte, Nat.add_right_cancel_iff] using (depthCorrect false).1
  cases smart with
  | false => simp [finish, SourceCurrentConstrainedCapGuardDepth.profile]
  | true =>
      by_cases unused : .interned entry.identity ∉ body.free
      · have finished : finish true (.mu entry body depth ordinary) = body := by simp [finish, cleanup, unused]
        have observed := (depthCorrect true).1
        rw [finished, bodyDepth] at observed
        have used : usesLocal depth ordinary = false := by
          cases found : usesLocal depth ordinary <;> simp [InternedFreshOrdinaryDepthHeap.decodedDepth, found] at observed ⊢
        rw [finished]
        simp [used]
      · have present : .interned entry.identity ∈ body.free := by simpa using unused
        by_cases self : body.referenceOf = .ref (.interned entry.identity)
        · have bare := (referenceOf_self_iff (.interned entry.identity) body).mp self
          subst body
          have finished : finish true (.mu entry (.reference (.interned entry.identity)) depth ordinary) = .empty := by
            simp [finish, cleanup, Value.free, Value.referenceOf]
          have observed := (depthCorrect true).1
          rw [finished] at observed
          have used : usesLocal depth ordinary = false := by
            cases found : usesLocal depth ordinary <;> simp [InternedFreshOrdinaryDepthHeap.decodedDepth, found, Value.depth] at observed ⊢
          rw [finished]
          simp [used, SourceCurrentConstrainedCapGuardDepth.profile]
        · have finished : finish true (.mu entry body depth ordinary) = .mu entry body depth ordinary := by
            simp [finish, cleanup, present, self]
          have observed := (depthCorrect true).1
          rw [finished] at observed
          simp only [Value.depth, bodyDepth] at observed
          have used : usesLocal depth ordinary = true := by
            cases found : usesLocal depth ordinary <;> simp [InternedFreshOrdinaryDepthHeap.decodedDepth, found] at observed ⊢
          rw [finished]
          simp [used, SourceCurrentConstrainedCapGuardDepth.profile]

/-- A stored body's produced equality gives the exact probe-decoded returned guard profile. -/
theorem finish_of_probe (annotation : Guard → Prop) (smart : Bool) (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard)
    (depthCorrect : InternedFreshOrdinaryDepthHeap.Correct entry body depth ordinary)
    (guardCorrect : SourceCurrentConstrainedCapGuardHeap.Correct annotation body ordinary) :
    SourceCurrentConstrainedCapGuardDepth.profile annotation (finish smart (.mu entry body depth ordinary)) =
      decoded annotation smart depth ordinary := by
  rw [finish_profile annotation smart entry body depth ordinary depthCorrect]
  simpa only [decoded] using congrArg
    (fun profile => if !smart || usesLocal depth ordinary then if profile = some 0 then some 0 else none else profile) guardCorrect

/-- An exact canonical hit reads the earlier stored body's guard law at the current probes. -/
theorem hit_profile (annotation : Guard → Prop) (smart : Bool) (depth ordinary value : Value Symbol Guard)
    (state : State Symbol Guard) (facts : Facts state) (depthAvailable : Available state depth)
    (ordinaryAvailable : Available state ordinary) (depthHeap : InternedFreshOrdinaryDepthHeap.Heap state)
    (guardHeap : SourceCurrentConstrainedCapGuardHeap.Heap annotation state)
    (present : state.nodeRecords (muKey depth ordinary) = some value) :
    SourceCurrentConstrainedCapGuardDepth.profile annotation (finish smart value) = decoded annotation smart depth ordinary := by
  obtain ⟨entry, body, rfl⟩ := InternedProfileHeap.stored_probes depth ordinary value state facts depthAvailable ordinaryAvailable present
  exact finish_of_probe annotation smart entry body depth ordinary
    (depthHeap _ entry body depth ordinary present) (guardHeap _ entry body depth ordinary present)

/-- Unused-local warm cleanup derives the old winner's returned cap from its exact ordinary probe. -/
theorem hit_cap (annotation : Guard → Prop) (bound : Nat) (depth ordinary value : Value Symbol Guard)
    (state : State Symbol Guard) (facts : Facts state) (depthAvailable : Available state depth)
    (ordinaryAvailable : Available state ordinary) (depthHeap : InternedFreshOrdinaryDepthHeap.Heap state)
    (guardHeap : SourceCurrentConstrainedCapGuardHeap.Heap annotation state)
    (present : state.nodeRecords (muKey depth ordinary) = some value) (unused : usesLocal depth ordinary = false)
    (ordinaryCap : SourceCurrentConstrainedCap.Cap annotation bound ordinary) :
    SourceCurrentConstrainedCap.Cap annotation bound (finish true value) := by
  apply (SourceCurrentConstrainedCapGuardDepth.within_iff_cap annotation bound _).mp
  rw [hit_profile annotation true depth ordinary value state facts depthAvailable ordinaryAvailable depthHeap guardHeap present]
  simpa only [decoded, unused, Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte] using
    SourceCurrentConstrainedCapGuardDepth.profile_of_cap ordinaryCap

end MicroCFTA.SourceCurrentConstrainedCapGuardReadback
