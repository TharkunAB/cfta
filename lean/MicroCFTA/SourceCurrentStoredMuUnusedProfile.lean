import MicroCFTA.SourceCurrentStoredMuProfileContract
import MicroCFTA.InternedFreshOrdinaryDepthHeap

/-!
# Pure profiles after unused smart Mu cleanup

An unused local reduces to its Empty assigned profile. The proof covers
both the stored body return and bare-self cleanup. The actual probe-depth
invariant excludes a retained Mu in this branch. No marker is required.
-/
namespace MicroCFTA.SourceCurrentStoredMuUnusedProfile
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedBinderProtocol (Reference NodeKey)
open InternedNestedConstruction (finish)
open InternedRootProfile (Profile Equivalent)
open InternedFreshOrdinaryConstruction (ordinaryLevel)
open InternedFreshOrdinaryDepthHeap (usesLocal decodedDepth)
open SourceCurrentStoredProfileFunction (denote)
open SourceCurrentStoredMuProfileContract (shadow Correct)

/-- The unused smart return has the ordinary probe profile with an Empty local. -/
theorem smart_unused (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state)
    (available : Available state (.mu entry body depth ordinary))
    (depthCorrect : InternedFreshOrdinaryDepthHeap.Correct entry body depth ordinary)
    (correct : Correct entry body depth ordinary) (unused : usesLocal depth ordinary = false)
    (assignment : Reference → Profile) :
    Equivalent (denote (finish true (.mu entry body depth ordinary)) assignment)
      (denote ordinary (shadow (.uninterned (ordinaryLevel depth)) (some []) assignment)) := by
  have matched := correct assignment (some [])
  by_cases absent : .interned entry.identity ∉ body.free
  · have finished : finish true (.mu entry body depth ordinary) = body := by
      simp [finish,cleanup,absent]
    rw [finished]
    have unchanged := SourceCurrentStoredProfileFunction.congr body state coherent
      (available.children body (by simp [InternedProbeProvenance.children])) assignment
      (shadow (.interned entry.identity) (some []) assignment) (by
        intro name member
        have different : name ≠ .interned entry.identity := fun same => absent (same ▸ member)
        simp only [shadow,different,ite_false])
    rw [unchanged]
    exact matched
  · by_cases bare : body.referenceOf = .ref (.interned entry.identity)
    · have finished : finish true (.mu entry body depth ordinary) = .empty := by
        simp [finish,cleanup,absent,bare]
      rw [finished,SourceCurrentStoredProfileFunction.empty]
      have same := (referenceOf_self_iff (.interned entry.identity) body).mp bare
      rw [same,SourceCurrentStoredProfileFunction.reference] at matched
      simpa only [shadow,ite_true] using matched
    · have bodyDepth : body.depth = depth.depth := by
        simpa only [finish,Value.depth,decodedDepth,Bool.not_false,Bool.true_or,
          Bool.false_eq_true,ite_true,ite_false,Nat.add_right_cancel_iff] using (depthCorrect false).1
      have finished : finish true (.mu entry body depth ordinary) = .mu entry body depth ordinary := by
        simp [finish,cleanup,absent,bare]
      have smart := (depthCorrect true).1
      rw [finished,Value.depth,bodyDepth] at smart
      simp only [decodedDepth,Bool.not_true,Bool.false_or,unused,Bool.false_eq_true,ite_false] at smart
      omega

end MicroCFTA.SourceCurrentStoredMuUnusedProfile
