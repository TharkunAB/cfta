import MicroCFTA.SourcePruningPartialMatch
import MicroCFTA.EnumerationObservations

/-!
# Resume parked partial pruning matches

The source reads every parked representative before combining the optional
match results. Pending pieces retain their order and repeated entries.
-/
namespace MicroCFTA.SourcePruningResume
open Language EnumerationState EnumerationCorrectness EnumerationSchedule
open EnumerationCompressionFrame EnumerationObservations EnumerationExecution
open SourcePruningPartialMatch

local instance pruningResumeMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

local instance pruningResumeLawfulMonadList : LawfulMonad List where
  map_const := rfl
  id_map := by intro α xs; simp [Functor.map]
  seqLeft_eq := by
    intros
    simp [SeqLeft.seqLeft, Seq.seq, Functor.map, List.flatMap_map, ← List.map_eq_flatMap]
    simp only [List.map_const']
  seqRight_eq := by
    intros
    simp only [SeqRight.seqRight, Seq.seq, Functor.map, List.flatMap_map]
    simp
  pure_seq := by intros; simp [Seq.seq, Functor.map, pure]
  bind_pure_comp := by intros; simp [bind, pure, Functor.map, ← List.map_eq_flatMap]
  bind_map := by intros; rfl
  pure_bind := by intros; simp [pure, bind]
  bind_assoc := by intros; exact List.flatMap_assoc

variable {Symbol Guard : Type} [DecidableEq Symbol]

/-- Read one parked representative, then inspect the supplied partial term. -/
private def part (fuel current : Nat) (term : Term (PartialSymbol Symbol))
    (pending : Template.Pattern Symbol × Nat) : EnumerateM Symbol Guard (Option (Pending Symbol)) := do
  let root ← representative fuel pending.2
  pure (if root = current then matchPartial pending.1 term else some [(pending.1, root)])

/-- Read all parked parts before sequencing and concatenating their pure results. -/
def resume (fuel current : Nat) (term : Term (PartialSymbol Symbol))
    (pending : Pending Symbol) : EnumerateM Symbol Guard (Option (Pending Symbol)) := do
  let results ← pending.mapM (part fuel current term)
  pure ((results.mapM id : Option (List (Pending Symbol))).map (fun pieces => pieces.flatMap id))

private theorem part_success (fuel current : Nat) (term : Term (PartialSymbol Symbol))
    (pending : Template.Pattern Symbol × Nat) (before after : State Symbol Guard)
    (result : Option (Pending Symbol)) :
    Success (part fuel current term pending) before result after ↔
      ∃ root, Success (representative fuel pending.2) before root after ∧
        result = (if root = current then matchPartial pending.1 term else some [(pending.1, root)]) := by
  unfold part
  constructor
  · intro success
    obtain ⟨root, middle, reading, final⟩ := (success_bind _ _ _ _ _).mp success
    obtain ⟨projected, same⟩ := (success_pure _ result middle after).mp final
    subst after
    exact ⟨root, reading, projected⟩
  · rintro ⟨root, reading, projected⟩
    exact (success_bind _ _ _ _ _).mpr
      ⟨root, after, reading, (success_pure _ result after after).mpr ⟨projected, rfl⟩⟩

private theorem part_frame (fuel current : Nat) (term : Term (PartialSymbol Symbol))
    (pending : Template.Pattern Symbol × Nat) (before after : State Symbol Guard)
    (result : Option (Pending Symbol)) (total : UnionFind.Total before.representatives)
    (success : Success (part fuel current term pending) before result after) : Frame before after := by
  obtain ⟨root, reading, _⟩ := (part_success fuel current term pending before after result).mp success
  exact representative_frame fuel pending.2 root before after total reading

private theorem part_agrees (leftFuel rightFuel current : Nat) (term : Term (PartialSymbol Symbol))
    (pending : Template.Pattern Symbol × Nat) (left right leftAfter rightAfter : State Symbol Guard)
    (leftResult rightResult : Option (Pending Symbol)) (frame : Frame left right)
    (total : UnionFind.Total left.representatives)
    (leftRead : Success (part leftFuel current term pending) left leftResult leftAfter)
    (rightRead : Success (part rightFuel current term pending) right rightResult rightAfter) :
    leftResult = rightResult ∧ Frame leftAfter rightAfter := by
  obtain ⟨leftRoot, leftReading, leftProjected⟩ :=
    (part_success leftFuel current term pending left leftAfter leftResult).mp leftRead
  obtain ⟨rightRoot, rightReading, rightProjected⟩ :=
    (part_success rightFuel current term pending right rightAfter rightResult).mp rightRead
  obtain ⟨same, finalFrame⟩ := representative_agrees leftFuel rightFuel pending.2
    left right leftAfter rightAfter leftRoot rightRoot frame total leftReading rightReading
  refine ⟨?_, finalFrame⟩
  rw [leftProjected, rightProjected, same]

private theorem part_transport (leftFuel current : Nat) (term : Term (PartialSymbol Symbol))
    (pending : Template.Pattern Symbol × Nat) (left right leftAfter : State Symbol Guard)
    (result : Option (Pending Symbol)) (frame : Frame left right)
    (total : UnionFind.Total left.representatives)
    (leftRead : Success (part leftFuel current term pending) left result leftAfter) :
    ∃ rightFuel rightAfter, Success (part rightFuel current term pending) right result rightAfter ∧
      Frame leftAfter rightAfter := by
  obtain ⟨root, reading, projected⟩ :=
    (part_success leftFuel current term pending left leftAfter result).mp leftRead
  obtain ⟨rightFuel, rightAfter, rightReading, finalFrame⟩ :=
    representative_transport leftFuel pending.2 left right leftAfter root frame total reading
  exact ⟨rightFuel, rightAfter,
    (part_success rightFuel current term pending right rightAfter result).mpr
      ⟨root, rightReading, projected⟩, finalFrame⟩

private theorem part_moreFuel (fuel extra current : Nat) (term : Term (PartialSymbol Symbol))
    (pending : Template.Pattern Symbol × Nat) :
    Retains (part (Symbol := Symbol) (Guard := Guard) fuel current term pending)
      (part (fuel + extra) current term pending) := by
  unfold part
  exact retains_bind _ _ _ _ (representative_moreFuel fuel extra pending.2) (fun _ => retains_refl _)

private theorem parts_agree (leftFuel rightFuel current : Nat) (term : Term (PartialSymbol Symbol))
    (pending : Pending Symbol) (left right leftAfter rightAfter : State Symbol Guard)
    (leftResults rightResults : List (Option (Pending Symbol))) (frame : Frame left right)
    (total : UnionFind.Total left.representatives)
    (leftRead : Success (pending.mapM (part leftFuel current term)) left leftResults leftAfter)
    (rightRead : Success (pending.mapM (part rightFuel current term)) right rightResults rightAfter) :
    leftResults = rightResults ∧ Frame leftAfter rightAfter := by
  induction pending generalizing left right leftAfter rightAfter leftResults rightResults with
  | nil =>
      obtain ⟨leftEq, leftSame⟩ := (success_pure [] leftResults left leftAfter).mp leftRead
      obtain ⟨rightEq, rightSame⟩ := (success_pure [] rightResults right rightAfter).mp rightRead
      exact ⟨leftEq.trans rightEq.symm, by simpa only [leftSame, rightSame] using frame⟩
  | cons first rest ih =>
      rw [List.mapM_cons] at leftRead rightRead
      obtain ⟨leftResult, leftMiddle, leftFirst, leftContinued⟩ := (success_bind _ _ _ _ _).mp leftRead
      obtain ⟨leftTail, leftLast, leftRest, leftFinal⟩ := (success_bind _ _ _ _ _).mp leftContinued
      obtain ⟨rightResult, rightMiddle, rightFirst, rightContinued⟩ := (success_bind _ _ _ _ _).mp rightRead
      obtain ⟨rightTail, rightLast, rightRest, rightFinal⟩ := (success_bind _ _ _ _ _).mp rightContinued
      obtain ⟨sameFirst, middleFrame⟩ := part_agrees leftFuel rightFuel current term first
        left right leftMiddle rightMiddle leftResult rightResult frame total leftFirst rightFirst
      have middleTotal := (part_frame leftFuel current term first left leftMiddle leftResult total leftFirst).total total
      obtain ⟨sameTail, lastFrame⟩ := ih leftMiddle rightMiddle leftLast rightLast leftTail rightTail
        middleFrame middleTotal leftRest rightRest
      obtain ⟨leftEq, leftSame⟩ := (success_pure (leftResult :: leftTail) leftResults leftLast leftAfter).mp leftFinal
      obtain ⟨rightEq, rightSame⟩ := (success_pure (rightResult :: rightTail) rightResults rightLast rightAfter).mp rightFinal
      refine ⟨?_, ?_⟩
      · rw [leftEq, rightEq, sameFirst, sameTail]
      · simpa only [leftSame, rightSame] using lastFrame

private theorem parts_transport (leftFuel current : Nat) (term : Term (PartialSymbol Symbol))
    (pending : Pending Symbol) (left right leftAfter : State Symbol Guard)
    (results : List (Option (Pending Symbol))) (frame : Frame left right)
    (total : UnionFind.Total left.representatives)
    (leftRead : Success (pending.mapM (part leftFuel current term)) left results leftAfter) :
    ∃ rightFuel rightAfter,
      Success (pending.mapM (part rightFuel current term)) right results rightAfter ∧
      Frame leftAfter rightAfter := by
  induction pending generalizing left right leftAfter results with
  | nil =>
      obtain ⟨resultsEq, leftSame⟩ := (success_pure [] results left leftAfter).mp leftRead
      exact ⟨0, right, (success_pure [] results right right).mpr ⟨resultsEq, rfl⟩,
        by simpa only [leftSame] using frame⟩
  | cons first rest ih =>
      rw [List.mapM_cons] at leftRead
      obtain ⟨firstResult, leftMiddle, leftFirst, leftContinued⟩ := (success_bind _ _ _ _ _).mp leftRead
      obtain ⟨tailResults, leftLast, leftRest, leftFinal⟩ := (success_bind _ _ _ _ _).mp leftContinued
      obtain ⟨resultsEq, leftSame⟩ := (success_pure (firstResult :: tailResults) results leftLast leftAfter).mp leftFinal
      obtain ⟨firstFuel, rightMiddle, rightFirst, middleFrame⟩ :=
        part_transport leftFuel current term first left right leftMiddle firstResult frame total leftFirst
      have middleTotal := (part_frame leftFuel current term first left leftMiddle firstResult total leftFirst).total total
      obtain ⟨restFuel, rightLast, rightRest, lastFrame⟩ :=
        ih leftMiddle rightMiddle leftLast tailResults middleFrame middleTotal leftRest
      refine ⟨firstFuel + restFuel, rightLast, ?_, ?_⟩
      · rw [List.mapM_cons]
        apply (success_bind _ _ _ _ _).mpr
        refine ⟨firstResult, rightMiddle,
          part_moreFuel firstFuel restFuel current term first right firstResult rightMiddle rightFirst, ?_⟩
        apply (success_bind _ _ _ _ _).mpr
        refine ⟨tailResults, rightLast, ?_,
          (success_pure (firstResult :: tailResults) results rightLast rightLast).mpr ⟨resultsEq, rfl⟩⟩
        have raised := retains_mapM _ _
          (fun pending => part_moreFuel restFuel firstFuel current term pending) rest
          rightMiddle tailResults rightLast rightRest
        simpa only [Nat.add_comm] using raised
      · simpa only [leftSame] using lastFrame

/-- Every successful resume preserves the complete compression frame. -/
theorem resume_frame (fuel current : Nat) (term : Term (PartialSymbol Symbol))
    (pending : Pending Symbol) (before after : State Symbol Guard) (result : Option (Pending Symbol))
    (total : UnionFind.Total before.representatives)
    (success : Success (resume fuel current term pending) before result after) : Frame before after := by
  unfold resume at success
  obtain ⟨results, middle, traversed, final⟩ := (success_bind _ _ _ _ _).mp success
  have step : ∀ pendingPart ∈ pending, ∀ previous output next, Frame before previous →
      Success (part fuel current term pendingPart) previous output next → Frame before next := by
    intro pendingPart _ previous output next previousFrame reading
    exact previousFrame.trans
      (part_frame fuel current term pendingPart previous next output (previousFrame.total total) reading)
  have middleFrame := mapM_invariant (part fuel current term) (Frame before) pending step
    before middle results (.refl before) traversed
  exact middleFrame.trans (pure_frame _ result middle after final)

/-- Independent successful resumes return the same ordered pending parts. -/
theorem resume_agrees (leftFuel rightFuel current : Nat) (term : Term (PartialSymbol Symbol))
    (pending : Pending Symbol) (left right leftAfter rightAfter : State Symbol Guard)
    (leftResult rightResult : Option (Pending Symbol)) (frame : Frame left right)
    (total : UnionFind.Total left.representatives)
    (leftRead : Success (resume leftFuel current term pending) left leftResult leftAfter)
    (rightRead : Success (resume rightFuel current term pending) right rightResult rightAfter) :
    leftResult = rightResult ∧ Frame leftAfter rightAfter := by
  unfold resume at leftRead rightRead
  obtain ⟨leftResults, leftMiddle, leftParts, leftFinal⟩ := (success_bind _ _ _ _ _).mp leftRead
  obtain ⟨rightResults, rightMiddle, rightParts, rightFinal⟩ := (success_bind _ _ _ _ _).mp rightRead
  obtain ⟨same, middleFrame⟩ := parts_agree leftFuel rightFuel current term pending
    left right leftMiddle rightMiddle leftResults rightResults frame total leftParts rightParts
  obtain ⟨leftEq, leftSame⟩ := (success_pure _ leftResult leftMiddle leftAfter).mp leftFinal
  obtain ⟨rightEq, rightSame⟩ := (success_pure _ rightResult rightMiddle rightAfter).mp rightFinal
  refine ⟨?_, ?_⟩
  · rw [leftEq, rightEq, same]
  · simpa only [leftSame, rightSame] using middleFrame

/-- One actual resume constructs a finite matching resume in the framed state. -/
theorem resume_transport (leftFuel current : Nat) (term : Term (PartialSymbol Symbol))
    (pending : Pending Symbol) (left right leftAfter : State Symbol Guard)
    (result : Option (Pending Symbol)) (frame : Frame left right)
    (total : UnionFind.Total left.representatives)
    (leftRead : Success (resume leftFuel current term pending) left result leftAfter) :
    ∃ rightFuel rightAfter, Success (resume rightFuel current term pending) right result rightAfter ∧
      Frame leftAfter rightAfter := by
  unfold resume at leftRead
  obtain ⟨results, leftMiddle, traversed, final⟩ := (success_bind _ _ _ _ _).mp leftRead
  obtain ⟨projected, leftSame⟩ := (success_pure _ result leftMiddle leftAfter).mp final
  obtain ⟨rightFuel, rightMiddle, rightParts, middleFrame⟩ :=
    parts_transport leftFuel current term pending left right leftMiddle results frame total traversed
  refine ⟨rightFuel, rightMiddle, ?_, ?_⟩
  · unfold resume
    exact (success_bind _ _ _ _ _).mpr
      ⟨results, rightMiddle, rightParts, (success_pure _ result rightMiddle rightMiddle).mpr ⟨projected, rfl⟩⟩
  · simpa only [leftSame] using middleFrame

/-- More fuel retains the exact optional result and complete final state. -/
theorem resume_moreFuel (fuel extra current : Nat) (term : Term (PartialSymbol Symbol))
    (pending : Pending Symbol) :
    Retains (resume (Symbol := Symbol) (Guard := Guard) fuel current term pending)
      (resume (fuel + extra) current term pending) := by
  unfold resume
  exact retains_bind _ _ _ _
    (retains_mapM _ _ (fun pendingPart => part_moreFuel fuel extra current term pendingPart) pending)
    (fun _ => retains_refl _)

end MicroCFTA.SourcePruningResume
