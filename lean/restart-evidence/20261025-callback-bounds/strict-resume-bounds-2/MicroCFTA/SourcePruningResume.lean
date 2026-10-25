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

/-- A total forest gives a finite resume and its actual complete compression frame. -/
theorem resume_complete (current : Nat) (term : Term (PartialSymbol Symbol))
    (pending : Pending Symbol) (before : State Symbol Guard)
    (total : UnionFind.Total before.representatives) :
    ∃ (fuel : Nat) (result : Option (Pending Symbol)) (after : State Symbol Guard),
      Success (resume fuel current term pending) before result after ∧ Frame before after := by
  have step : ∀ (pendingPart : Template.Pattern Symbol × Nat) (previous : State Symbol Guard),
      UnionFind.Total previous.representatives →
        ∃ (fuel : Nat) (result : Option (Pending Symbol)) (next : State Symbol Guard),
          Success (part fuel current term pendingPart) previous result next ∧
            UnionFind.Total next.representatives := by
    intro pendingPart previous previousTotal
    obtain ⟨fuel, root, next, reading, nextTotal⟩ :=
      representative_terminates previous previousTotal pendingPart.2
    refine ⟨fuel, (if root = current then matchPartial pendingPart.1 term else some [(pendingPart.1, root)]),
      next, ?_, nextTotal⟩
    exact (part_success fuel current term pendingPart previous next _).mpr ⟨root, reading, rfl⟩
  obtain ⟨fuel, results, after, traversed, _afterTotal⟩ :=
    mapM_terminates (fun fuel pendingPart => part fuel current term pendingPart)
      (fun state : State Symbol Guard => UnionFind.Total state.representatives)
      (fun fuel extra pendingPart => part_moreFuel fuel extra current term pendingPart)
      step pending before total
  let result := (results.mapM id : Option (List (Pending Symbol))).map (fun pieces => pieces.flatMap id)
  have completed : Success (resume fuel current term pending) before result after := by
    unfold resume
    exact (success_bind _ _ _ _ _).mpr
      ⟨results, after, traversed, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩
  exact ⟨fuel, result, after, completed, resume_frame fuel current term pending before after result total completed⟩

/-- Resuming allocated parked references preserves safety and the rendering state. -/
theorem resume_read (fuel current : Nat) (term : Term (PartialSymbol Symbol))
    (pending : Pending Symbol) (before after : State Symbol Guard) (result : Option (Pending Symbol))
    (safe : Safe before) (bounded : ∀ pendingPart ∈ pending, pendingPart.2 < before.counter)
    (success : Success (resume fuel current term pending) before result after) :
    EnumerationDriver.RenderStable before after := by
  unfold resume at success
  obtain ⟨results, middle, traversed, final⟩ := (success_bind _ _ _ _ _).mp success
  have step : ∀ pendingPart ∈ pending, ∀ previous output next,
      EnumerationDriver.RenderStable before previous →
        Success (part fuel current term pendingPart) previous output next →
          EnumerationDriver.RenderStable before next := by
    intro pendingPart member previous output next previousStable reading
    obtain ⟨root, representativeRead, _projected⟩ :=
      (part_success fuel current term pendingPart previous next output).mp reading
    have inside : pendingPart.2 < previous.counter := by
      rw [previousStable.counter]
      exact bounded pendingPart member
    exact previousStable.trans (EnumerationReferences.representative_read fuel pendingPart.2 root previous next
      previousStable.safe inside representativeRead)
  have middleStable := mapM_invariant (part fuel current term)
    (EnumerationDriver.RenderStable before) pending step before middle results
      (EnumerationDriver.RenderStable.refl before safe) traversed
  obtain ⟨_projected, same⟩ := (success_pure _ _ _ _).mp final
  subst after
  exact middleStable

private theorem parts_bounded (fuel current : Nat) (term : Term (PartialSymbol Symbol))
    (pending : Pending Symbol) (before after : State Symbol Guard)
    (results : List (Option (Pending Symbol))) (safe : Safe before)
    (bounded : PendingBound before.counter pending)
    (termBound : EnumerationPartialBounds.TermBound before.counter term)
    (success : Success (pending.mapM (part fuel current term)) before results after) :
    EnumerationDriver.RenderStable before after ∧
      ∀ result ∈ results, ∀ resumed, result = some resumed → PendingBound after.counter resumed := by
  induction pending generalizing before after results with
  | nil =>
      obtain ⟨rfl, rfl⟩ := (success_pure [] results before after).mp success
      exact ⟨.refl _ safe, by simp⟩
  | cons first rest ih =>
      rw [List.mapM_cons] at success
      obtain ⟨firstResult, middle, firstRead, continued⟩ := (success_bind _ _ _ _ _).mp success
      obtain ⟨tailResults, last, restRead, final⟩ := (success_bind _ _ _ _ _).mp continued
      obtain ⟨rfl, rfl⟩ := (success_pure (firstResult :: tailResults) results last after).mp final
      obtain ⟨root, reading, projected⟩ := (part_success fuel current term first before middle firstResult).mp firstRead
      have inside := bounded first (by simp)
      have firstStable := EnumerationReferences.representative_read fuel first.2 root before middle safe inside reading
      have rootInside : root < before.counter := by
        obtain ⟨found, lookup, same, _state⟩ := (representative_success fuel first.2 before middle root).mp reading
        rw [same]
        exact reaches_bounded before.representatives before.counter safe.1.forest
          (UnionFind.findRoot_correct fuel before.representatives first.2 found lookup).1 inside
      have firstBound : ∀ resumed, firstResult = some resumed → PendingBound middle.counter resumed := by
        intro resumed same
        rw [projected] at same
        split at same
        · rw [firstStable.counter]
          exact matchPartial_bounded before.counter first.1 term resumed termBound same
        · have identical := Option.some.inj same
          subst resumed
          intro entry member
          obtain rfl := List.mem_singleton.mp member
          simpa only [firstStable.counter] using rootInside
      obtain ⟨lastStable, tailBound⟩ := ih middle after tailResults firstStable.safe
        (by intro entry member; rw [firstStable.counter]; exact bounded entry (List.mem_cons_of_mem first member))
        (by simpa only [firstStable.counter] using termBound) restRead
      refine ⟨firstStable.trans lastStable, ?_⟩
      intro result member resumed same
      rcases List.mem_cons.mp member with rfl | member
      · rw [lastStable.counter]
        exact firstBound resumed same
      · exact tailBound result member resumed same

omit [DecidableEq Symbol] in
private theorem sequenced_bounded (limit : Nat) (results : List (Option (Pending Symbol)))
    (pieces : List (Pending Symbol))
    (bounded : ∀ result ∈ results, ∀ pending, result = some pending → PendingBound limit pending)
    (sequenced : (results.mapM id : Option (List (Pending Symbol))) = some pieces) :
    PendingBound limit (pieces.flatMap id) := by
  induction results generalizing pieces with
  | nil =>
      have same : pieces = [] := by simpa using sequenced.symm
      subst pieces
      simp [PendingBound]
  | cons result rest ih =>
      cases result with
      | none => simp [List.mapM_cons] at sequenced
      | some pending =>
          cases restSequence : (rest.mapM id : Option (List (Pending Symbol))) with
          | none => simp [List.mapM_cons, restSequence] at sequenced
          | some restPieces =>
              have same : pieces = pending :: restPieces := by
                simpa [List.mapM_cons, restSequence] using sequenced.symm
              subst pieces
              have firstBound := bounded (some pending) (by simp) pending rfl
              have restBound := ih restPieces (fun result member => bounded result (List.mem_cons_of_mem _ member)) restSequence
              intro entry member
              simp only [List.flatMap_cons, id_eq, List.mem_append] at member
              rcases member with member | member
              · exact firstBound entry member
              · exact restBound entry member

/-- Successful resumption keeps every returned parked ID inside the allocation domain. -/
theorem resume_bounded (fuel current : Nat) (term : Term (PartialSymbol Symbol))
    (pending : Pending Symbol) (before after : State Symbol Guard) (result : Option (Pending Symbol))
    (safe : Safe before) (bounded : PendingBound before.counter pending)
    (termBound : EnumerationPartialBounds.TermBound before.counter term)
    (success : Success (resume fuel current term pending) before result after) :
    ∀ resumed, result = some resumed → PendingBound after.counter resumed := by
  unfold resume at success
  obtain ⟨results, middle, traversed, final⟩ := (success_bind _ _ _ _ _).mp success
  obtain ⟨_stable, resultBounds⟩ := parts_bounded fuel current term pending before middle results safe bounded termBound traversed
  obtain ⟨projected, rfl⟩ := (success_pure _ result middle after).mp final
  intro resumed same
  rw [projected] at same
  cases sequenced : (results.mapM id : Option (List (Pending Symbol))) with
  | none => simp [sequenced] at same
  | some pieces =>
      have identical : resumed = pieces.flatMap id := by simpa [sequenced] using same.symm
      subst resumed
      exact sequenced_bounded after.counter results pieces resultBounds sequenced

end MicroCFTA.SourcePruningResume
