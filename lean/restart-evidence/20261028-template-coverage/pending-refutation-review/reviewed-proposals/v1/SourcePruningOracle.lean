import MicroCFTA.SourcePruningTemplates
import MicroCFTA.SourcePruningResume
import MicroCFTA.EnumerationPartialCongruence
import MicroCFTA.EnumerationPartialTransport
import MicroCFTA.EnumerationPartialCompletion

/-!
# The concrete template pruning callback

The callback renders once, resumes every pending group, then combines the
pure match results. A rejected match does not omit later state reads.
-/
namespace MicroCFTA.SourcePruningOracle
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule
open EnumerationCompressionFrame EnumerationObservations EnumerationExecution
open SourcePruningPartialMatch SourcePruningTemplates
attribute [local instance] FormulaExecutable.formulaDecidableEq

local instance pruningOracleMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

local instance pruningOracleLawfulMonadList : LawfulMonad List where
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

variable {Guard : Type}

/-- The concrete-root fast path applies only when no check is pending. -/
private def idle (pending : List (Pending Symbol)) : Fragment Symbol → Bool
  | .node symbol children => pending.isEmpty &&
      !(isProgramRoot (.node symbol children))
  | .hole _ => false

/-- Render the fragment, then read every group before combining match results. -/
private def observe (graph : Graph Symbol Guard) (templates : List (Template.Pattern Symbol))
    (fuel : Nat) (pending : List (Pending Symbol)) (uv : Nat) (fragment : Fragment Symbol) :
    EnumerateM Symbol Guard (Bool × List (Pending Symbol)) := do
  let term ← expandPartial graph fuel fragment
  let resumed ← pending.mapM (SourcePruningResume.resume fuel uv term)
  pure (finishChecks resumed (startMatches templates term))

/-- The source callback preserves its early-rejection and empty-check branches. -/
def oracle (graph : Graph Symbol Guard) (templates : List (Template.Pattern Symbol))
    (fuel : Nat) : Oracle Symbol Guard (List (Pending Symbol)) := fun pending uv input =>
  match input with
  | .inr _ => pure (false, pending)
  | .inl fragment =>
      if rejectEarly templates fragment = true then pure (true, pending)
      else if idle pending fragment = true then pure (false, [])
      else observe graph templates fuel pending uv fragment

/-- The pre-expansion callback returns the pending checks without a state read. -/
theorem oracle_inr (graph : Graph Symbol Guard) (templates : List (Template.Pattern Symbol))
    (fuel : Nat) (pending : List (Pending Symbol)) (uv node : Nat) :
    oracle graph templates fuel pending uv (.inr node) = pure (false, pending) := rfl

private theorem groups_agree (leftFuel rightFuel current : Nat) (term : PartialTerm)
    (pending : List (Pending Symbol)) (left right leftAfter rightAfter : State Symbol Guard)
    (leftResults rightResults : List (Option (Pending Symbol))) (frame : Frame left right)
    (total : UnionFind.Total left.representatives)
    (leftRead : Success (pending.mapM (SourcePruningResume.resume leftFuel current term)) left leftResults leftAfter)
    (rightRead : Success (pending.mapM (SourcePruningResume.resume rightFuel current term)) right rightResults rightAfter) :
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
      obtain ⟨sameFirst, middleFrame⟩ := SourcePruningResume.resume_agrees leftFuel rightFuel current term first
        left right leftMiddle rightMiddle leftResult rightResult frame total leftFirst rightFirst
      have middleTotal := (SourcePruningResume.resume_frame leftFuel current term first left leftMiddle leftResult total leftFirst).total total
      obtain ⟨sameTail, lastFrame⟩ := ih leftMiddle rightMiddle leftLast rightLast leftTail rightTail
        middleFrame middleTotal leftRest rightRest
      obtain ⟨leftEq, leftSame⟩ := (success_pure (leftResult :: leftTail) leftResults leftLast leftAfter).mp leftFinal
      obtain ⟨rightEq, rightSame⟩ := (success_pure (rightResult :: rightTail) rightResults rightLast rightAfter).mp rightFinal
      refine ⟨?_, ?_⟩
      · rw [leftEq, rightEq, sameFirst, sameTail]
      · simpa only [leftSame, rightSame] using lastFrame

private theorem groups_transport (leftFuel current : Nat) (term : PartialTerm)
    (pending : List (Pending Symbol)) (left right leftAfter : State Symbol Guard)
    (results : List (Option (Pending Symbol))) (frame : Frame left right)
    (total : UnionFind.Total left.representatives)
    (leftRead : Success (pending.mapM (SourcePruningResume.resume leftFuel current term)) left results leftAfter) :
    ∃ rightFuel rightAfter,
      Success (pending.mapM (SourcePruningResume.resume rightFuel current term)) right results rightAfter ∧
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
        SourcePruningResume.resume_transport leftFuel current term first left right leftMiddle firstResult frame total leftFirst
      have middleTotal := (SourcePruningResume.resume_frame leftFuel current term first left leftMiddle firstResult total leftFirst).total total
      obtain ⟨restFuel, rightLast, rightRest, lastFrame⟩ :=
        ih leftMiddle rightMiddle leftLast tailResults middleFrame middleTotal leftRest
      refine ⟨firstFuel + restFuel, rightLast, ?_, ?_⟩
      · rw [List.mapM_cons]
        apply (success_bind _ _ _ _ _).mpr
        refine ⟨firstResult, rightMiddle,
          SourcePruningResume.resume_moreFuel firstFuel restFuel current term first right firstResult rightMiddle rightFirst, ?_⟩
        apply (success_bind _ _ _ _ _).mpr
        refine ⟨tailResults, rightLast, ?_,
          (success_pure (firstResult :: tailResults) results rightLast rightLast).mpr ⟨resultsEq, rfl⟩⟩
        have raised := retains_mapM _ _
          (fun pending => SourcePruningResume.resume_moreFuel restFuel firstFuel current term pending) rest
          rightMiddle tailResults rightLast rightRest
        simpa only [Nat.add_comm] using raised
      · simpa only [leftSame] using lastFrame

private theorem observe_frame (graph : Graph Symbol Guard)
    (templates : List (Template.Pattern Symbol)) (fuel : Nat) (pending : List (Pending Symbol))
    (uv : Nat) (fragment : Fragment Symbol) (before after : State Symbol Guard)
    (result : Bool × List (Pending Symbol)) (total : UnionFind.Total before.representatives)
    (success : Success (observe graph templates fuel pending uv fragment) before result after) :
    Frame before after := by
  unfold observe at success
  obtain ⟨term, middle, rendered, continued⟩ := (success_bind _ _ _ _ _).mp success
  obtain ⟨resumed, last, traversed, final⟩ := (success_bind _ _ _ _ _).mp continued
  have renderFrame := expandPartial_frame graph fuel fragment before middle term total rendered
  have step : ∀ group ∈ pending, ∀ previous output next, Frame middle previous →
      Success (SourcePruningResume.resume fuel uv term group) previous output next → Frame middle next := by
    intro group _ previous output next previousFrame reading
    exact previousFrame.trans (SourcePruningResume.resume_frame fuel uv term group previous next output
      (previousFrame.total (renderFrame.total total)) reading)
  have groupFrame := mapM_invariant (SourcePruningResume.resume fuel uv term) (Frame middle)
    pending step middle last resumed (.refl middle) traversed
  exact renderFrame.trans (groupFrame.trans (pure_frame _ result last after final))

private theorem observe_agrees (graph : Graph Symbol Guard)
    (templates : List (Template.Pattern Symbol)) (leftFuel rightFuel : Nat)
    (pending : List (Pending Symbol)) (uv : Nat) (fragment : Fragment Symbol)
    (left right leftAfter rightAfter : State Symbol Guard)
    (leftResult rightResult : Bool × List (Pending Symbol)) (frame : Frame left right)
    (total : UnionFind.Total left.representatives)
    (leftRead : Success (observe graph templates leftFuel pending uv fragment) left leftResult leftAfter)
    (rightRead : Success (observe graph templates rightFuel pending uv fragment) right rightResult rightAfter) :
    leftResult = rightResult ∧ Frame leftAfter rightAfter := by
  unfold observe at leftRead rightRead
  obtain ⟨leftTerm, leftMiddle, leftRender, leftContinued⟩ := (success_bind _ _ _ _ _).mp leftRead
  obtain ⟨leftGroups, leftLast, leftTraversal, leftFinal⟩ := (success_bind _ _ _ _ _).mp leftContinued
  obtain ⟨rightTerm, rightMiddle, rightRender, rightContinued⟩ := (success_bind _ _ _ _ _).mp rightRead
  obtain ⟨rightGroups, rightLast, rightTraversal, rightFinal⟩ := (success_bind _ _ _ _ _).mp rightContinued
  obtain ⟨termSame, renderFrame⟩ := expandPartial_agrees graph leftFuel rightFuel fragment
    left right leftMiddle rightMiddle leftTerm rightTerm frame total leftRender rightRender
  subst rightTerm
  have middleTotal := (expandPartial_frame graph leftFuel fragment left leftMiddle leftTerm total leftRender).total total
  obtain ⟨groupsSame, groupFrame⟩ := groups_agree leftFuel rightFuel uv leftTerm pending
    leftMiddle rightMiddle leftLast rightLast leftGroups rightGroups renderFrame middleTotal leftTraversal rightTraversal
  obtain ⟨leftEq, leftSame⟩ := (success_pure _ leftResult leftLast leftAfter).mp leftFinal
  obtain ⟨rightEq, rightSame⟩ := (success_pure _ rightResult rightLast rightAfter).mp rightFinal
  refine ⟨?_, ?_⟩
  · rw [leftEq, rightEq, groupsSame]
  · simpa only [leftSame, rightSame] using groupFrame

private theorem observe_moreFuel (graph : Graph Symbol Guard)
    (templates : List (Template.Pattern Symbol)) (fuel extra : Nat)
    (pending : List (Pending Symbol)) (uv : Nat) (fragment : Fragment Symbol) :
    Retains (observe graph templates fuel pending uv fragment)
      (observe graph templates (fuel + extra) pending uv fragment) := by
  unfold observe
  apply retains_bind _ _ _ _ (expandPartial_moreFuel graph fuel extra fragment)
  intro term
  exact retains_bind _ _ _ _
    (retains_mapM _ _ (fun group => SourcePruningResume.resume_moreFuel fuel extra uv term group) pending)
    (fun _ => retains_refl _)

private theorem observe_transport (graph : Graph Symbol Guard)
    (templates : List (Template.Pattern Symbol)) (leftFuel : Nat)
    (pending : List (Pending Symbol)) (uv : Nat) (fragment : Fragment Symbol)
    (left right leftAfter : State Symbol Guard) (result : Bool × List (Pending Symbol))
    (frame : Frame left right) (total : UnionFind.Total left.representatives)
    (leftRead : Success (observe graph templates leftFuel pending uv fragment) left result leftAfter) :
    ∃ rightFuel rightAfter,
      Success (observe graph templates rightFuel pending uv fragment) right result rightAfter ∧
      Frame leftAfter rightAfter := by
  unfold observe at leftRead
  obtain ⟨term, leftMiddle, rendered, continued⟩ := (success_bind _ _ _ _ _).mp leftRead
  obtain ⟨resumed, leftLast, traversed, final⟩ := (success_bind _ _ _ _ _).mp continued
  obtain ⟨resultEq, leftSame⟩ := (success_pure _ result leftLast leftAfter).mp final
  obtain ⟨renderFuel, rightMiddle, rightRender, renderFrame⟩ :=
    expandPartial_transport graph leftFuel fragment left right leftMiddle term frame total rendered
  have middleTotal := (expandPartial_frame graph leftFuel fragment left leftMiddle term total rendered).total total
  obtain ⟨groupFuel, rightLast, rightGroups, groupFrame⟩ := groups_transport leftFuel uv term pending
    leftMiddle rightMiddle leftLast resumed renderFrame middleTotal traversed
  refine ⟨renderFuel + groupFuel, rightLast, ?_, ?_⟩
  · unfold observe
    apply (success_bind _ _ _ _ _).mpr
    refine ⟨term, rightMiddle,
      expandPartial_moreFuel graph renderFuel groupFuel fragment right term rightMiddle rightRender, ?_⟩
    apply (success_bind _ _ _ _ _).mpr
    refine ⟨resumed, rightLast, ?_, (success_pure _ result rightLast rightLast).mpr ⟨resultEq, rfl⟩⟩
    have raised := retains_mapM _ _
      (fun group => SourcePruningResume.resume_moreFuel groupFuel renderFuel uv term group) pending
      rightMiddle resumed rightLast rightGroups
    simpa only [Nat.add_comm] using raised
  · simpa only [leftSame] using groupFrame

private theorem pure_agrees {α : Type} (value : α)
    (left right leftAfter rightAfter : State Symbol Guard) (leftResult rightResult : α)
    (frame : Frame left right) (leftRead : Success (pure value) left leftResult leftAfter)
    (rightRead : Success (pure value) right rightResult rightAfter) :
    leftResult = rightResult ∧ Frame leftAfter rightAfter := by
  obtain ⟨leftEq, leftSame⟩ := (success_pure value leftResult left leftAfter).mp leftRead
  obtain ⟨rightEq, rightSame⟩ := (success_pure value rightResult right rightAfter).mp rightRead
  exact ⟨leftEq.trans rightEq.symm, by simpa only [leftSame, rightSame] using frame⟩

private theorem pure_transport {α : Type} (value result : α)
    (left right leftAfter : State Symbol Guard) (frame : Frame left right)
    (leftRead : Success (pure value) left result leftAfter) :
    ∃ _rightFuel : Nat, ∃ rightAfter,
      Success (pure value) right result rightAfter ∧ Frame leftAfter rightAfter := by
  obtain ⟨resultEq, leftSame⟩ := (success_pure value result left leftAfter).mp leftRead
  exact ⟨0, right, (success_pure value result right right).mpr ⟨resultEq, rfl⟩,
    by simpa only [leftSame] using frame⟩

/-- Every actual successful callback preserves the full compression frame. -/
theorem oracle_frame (graph : Graph Symbol Guard) (templates : List (Template.Pattern Symbol))
    (fuel : Nat) (pending : List (Pending Symbol)) (uv : Nat) (input : Sum (Fragment Symbol) Nat)
    (before after : State Symbol Guard) (result : Bool × List (Pending Symbol))
    (total : UnionFind.Total before.representatives)
    (success : Success (oracle graph templates fuel pending uv input) before result after) : Frame before after := by
  cases input with
  | inr node => exact pure_frame _ result before after success
  | inl fragment =>
      by_cases rejected : rejectEarly templates fragment = true
      · simp only [oracle, ite_eq_left rejected] at success
        exact pure_frame _ result before after success
      · by_cases skipped : idle pending fragment = true
        · simp only [oracle, ite_eq_right rejected, ite_eq_left skipped] at success
          exact pure_frame _ result before after success
        · simp only [oracle, ite_eq_right rejected, ite_eq_right skipped] at success
          exact observe_frame graph templates fuel pending uv fragment before after result total success

/-- Independent successful callbacks return equal results and framed final states. -/
theorem oracle_agrees (graph : Graph Symbol Guard) (templates : List (Template.Pattern Symbol))
    (leftFuel rightFuel : Nat) (pending : List (Pending Symbol)) (uv : Nat)
    (input : Sum (Fragment Symbol) Nat) (left right leftAfter rightAfter : State Symbol Guard)
    (leftResult rightResult : Bool × List (Pending Symbol)) (frame : Frame left right)
    (total : UnionFind.Total left.representatives)
    (leftRead : Success (oracle graph templates leftFuel pending uv input) left leftResult leftAfter)
    (rightRead : Success (oracle graph templates rightFuel pending uv input) right rightResult rightAfter) :
    leftResult = rightResult ∧ Frame leftAfter rightAfter := by
  cases input with
  | inr node => exact pure_agrees _ left right leftAfter rightAfter leftResult rightResult frame leftRead rightRead
  | inl fragment =>
      by_cases rejected : rejectEarly templates fragment = true
      · simp only [oracle, ite_eq_left rejected] at leftRead rightRead
        exact pure_agrees _ left right leftAfter rightAfter leftResult rightResult frame leftRead rightRead
      · by_cases skipped : idle pending fragment = true
        · simp only [oracle, ite_eq_right rejected, ite_eq_left skipped] at leftRead rightRead
          exact pure_agrees _ left right leftAfter rightAfter leftResult rightResult frame leftRead rightRead
        · simp only [oracle, ite_eq_right rejected, ite_eq_right skipped] at leftRead rightRead
          exact observe_agrees graph templates leftFuel rightFuel pending uv fragment
            left right leftAfter rightAfter leftResult rightResult frame total leftRead rightRead

/-- Additional fuel retains the callback result and the exact complete final state. -/
theorem oracle_moreFuel (graph : Graph Symbol Guard) (templates : List (Template.Pattern Symbol))
    (fuel extra : Nat) (pending : List (Pending Symbol)) (uv : Nat) (input : Sum (Fragment Symbol) Nat) :
    Retains (oracle graph templates fuel pending uv input)
      (oracle graph templates (fuel + extra) pending uv input) := by
  cases input with
  | inr node => exact retains_refl _
  | inl fragment =>
      by_cases rejected : rejectEarly templates fragment = true
      · simp only [oracle, ite_eq_left rejected]
        exact retains_refl _
      · by_cases skipped : idle pending fragment = true
        · simp only [oracle, ite_eq_right rejected, ite_eq_left skipped]
          exact retains_refl _
        · simp only [oracle, ite_eq_right rejected, ite_eq_right skipped]
          exact observe_moreFuel graph templates fuel extra pending uv fragment

/-- One actual callback gives a finite matching callback from a framed input. -/
theorem oracle_transport (graph : Graph Symbol Guard) (templates : List (Template.Pattern Symbol))
    (leftFuel : Nat) (pending : List (Pending Symbol)) (uv : Nat) (input : Sum (Fragment Symbol) Nat)
    (left right leftAfter : State Symbol Guard) (result : Bool × List (Pending Symbol))
    (frame : Frame left right) (total : UnionFind.Total left.representatives)
    (leftRead : Success (oracle graph templates leftFuel pending uv input) left result leftAfter) :
    ∃ rightFuel rightAfter,
      Success (oracle graph templates rightFuel pending uv input) right result rightAfter ∧
      Frame leftAfter rightAfter := by
  cases input with
  | inr node => exact pure_transport _ result left right leftAfter frame leftRead
  | inl fragment =>
      by_cases rejected : rejectEarly templates fragment = true
      · simp only [oracle, ite_eq_left rejected] at leftRead ⊢
        exact pure_transport _ result left right leftAfter frame leftRead
      · by_cases skipped : idle pending fragment = true
        · simp only [oracle, ite_eq_right rejected, ite_eq_left skipped] at leftRead ⊢
          exact pure_transport _ result left right leftAfter frame leftRead
        · simp only [oracle, ite_eq_right rejected, ite_eq_right skipped] at leftRead ⊢
          exact observe_transport graph templates leftFuel pending uv fragment left right leftAfter result frame total leftRead

/-- Bounded fragment history constructs the actual callback and every pending-group read. -/
theorem oracle_inl_complete (graph : Graph Symbol Guard) (templates : List (Template.Pattern Symbol))
    (level : Nat → Nat) (frontier : Nat) (pending : List (Pending Symbol))
    (uv : Nat) (fragment : Fragment Symbol) (before : State Symbol Guard)
    (safe : Safe before)
    (stratified : EnumerationOrder.Stratified before level frontier)
    (allocated : FragmentBound before.counter fragment)
    (bounded : ∀ group ∈ pending, ∀ entry ∈ group, entry.2 < before.counter) :
    ∃ fuel result after, Success (oracle graph templates fuel pending uv (.inl fragment)) before result after ∧
      EnumerationDriver.RenderStable before after ∧ Frame before after ∧
      EnumerationOrder.Stratified after level frontier := by
  by_cases rejected : rejectEarly templates fragment = true
  · refine ⟨0, (true, pending), before, ?_, .refl before safe, .refl before, stratified⟩
    simp only [oracle, ite_eq_left rejected]
    exact (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩
  · by_cases skipped : idle pending fragment = true
    · refine ⟨0, (false, []), before, ?_, .refl before safe, .refl before, stratified⟩
      simp only [oracle, ite_eq_right rejected, ite_eq_left skipped]
      exact (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩
    · obtain ⟨renderFuel, term, middle, rendered, renderStable, _renderFrame, _renderStratified⟩ :=
        EnumerationPartialCompletion.expandPartial_complete graph level frontier fragment before safe stratified allocated
      have groups : ∀ (pending : List (Pending Symbol)) (previous : State Symbol Guard),
          Safe previous →
          (∀ group ∈ pending, ∀ entry ∈ group, entry.2 < previous.counter) →
          ∃ fuel resumed after,
            Success (pending.mapM (SourcePruningResume.resume fuel uv term)) previous resumed after ∧
            EnumerationDriver.RenderStable previous after := by
        intro pending
        induction pending with
        | nil =>
            intro previous previousSafe _bounded
            exact ⟨0, [], previous, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩, .refl previous previousSafe⟩
        | cons first rest ih =>
            intro previous previousSafe pendingBounded
            obtain ⟨firstFuel, firstResult, reached, firstRead, _firstFrame⟩ :=
              SourcePruningResume.resume_complete uv term first previous previousSafe.1.total
            have firstStable := SourcePruningResume.resume_read firstFuel uv term first previous reached firstResult
              previousSafe (pendingBounded first (by simp)) firstRead
            obtain ⟨restFuel, resumed, after, restRead, restStable⟩ :=
              ih reached firstStable.safe (by
                intro group member entry present
                rw [firstStable.counter]
                exact pendingBounded group (List.mem_cons_of_mem first member) entry present)
            refine ⟨firstFuel + restFuel, firstResult :: resumed, after, ?_, firstStable.trans restStable⟩
            rw [List.mapM_cons]
            apply (success_bind _ _ _ _ _).mpr
            refine ⟨firstResult, reached,
              SourcePruningResume.resume_moreFuel firstFuel restFuel uv term first previous firstResult reached firstRead, ?_⟩
            apply (success_bind _ _ _ _ _).mpr
            refine ⟨resumed, after, ?_, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩
            have raised := retains_mapM _ _
              (fun group => SourcePruningResume.resume_moreFuel restFuel firstFuel uv term group)
              rest reached resumed after restRead
            simpa only [Nat.add_comm] using raised
      obtain ⟨groupFuel, resumed, after, traversed, groupStable⟩ := groups pending middle renderStable.safe (by
        intro group member entry present
        rw [renderStable.counter]
        exact bounded group member entry present)
      let result := finishChecks resumed (startMatches templates term)
      have observed : Success (observe graph templates (renderFuel + groupFuel) pending uv fragment)
          before result after := by
        unfold observe
        apply (success_bind _ _ _ _ _).mpr
        refine ⟨term, middle,
          expandPartial_moreFuel graph renderFuel groupFuel fragment before term middle rendered, ?_⟩
        apply (success_bind _ _ _ _ _).mpr
        refine ⟨resumed, after, ?_, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩
        have raised := retains_mapM _ _
          (fun group => SourcePruningResume.resume_moreFuel groupFuel renderFuel uv term group)
          pending middle resumed after traversed
        simpa only [Nat.add_comm] using raised
      have stable := renderStable.trans groupStable
      refine ⟨renderFuel + groupFuel, result, after, ?_, stable,
        observe_frame graph templates (renderFuel + groupFuel) pending uv fragment before after result safe.1.total observed,
        EnumerationOrder.stratified_read before after level frontier stable stratified⟩
      simpa only [oracle, ite_eq_right rejected, ite_eq_right skipped] using observed

/-- A completed fragment callback returns only allocated pending references. -/
theorem oracle_inl_bounded (graph : Graph Symbol Guard) (templates : List (Template.Pattern Symbol))
    (fuel : Nat) (pending : List (Pending Symbol)) (uv : Nat) (fragment : Fragment Symbol)
    (before after : State Symbol Guard) (result : Bool × List (Pending Symbol))
    (safe : Safe before) (allocated : FragmentBound before.counter fragment)
    (bounded : ∀ group ∈ pending, PendingBound before.counter group)
    (success : Success (oracle graph templates fuel pending uv (.inl fragment)) before result after) :
    ∀ group ∈ result.2, PendingBound after.counter group := by
  by_cases rejected : rejectEarly templates fragment = true
  · simp only [oracle, ite_eq_left rejected] at success
    obtain ⟨rfl, rfl⟩ := (success_pure (true, pending) result before after).mp success
    exact bounded
  · by_cases skipped : idle pending fragment = true
    · simp only [oracle, ite_eq_right rejected, ite_eq_left skipped] at success
      obtain ⟨rfl, rfl⟩ := (success_pure (false, []) result before after).mp success
      simp
    · simp only [oracle, ite_eq_right rejected, ite_eq_right skipped] at success
      unfold observe at success
      obtain ⟨term, middle, rendered, continued⟩ := (success_bind _ _ _ _ _).mp success
      obtain ⟨resumed, last, traversed, final⟩ := (success_bind _ _ _ _ _).mp continued
      obtain ⟨renderStable, termBound⟩ :=
        EnumerationPartialBounds.expandPartial_bounded graph fuel fragment before middle term safe allocated rendered
      have groups : ∀ (pending : List (Pending Symbol)) (before after : State Symbol Guard)
          (results : List (Option (Pending Symbol))), Safe before →
          (∀ group ∈ pending, PendingBound before.counter group) →
          EnumerationPartialBounds.TermBound before.counter term →
          Success (pending.mapM (SourcePruningResume.resume fuel uv term)) before results after →
          EnumerationDriver.RenderStable before after ∧
            ∀ result ∈ results, ∀ group, result = some group → PendingBound after.counter group := by
        intro pending
        induction pending with
        | nil =>
            intro before after results safe _bounded _termBound success
            obtain ⟨rfl, rfl⟩ := (success_pure [] results before after).mp success
            exact ⟨.refl _ safe, by simp⟩
        | cons first rest ih =>
            intro before after results safe bounded termBound success
            rw [List.mapM_cons] at success
            obtain ⟨firstResult, reached, firstRead, continued⟩ := (success_bind _ _ _ _ _).mp success
            obtain ⟨tailResults, last, restRead, final⟩ := (success_bind _ _ _ _ _).mp continued
            obtain ⟨rfl, rfl⟩ := (success_pure (firstResult :: tailResults) results last after).mp final
            have firstStable := SourcePruningResume.resume_read fuel uv term first before reached firstResult
              safe (bounded first (by simp)) firstRead
            have firstBound := SourcePruningResume.resume_bounded fuel uv term first before reached firstResult
              safe (bounded first (by simp)) termBound firstRead
            obtain ⟨lastStable, tailBound⟩ := ih reached after tailResults firstStable.safe
              (by intro group member; rw [firstStable.counter]; exact bounded group (List.mem_cons_of_mem _ member))
              (by simpa only [firstStable.counter] using termBound) restRead
            refine ⟨firstStable.trans lastStable, ?_⟩
            intro result member group same
            rcases List.mem_cons.mp member with rfl | member
            · rw [lastStable.counter]
              exact firstBound group same
            · exact tailBound result member group same
      obtain ⟨groupStable, resultBounds⟩ := groups pending middle last resumed renderStable.safe
        (by intro group member; rw [renderStable.counter]; exact bounded group member) termBound traversed
      obtain ⟨rfl, rfl⟩ := (success_pure (finishChecks resumed (startMatches templates term)) result last after).mp final
      exact finishChecks_bounded after.counter resumed (startMatches templates term)
        (fun group member => resultBounds (some group) member group rfl)
        (startMatches_bounded after.counter templates term (by simpa only [groupStable.counter] using termBound))

end MicroCFTA.SourcePruningOracle
