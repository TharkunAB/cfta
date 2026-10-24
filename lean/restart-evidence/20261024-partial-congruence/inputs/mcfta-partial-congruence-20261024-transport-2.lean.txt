import MicroCFTA.EnumerationPartialObservation

/-!
# Finite transport of an observed partial render

One successful render supplies the stored reads and finite unfolding needed
by the related input. The constructed bound can differ from the original.
-/
namespace MicroCFTA.EnumerationObservations
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule
open EnumerationCompressionFrame EnumerationExecution

local instance partialTransportMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

local instance partialTransportLawfulMonadList : LawfulMonad List where
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

variable {Symbol Guard : Type}

/-- An actual partial render gives a finite matching render from the framed input. -/
theorem expandPartial_transport (graph : Graph Symbol Guard) (leftFuel : Nat)
    (fragment : Fragment Symbol) (left right leftAfter : State Symbol Guard)
    (term : Term (PartialSymbol Symbol)) (frame : Frame left right)
    (total : UnionFind.Total left.representatives)
    (leftRender : Success (expandPartial graph leftFuel fragment) left term leftAfter) :
    ∃ rightFuel rightAfter, Success (expandPartial graph rightFuel fragment) right term rightAfter ∧
      Frame leftAfter rightAfter := by
  induction leftFuel generalizing fragment left right leftAfter term with
  | zero => exact (success_failure .fuelExhausted left leftAfter term leftRender).elim
  | succ fuel ih =>
      cases fragment with
      | node symbol children =>
          have traversal : ∀ children : List (Fragment Symbol),
              ∀ (left right leftAfter : State Symbol Guard) (terms : List (Term (PartialSymbol Symbol))),
              Frame left right → UnionFind.Total left.representatives →
              Success (children.mapM (expandPartial graph fuel)) left terms leftAfter →
              ∃ rightFuel rightAfter,
                Success (children.mapM (expandPartial graph rightFuel)) right terms rightAfter ∧
                Frame leftAfter rightAfter := by
            intro children
            induction children with
            | nil =>
                intro left right leftAfter terms frame total success
                obtain ⟨rfl, rfl⟩ := (success_pure [] terms left leftAfter).mp success
                exact ⟨0, right, (success_pure [] [] right right).mpr ⟨rfl, rfl⟩, frame⟩
            | cons first rest restIH =>
                intro left right leftAfter terms frame total success
                rw [List.mapM_cons] at success
                obtain ⟨term, leftMiddle, firstDone, continued⟩ := (success_bind _ _ _ _ _).mp success
                obtain ⟨tail, leftLast, restDone, final⟩ := (success_bind _ _ _ _ _).mp continued
                obtain ⟨rfl, rfl⟩ := (success_pure (term :: tail) terms leftLast leftAfter).mp final
                obtain ⟨firstFuel, rightMiddle, rightFirst, firstFrame⟩ :=
                  ih first left right leftMiddle term frame total firstDone
                have middleTotal : UnionFind.Total leftMiddle.representatives :=
                  (expandPartial_frame graph fuel first left leftMiddle term total firstDone).total total
                obtain ⟨restFuel, rightLast, rightRest, restFrame⟩ :=
                  restIH leftMiddle rightMiddle leftAfter tail firstFrame middleTotal restDone
                refine ⟨firstFuel + restFuel, rightLast, ?_, restFrame⟩
                rw [List.mapM_cons]
                apply (success_bind _ _ _ _ _).mpr
                refine ⟨term, rightMiddle, ?_, ?_⟩
                · exact expandPartial_moreFuel graph firstFuel restFuel first right term rightMiddle rightFirst
                · apply (success_bind _ _ _ _ _).mpr
                  refine ⟨tail, rightLast, ?_, (success_pure (term :: tail) (term :: tail) rightLast rightLast).mpr ⟨rfl, rfl⟩⟩
                  have raised := retains_mapM _ _ (fun child => expandPartial_moreFuel graph restFuel firstFuel child)
                    rest rightMiddle tail rightLast rightRest
                  simpa only [Nat.add_comm] using raised
          change Success (children.mapM (expandPartial graph fuel) >>= fun terms =>
            pure (.node (.concrete symbol) terms)) left term leftAfter at leftRender
          obtain ⟨terms, leftMiddle, traversed, final⟩ := (success_bind _ _ _ _ _).mp leftRender
          obtain ⟨rfl, rfl⟩ := (success_pure (.node (.concrete symbol) terms) term leftMiddle leftAfter).mp final
          obtain ⟨rightFuel, rightAfter, rightTraversal, finalFrame⟩ :=
            traversal children left right leftAfter terms frame total traversed
          refine ⟨rightFuel + 1, rightAfter, ?_, finalFrame⟩
          change Success (children.mapM (expandPartial graph rightFuel) >>= fun terms =>
            pure (.node (.concrete symbol) terms)) right (.node (.concrete symbol) terms) rightAfter
          exact (success_bind _ _ _ _ _).mpr
            ⟨terms, rightAfter, rightTraversal, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩
      | hole uv =>
          change Success (getValue (fuel + 1) uv >>= fun value => match value with
            | .enumerated stored => expandPartial graph fuel stored
            | .unenumerated (some node) [] => match graph.node node with
              | .recursive _ => pure (.node .truncated [])
              | _ => pure (.node (.hole uv) [])
            | _ => pure (.node (.hole uv) [])) left term leftAfter at leftRender
          obtain ⟨value, leftMiddle, leftRead, continued⟩ := (success_bind _ _ _ _ _).mp leftRender
          obtain ⟨readFuel, rightMiddle, rightRead, readFrame⟩ :=
            getValue_transport (fuel + 1) uv left right leftMiddle value frame total leftRead
          have middleTotal : UnionFind.Total leftMiddle.representatives :=
            (getValue_frame (fuel + 1) uv left leftMiddle value total leftRead).1.total total
          have readingMore (extra : Nat) :
              Success (getValue (readFuel + extra) uv) right value rightMiddle :=
            getValue_moreFuel readFuel extra uv right value rightMiddle rightRead
          cases value with
          | enumerated stored =>
              obtain ⟨tailFuel, rightAfter, tailRender, finalFrame⟩ :=
                ih stored leftMiddle rightMiddle leftAfter term readFrame middleTotal continued
              refine ⟨readFuel + tailFuel + 1, rightAfter, ?_, finalFrame⟩
              simp only [expandPartial]
              apply (success_bind _ _ _ _ _).mpr
              refine ⟨.enumerated stored, rightMiddle, ?_, ?_⟩
              · simpa only [Nat.add_assoc] using readingMore (tailFuel + 1)
              · simpa only [Nat.add_comm] using expandPartial_moreFuel graph tailFuel readFuel stored rightMiddle term rightAfter tailRender
          | eliminated =>
              obtain ⟨rfl, rfl⟩ := (success_pure _ term leftMiddle leftAfter).mp continued
              refine ⟨readFuel + 1, rightMiddle, ?_, readFrame⟩
              simp only [expandPartial]
              exact (success_bind _ _ _ _ _).mpr
                ⟨.eliminated, rightMiddle, readingMore 1, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩
          | unenumerated node scs =>
              cases node with
              | none =>
                  obtain ⟨rfl, rfl⟩ := (success_pure _ term leftMiddle leftAfter).mp continued
                  refine ⟨readFuel + 1, rightMiddle, ?_, readFrame⟩
                  simp only [expandPartial]
                  exact (success_bind _ _ _ _ _).mpr
                    ⟨.unenumerated none scs, rightMiddle, readingMore 1, (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩
              | some node =>
                  cases scs with
                  | cons first rest =>
                      obtain ⟨rfl, rfl⟩ := (success_pure _ term leftMiddle leftAfter).mp continued
                      refine ⟨readFuel + 1, rightMiddle, ?_, readFrame⟩
                      simp only [expandPartial]
                      exact (success_bind _ _ _ _ _).mpr
                        ⟨.unenumerated (some node) (first :: rest), rightMiddle, readingMore 1,
                          (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩⟩
                  | nil =>
                      cases view : graph.node node <;> simp only [view] at continued
                      all_goals
                        obtain ⟨rfl, rfl⟩ := (success_pure _ term leftMiddle leftAfter).mp continued
                        refine ⟨readFuel + 1, rightMiddle, ?_, readFrame⟩
                        simp only [expandPartial]
                        apply (success_bind _ _ _ _ _).mpr
                        refine ⟨.unenumerated (some node) [], rightMiddle, readingMore 1, ?_⟩
                        simp only [view]
                        exact (success_pure _ _ _ _).mpr ⟨rfl, rfl⟩

end MicroCFTA.EnumerationObservations
