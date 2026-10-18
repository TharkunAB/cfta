import MicroCFTA.SourceCurrentParentUniformGuardAlphabet
import MicroCFTA.SourceCurrentParentInitialRoom
import MicroCFTA.SourceCurrentOuterConstructorBounds

/-!
# Initial physical and guard schedules for the outer phases

Each phase uses the predicted output of its preceding phase. A skipped
branch can retain its entry bounds. The schedule depends only on outer
fuel, the local query budget, the initial alphabet and the initial profile.
No future entry or completed call is a schedule input.
-/
namespace MicroCFTA.SourceCurrentOuterInitialSchedule
open SourceCurrentAllocatedNativeResourceForecast (Profile Le Room)
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- One Parent uses the common finite initial guard and numeric image. -/
noncomputable def parent (budget : Nat) (seed : List Guard × Profile) : List Guard × Profile :=
  (SourceCurrentParentUniformGuardAlphabet.forecast budget seed.1 seed.2,
    SourceCurrentParentUniformEnvelope.profile budget seed.1 seed.2)

/-- One raw constructor retains its alphabet and reserves its original width. -/
def rebuild (seed : List Guard × Profile) : List Guard × Profile :=
  (seed.1, SourceCurrentOuterConstructorBounds.profile seed.2)

/-- The Parent image retains both initial bounds. -/
theorem parent_ge (budget : Nat) (seed : List Guard × Profile) :
    Le seed.2 (parent budget seed).2 ∧ seed.1 ⊆ (parent budget seed).1 := by
  refine ⟨?_, fun _ member => SourceCurrentParentUniformGuardAlphabet.initial_mem budget seed.1 seed.2 member⟩
  exact (SourceCurrentInitialSelectionForecast.cover_ge _ seed.2).trans
    (SourceCurrentMkEdgeNumeric.finalProfile_ge seed.2.mass
      (SourceCurrentParentUniformEnvelope.classesProfile budget seed.1 seed.2))

/-- A raw constructor retains both initial bounds. -/
theorem rebuild_ge (seed : List Guard × Profile) :
    Le seed.2 (rebuild seed).2 ∧ seed.1 ⊆ (rebuild seed).1 :=
  ⟨SourceCurrentOuterConstructorBounds.profile_ge seed.2, fun _ member => member⟩

mutual
/-- Node demand reserves its possible body; a warm hit can retain entry bounds. -/
noncomputable def node (fuel budget : Nat) (seed : List Guard × Profile) : List Guard × Profile :=
  body fuel budget seed
termination_by (fuel, 3)

/-- An ordinary body reserves its row pass and one raw node constructor. -/
noncomputable def body (fuel budget : Nat) (seed : List Guard × Profile) : List Guard × Profile :=
  match fuel with
  | 0 => seed
  | next + 1 => rebuild (rows next budget seed)
termination_by (fuel, 2)

/-- Rows reserve the head Parent, its descendants and then the original suffix. -/
noncomputable def rows (fuel budget : Nat) (seed : List Guard × Profile) : List Guard × Profile :=
  match fuel with
  | 0 => seed
  | next + 1 => rows next budget (descendants next budget (parent budget seed))
termination_by (fuel, 2)

/-- Descendants reserve the child pass and one raw edge constructor. -/
noncomputable def descendants (fuel budget : Nat) (seed : List Guard × Profile) : List Guard × Profile :=
  rebuild (children fuel budget seed)
termination_by (fuel, 2)

/-- The child schedule includes the live walk; contradiction can retain entry bounds. -/
noncomputable def children (fuel budget : Nat) (seed : List Guard × Profile) : List Guard × Profile :=
  walk fuel budget seed
termination_by (fuel, 1)

/-- A walk reserves the selected node and then the original suffix at its returned bounds. -/
noncomputable def walk (fuel budget : Nat) (seed : List Guard × Profile) : List Guard × Profile :=
  match fuel with
  | 0 => seed
  | next + 1 => walk next budget (node next budget seed)
termination_by (fuel, 0)
end

private def Retains (first last : List Guard × Profile) : Prop :=
  Le first.2 last.2 ∧ first.1 ⊆ last.1

private theorem refl (seed : List Guard × Profile) : Retains seed seed :=
  ⟨Le.refl _, fun _ member => member⟩

private theorem trans {first middle last : List Guard × Profile}
    (one : Retains first middle) (two : Retains middle last) : Retains first last :=
  ⟨one.1.trans two.1, fun _ member => two.2 (one.2 member)⟩

private theorem all_ge (fuel budget : Nat) :
    (∀ seed, Retains seed (node fuel budget seed)) ∧
    (∀ seed, Retains seed (body fuel budget seed)) ∧
    (∀ seed, Retains seed (rows fuel budget seed)) ∧
    (∀ seed, Retains seed (descendants fuel budget seed)) ∧
    (∀ seed, Retains seed (children fuel budget seed)) ∧
    (∀ seed, Retains seed (walk fuel budget seed)) := by
  induction fuel with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [node, body] using refl
      · simpa only [body] using refl
      · simpa only [rows] using refl
      · simpa only [descendants, children, walk] using rebuild_ge
      · simpa only [children, walk] using refl
      · simpa only [walk] using refl
  | succ fuel ih =>
      have walkKeeps : ∀ seed, Retains seed (walk (fuel+1) budget seed) := by
        intro seed
        simpa only [walk] using trans (ih.1 seed) (ih.2.2.2.2.2 (node fuel budget seed))
      have childKeeps : ∀ seed, Retains seed (children (fuel+1) budget seed) := by
        simpa only [children] using walkKeeps
      have descKeeps : ∀ seed, Retains seed (descendants (fuel+1) budget seed) := by
        intro seed
        simpa only [descendants] using trans (childKeeps seed) (rebuild_ge _)
      have rowKeeps : ∀ seed, Retains seed (rows (fuel+1) budget seed) := by
        intro seed
        simpa only [rows] using trans (parent_ge budget seed)
          (trans (ih.2.2.2.1 (parent budget seed))
            (ih.2.2.1 (descendants fuel budget (parent budget seed))))
      have bodyKeeps : ∀ seed, Retains seed (body (fuel+1) budget seed) := by
        intro seed
        simpa only [body] using trans (ih.2.2.1 seed) (rebuild_ge _)
      exact ⟨by simpa only [node] using bodyKeeps, bodyKeeps, rowKeeps, descKeeps, childKeeps, walkKeeps⟩

/-- Node demand retains the entry profile and every initial raw guard. -/
theorem node_ge (fuel budget : Nat) (seed : List Guard × Profile) :
    Le seed.2 (node fuel budget seed).2 ∧ seed.1 ⊆ (node fuel budget seed).1 := (all_ge fuel budget).1 seed

/-- Each body forecast retains the entry profile and every initial raw guard. -/
theorem body_ge (fuel budget : Nat) (seed : List Guard × Profile) :
    Le seed.2 (body fuel budget seed).2 ∧ seed.1 ⊆ (body fuel budget seed).1 := (all_ge fuel budget).2.1 seed

/-- Each row forecast retains the entry profile and every initial raw guard. -/
theorem rows_ge (fuel budget : Nat) (seed : List Guard × Profile) :
    Le seed.2 (rows fuel budget seed).2 ∧ seed.1 ⊆ (rows fuel budget seed).1 := (all_ge fuel budget).2.2.1 seed

/-- Each descendants forecast retains the entry profile and every initial raw guard. -/
theorem descendants_ge (fuel budget : Nat) (seed : List Guard × Profile) :
    Le seed.2 (descendants fuel budget seed).2 ∧ seed.1 ⊆ (descendants fuel budget seed).1 := (all_ge fuel budget).2.2.2.1 seed

/-- Each child forecast retains the entry profile and every initial raw guard. -/
theorem children_ge (fuel budget : Nat) (seed : List Guard × Profile) :
    Le seed.2 (children fuel budget seed).2 ∧ seed.1 ⊆ (children fuel budget seed).1 := (all_ge fuel budget).2.2.2.2.1 seed

/-- Each walk forecast retains the entry profile and every initial raw guard. -/
theorem walk_ge (fuel budget : Nat) (seed : List Guard × Profile) :
    Le seed.2 (walk fuel budget seed).2 ∧ seed.1 ⊆ (walk fuel budget seed).1 := (all_ge fuel budget).2.2.2.2.2 seed

/-- Room at one predicted Parent return supplies every initial Parent query reservation. -/
theorem parent_reserved (bits budget : Nat) (seed : List Guard × Profile)
    (room : Room bits (parent budget seed).2) :
    SourceCurrentParentAlphabetReservation.UniformReserved bits budget seed.1 seed.2 :=
  SourceCurrentParentInitialRoom.uniform_of_room bits budget seed.1 seed.2
    (room.mono (SourceCurrentMkEdgeNumeric.finalProfile_ge seed.2.mass _))

end MicroCFTA.SourceCurrentOuterInitialSchedule
