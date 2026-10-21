import MicroCFTA.SourceCurrentOuterInitialSchedule
import Init.Data.List.Attach
import Init.Data.List.Lemmas
import Init.Data.List.Range
import Init.WF

/-!
# A finite numeric envelope over strict count and mass ranks

Each recursive candidate has a smaller rank. Its seed is the current
numeric accumulator. This module proves only entry retention and a
positive work bound. It does not prove stage coverage or completion.
-/
namespace MicroCFTA.SourceCurrentOuterRankEnvelope
open SourceCurrentAllocatedNativeResourceForecast (Profile Le)
open SourceCurrentInitialSelectionForecast (cover cover_ge maximum)
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Seed" => List Guard × Profile
local notation "Out" => Nat × Nat × Seed

private def candidates (rank : Nat × Nat) (seed : Seed) : List (Nat × Nat) :=
  ((List.range (rank.1 + 1)).flatMap fun a =>
    (List.range (seed.2.mass + 1)).map fun b => (a,b)).filter
      (fun child => decide (child.1 < rank.1 ∨ (child.1 = rank.1 ∧ child.2 < rank.2)))

private theorem candidates_lt (rank : Nat × Nat) (seed : Seed) (child : Nat × Nat)
    (member : child ∈ candidates rank seed) : Prod.Lex Nat.lt Nat.lt child rank := by
  simp only [candidates, List.mem_filter, decide_eq_true_eq] at member
  exact Prod.lex_def.mpr member.2

private def images (rank : Nat × Nat)
    (recurse : ∀ child, Prod.Lex Nat.lt Nat.lt child rank → Seed → Out)
    (seed : Seed) : List Out :=
  (candidates rank seed).attach.map fun child =>
    recurse child.val (candidates_lt rank seed child.val child.property) seed

private def joinSeed (seed : Seed) (outputs : List Out) : Seed :=
  (seed.1 ++ outputs.flatMap (fun output => output.2.2.1),
    cover (outputs.map fun output => output.2.2.2) seed.2)

private def slot (all : Seed → List Out) (acc : Out) (_index : Nat) : Out :=
  let outputs := all acc.2.2
  (acc.1 + 1 + maximum (outputs.map fun output => output.1),
    max acc.2.1 (maximum (outputs.map fun output => output.2.1)),
    joinSeed acc.2.2 outputs)

private noncomputable def row (budget : Nat) (all : Seed → List Out)
    (acc : Out) (_index : Nat) : Out :=
  let post := SourceCurrentOuterInitialSchedule.parent budget acc.2.2
  let walked := (List.range post.2.mass).foldl (slot all) (0,0,post)
  (acc.1 + 1 + walked.1,
    max acc.2.1 (max (SourceCurrentParentUniformEnvelope.fuel budget acc.2.2.1 acc.2.2.2) walked.2.1),
    SourceCurrentOuterInitialSchedule.rebuild walked.2.2)

private noncomputable def recipe (budget : Nat) (rank : Nat × Nat)
    (recurse : ∀ child, Prod.Lex Nat.lt Nat.lt child rank → Seed → Out)
    (seed : Seed) : Out :=
  let completed := (List.range rank.2).foldl (row budget (images rank recurse)) (0,0,seed)
  (1 + completed.1, completed.2.1, SourceCurrentOuterInitialSchedule.rebuild completed.2.2)

/-- Compute finite work, lower fuel, and an output seed from the initial rank and seed. -/
noncomputable def envelope (budget count mass : Nat)
    (seed : List Guard × Profile) : Nat × Nat × (List Guard × Profile) :=
  WellFounded.fix (C := fun _ : Nat × Nat => Seed → Out)
    (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf (recipe budget) (count,mass) seed

private theorem envelope_eq (budget count mass : Nat) (seed : Seed) :
    envelope budget count mass seed = recipe budget (count,mass)
      (fun child _ current => envelope budget child.1 child.2 current) seed := by
  unfold envelope
  rw [WellFounded.fix_eq]
  apply congrArg (fun recurse => recipe budget (count,mass) recurse seed)
  funext child smaller current
  cases child
  rfl

private theorem fold_retains (step : Out → Nat → Out)
    (growth : ∀ acc index, Le acc.2.2.2 (step acc index).2.2.2 ∧
      acc.2.2.1 ⊆ (step acc index).2.2.1)
    (values : List Nat) (initial : Out) :
    Le initial.2.2.2 (values.foldl step initial).2.2.2 ∧
      initial.2.2.1 ⊆ (values.foldl step initial).2.2.1 := by
  induction values generalizing initial with
  | nil => exact ⟨Le.refl _, fun _ member => member⟩
  | cons first rest ih =>
      have one := growth initial first
      have last := ih (step initial first)
      exact ⟨one.1.trans last.1, fun _ member => last.2 (one.2 member)⟩

private theorem fold_work (step : Out → Nat → Out)
    (growth : ∀ acc index, acc.1 + 1 ≤ (step acc index).1)
    (values : List Nat) (initial : Out) :
    initial.1 + values.length ≤ (values.foldl step initial).1 := by
  induction values generalizing initial with
  | nil => simp only [List.length_nil, List.foldl_nil, Nat.add_zero, Nat.le_refl]
  | cons first rest ih =>
      have one := growth initial first
      have last := ih (step initial first)
      simp only [List.length_cons, List.foldl_cons]
      omega

private theorem slot_retains (all : Seed → List Out) (acc : Out) (index : Nat) :
    Le acc.2.2.2 (slot all acc index).2.2.2 ∧ acc.2.2.1 ⊆ (slot all acc index).2.2.1 := by
  dsimp only [slot, joinSeed]
  exact ⟨cover_ge _ _, fun _ member => List.mem_append_left _ member⟩

private theorem row_retains (budget : Nat) (all : Seed → List Out) (acc : Out) (index : Nat) :
    Le acc.2.2.2 (row budget all acc index).2.2.2 ∧
      acc.2.2.1 ⊆ (row budget all acc index).2.2.1 := by
  let post := SourceCurrentOuterInitialSchedule.parent budget acc.2.2
  let walked := (List.range post.2.mass).foldl (slot all) (0,0,post)
  have one : Le acc.2.2.2 post.2 ∧ acc.2.2.1 ⊆ post.1 :=
    SourceCurrentOuterInitialSchedule.parent_ge budget acc.2.2
  have middle : Le post.2 walked.2.2.2 ∧ post.1 ⊆ walked.2.2.1 :=
    fold_retains (slot all) (slot_retains all) (List.range post.2.mass) (0,0,post)
  have last := SourceCurrentOuterInitialSchedule.rebuild_ge walked.2.2
  dsimp only [row]
  change Le acc.2.2.2 (SourceCurrentOuterInitialSchedule.rebuild walked.2.2).2 ∧
    acc.2.2.1 ⊆ (SourceCurrentOuterInitialSchedule.rebuild walked.2.2).1
  refine ⟨one.1.trans (middle.1.trans last.1), ?_⟩
  change acc.2.2.1 ⊆ walked.2.2.1
  intro guard member
  have present : guard ∈ post.1 := one.2 member
  exact middle.2 present

private theorem row_work (budget : Nat) (all : Seed → List Out) (acc : Out) (index : Nat) :
    acc.1 + 1 ≤ (row budget all acc index).1 := by
  dsimp only [row]
  exact Nat.le_add_right _ _

private theorem recipe_retains (budget : Nat) (rank : Nat × Nat)
    (recurse : ∀ child, Prod.Lex Nat.lt Nat.lt child rank → Seed → Out)
    (seed : Seed) :
    rank.2 + 1 ≤ (recipe budget rank recurse seed).1 ∧
      Le seed.2 (recipe budget rank recurse seed).2.2.2 ∧
      seed.1 ⊆ (recipe budget rank recurse seed).2.2.1 := by
  let all := images rank recurse
  let completed := (List.range rank.2).foldl (row budget all) (0,0,seed)
  have kept := fold_retains (row budget all) (row_retains budget all) (List.range rank.2) (0,0,seed)
  have work := fold_work (row budget all) (row_work budget all) (List.range rank.2) (0,0,seed)
  have last := SourceCurrentOuterInitialSchedule.rebuild_ge completed.2.2
  have countBound : rank.2 ≤ completed.1 := by
    simpa only [List.length_range, Nat.zero_add] using work
  change rank.2 + 1 ≤ 1 + completed.1 ∧
    Le seed.2 (SourceCurrentOuterInitialSchedule.rebuild completed.2.2).2 ∧ seed.1 ⊆ (SourceCurrentOuterInitialSchedule.rebuild completed.2.2).1
  exact ⟨by omega, kept.1.trans last.1, fun _ member => last.2 (kept.2 member)⟩

/-- The envelope has positive work and retains its complete entry profile and alphabet. -/
theorem retains (budget count mass : Nat) (seed : List Guard × Profile) :
    mass + 1 ≤ (envelope budget count mass seed).1 ∧
    Le seed.2 (envelope budget count mass seed).2.2.2 ∧
    seed.1 ⊆ (envelope budget count mass seed).2.2.1 := by
  rw [envelope_eq]
  exact recipe_retains budget (count,mass)
    (fun child _ current => envelope budget child.1 child.2 current) seed

end MicroCFTA.SourceCurrentOuterRankEnvelope
