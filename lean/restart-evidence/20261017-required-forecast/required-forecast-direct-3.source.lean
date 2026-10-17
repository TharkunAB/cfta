import MicroCFTA.SourceCurrentConstrainedCapEditForecast
import MicroCFTA.SourceCurrentOpenRowReadResources

/-!
# Initial finite Required resource forecasts

A stage covers Head exposure and a constructor of initially bounded width.
Each successor fixes its original row and child widths before either scan.
The numeric level is independent of any future graph or successful worker.
The Head profile uses the supported open reader envelope. These pure bounds
make no Required completion or actual Head resource claim.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapRequiredForecast
open SourceCurrentAllocatedNativeResourceForecast (Profile Le)
open SourceCurrentConstrainedCapEditForecast
  (join join_left join_right join_mono scalar_mono)
export SourceCurrentConstrainedCapEditForecast
  (scalar scan scan_zero scan_succ scan_ge scan_mono scan_add scan_count_mono
    scan_compare scan_joint scan_child scan_prefix)
export SourceCurrentConstrainedCapEditForecast (constructorProfile)

/-- The supported open Head forecast bounds the heap and keeps the domain supply. -/
def headProfile (profile : Profile) : Profile :=
  let bound := SourceCurrentOpenRowReadResources.headGrowth (scalar profile)
  ⟨bound, bound, profile.domains, bound⟩

/-- Supported open Head exposure retains every initial profile component. -/
theorem headProfile_ge (profile : Profile) : Le profile (headProfile profile) := by
  have enough := SourceCurrentOpenRowReadResources.headGrowth_ge (scalar profile)
  exact ⟨Nat.le_trans (SourceCurrentConstrainedCapTargetForecast.scalar_nodes profile) enough,
    Nat.le_trans (SourceCurrentConstrainedCapTargetForecast.scalar_edges profile) enough, Nat.le_refl _,
    Nat.le_trans (SourceCurrentConstrainedCapTargetForecast.scalar_mass profile) enough⟩

/-- Larger initial profiles retain the supported open Head return forecast. -/
theorem headProfile_mono {first last : Profile} (increase : Le first last) :
    Le (headProfile first) (headProfile last) := by
  have bounds := SourceCurrentOpenRowReadResources.headGrowth_mono (scalar_mono increase)
  exact ⟨bounds, bounds, increase.2.2.1, bounds⟩

/-- One stage includes the possible Head and one full constructor request. -/
def stageProfile (profile : Profile) : Profile :=
  join (headProfile profile) (constructorProfile (scalar profile) profile)

/-- Every stage retains all initial components. -/
theorem stage_ge (profile : Profile) : Le profile (stageProfile profile) :=
  (headProfile_ge profile).trans (join_left _ _)

/-- Larger initial components retain the complete stage. -/
theorem stage_mono {first last : Profile} (increase : Le first last) :
    Le (stageProfile first) (stageProfile last) :=
  join_mono (headProfile_mono increase)
    (SourceCurrentConstrainedCapEditForecast.constructorProfile_mono (scalar_mono increase) increase)

/-- Head exposure fits the stage at the same initial profile. -/
theorem stage_head_profile (profile : Profile) : Le (headProfile profile) (stageProfile profile) := join_left _ _

/-- Any original constructor list within the initial scalar fits the stage. -/
theorem stage_constructor_profile (profile : Profile) {length : Nat} (width : length ≤ scalar profile) :
    Le (constructorProfile length profile) (stageProfile profile) :=
  (SourceCurrentConstrainedCapEditForecast.constructorProfile_mono width (Le.refl profile)).trans (join_right _ _)

/-- Reserve one stage around fixed row and child scans at each finite syntax level. -/
def planProfile : Nat → Profile → Profile
  | 0, profile => stageProfile profile
  | level + 1, profile =>
      let start := stageProfile profile
      let width := scalar start
      let row := fun current => stageProfile (scan (planProfile level) width current)
      stageProfile (scan row width start)

/-- One original row scans its fixed child limit before the edge stage. -/
def rowStep (level width : Nat) (profile : Profile) : Profile :=
  stageProfile (scan (planProfile level) width profile)

/-- The base reserves its own actual stage. -/
theorem plan_zero (profile : Profile) :
    planProfile 0 profile = stageProfile profile := rfl

/-- A successor fixes its row and child widths before either scan. -/
theorem plan_succ (level : Nat) (profile : Profile) :
    planProfile (level + 1) profile =
      stageProfile (scan (rowStep level (scalar (stageProfile profile)))
        (scalar (stageProfile profile)) (stageProfile profile)) := rfl

/-- Every finite plan retains its original entry. -/
theorem plan_ge (level : Nat) (profile : Profile) :
    Le profile (planProfile level profile) := by
  induction level generalizing profile with
  | zero => exact stage_ge profile
  | succ level ih =>
      let start := stageProfile profile
      let width := scalar start
      have rowGrows : ∀ current, Le current (rowStep level width current) :=
        fun current => (scan_ge _ ih width current).trans (stage_ge _)
      exact (stage_ge profile).trans
        ((scan_ge _ rowGrows width start).trans (stage_ge _))

/-- One row retains its original entry. -/
theorem rowStep_ge (level width : Nat) (profile : Profile) :
    Le profile (rowStep level width profile) :=
  (scan_ge _ (plan_ge level) width profile).trans (stage_ge _)

/-- Larger initial component bounds retain the complete finite plan. -/
theorem plan_mono (level : Nat)
    {first last : Profile} (increase : Le first last) :
    Le (planProfile level first) (planProfile level last) := by
  induction level generalizing first last with
  | zero => exact stage_mono increase
  | succ level ih =>
      have start := stage_mono increase
      have widths := scalar_mono start
      have rowMono : ∀ width, ∀ {first last}, Le first last →
          Le (rowStep level width first) (rowStep level width last) :=
        fun width _ _ enough => stage_mono (scan_mono _ ih width enough)
      have rowCompare : ∀ current,
          Le (rowStep level (scalar (stageProfile first)) current)
            (rowStep level (scalar (stageProfile last)) current) :=
        fun current => stage_mono (scan_count_mono _ (plan_ge level) widths current)
      exact stage_mono
        (scan_joint _ _ (rowStep_ge level _) (rowMono _) rowCompare widths start)

/-- Larger child limits and row entries retain the complete row forecast. -/
theorem rowStep_mono (level : Nat)
    {firstWidth lastWidth : Nat} (widths : firstWidth ≤ lastWidth)
    {first last : Profile} (increase : Le first last) :
    Le (rowStep level firstWidth first) (rowStep level lastWidth last) :=
  stage_mono
    (scan_joint _ _ (plan_ge level) (plan_mono level) (fun _ => Le.refl _) widths increase)

/-- A plan contains the initial head and constructor stage. -/
theorem plan_stage (level : Nat) (profile : Profile) :
    Le (stageProfile profile) (planProfile level profile) := by
  cases level with
  | zero => exact Le.refl _
  | succ level =>
      exact (scan_ge _ (rowStep_ge level _) _ _).trans (stage_ge _)

/-- The last scan step acts at the exact preceding forecast. -/
theorem scan_succ_right (next : Profile → Profile) (count : Nat) (profile : Profile) :
    scan next (count + 1) profile = next (scan next count profile) := by
  exact scan_add next count 1 profile

/-- Any scheduled row entry fits the complete plan. -/
theorem plan_row_entry (level : Nat) (profile : Profile)
    {index : Nat} (inside : index ≤ scalar (stageProfile profile)) :
    Le (scan (rowStep level (scalar (stageProfile profile))) index
      (stageProfile profile)) (planProfile (level + 1) profile) :=
  (scan_count_mono _ (rowStep_ge level _) inside _).trans (stage_ge _)

/-- Any scheduled row return fits the complete plan. -/
theorem plan_row_return (level : Nat) (profile : Profile)
    {index : Nat} (inside : index < scalar (stageProfile profile)) :
    Le (rowStep level (scalar (stageProfile profile))
      (scan (rowStep level (scalar (stageProfile profile))) index
        (stageProfile profile))) (planProfile (level + 1) profile) := by
  have enough := plan_row_entry level profile (show index + 1 ≤ scalar (stageProfile profile) by omega)
  rw [scan_succ_right] at enough
  exact enough

/-- Every scheduled child entry fits its row return and complete plan. -/
theorem plan_child_entry (level : Nat) (profile : Profile)
    {row child : Nat} (rowInside : row < scalar (stageProfile profile))
    (childInside : child ≤ scalar (stageProfile profile)) :
    Le (scan (planProfile level) child
      (scan (rowStep level (scalar (stageProfile profile))) row
        (stageProfile profile))) (planProfile (level + 1) profile) :=
  (scan_count_mono _ (plan_ge level) childInside _).trans
    ((stage_ge _).trans (plan_row_return level profile rowInside))

/-- A selected child's complete forecast fits its enclosing row and complete plan. -/
theorem plan_child_return (level : Nat) (profile : Profile)
    {row child : Nat} (rowInside : row < scalar (stageProfile profile))
    (childInside : child < scalar (stageProfile profile)) :
    Le (planProfile level (scan (planProfile level) child
      (scan (rowStep level (scalar (stageProfile profile))) row
        (stageProfile profile)))) (planProfile (level + 1) profile) := by
  have enough := plan_child_entry level profile rowInside
    (show child + 1 ≤ scalar (stageProfile profile) by omega)
  rw [scan_succ_right] at enough
  exact enough


/-- A larger finite syntax level retains the preceding complete plan. -/
theorem plan_level_succ (level : Nat) (profile : Profile) :
    Le (planProfile level profile) (planProfile (level + 1) profile) := by
  induction level generalizing profile with
  | zero => exact plan_stage 1 profile
  | succ level ih =>
      let start := stageProfile profile
      let width := scalar start
      have rows : ∀ current, Le (rowStep level width current) (rowStep (level + 1) width current) :=
        fun current => stage_mono (scan_compare _ _ (plan_mono (level + 1)) ih width (Le.refl current))
      exact stage_mono (scan_compare _ _ (rowStep_mono (level + 1) (Nat.le_refl width)) rows width (Le.refl start))

/-- A larger initial syntax-level bound retains the complete plan. -/
theorem plan_level_mono {first last : Nat} (levels : first ≤ last) (profile : Profile) :
    Le (planProfile first profile) (planProfile last profile) := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le levels
  clear levels
  induction extra with
  | zero => exact Le.refl _
  | succ extra ih =>
      exact ih.trans (plan_level_succ (first + extra) profile)

end MicroCFTA.SourceCurrentConstrainedCapRequiredForecast
