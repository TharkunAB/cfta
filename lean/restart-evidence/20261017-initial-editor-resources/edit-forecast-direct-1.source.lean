import MicroCFTA.SourceCurrentConstrainedCapSharedMonotone
import MicroCFTA.SourceCurrentProjectionUnionResources

/-!
# Initial numeric envelopes for arbitrary supported mixed edits

Each stage covers a head, one constructor, and every original leaf token.
The finite level controls child recursion. Row and child scans use widths
fixed before those scans. These pure bounds do not assert Edit completion.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapEditForecast
open SourceCurrentAllocatedNativeResourceForecast (Profile Le Room)
namespace Shared
export SourceCurrentConstrainedCapSharedForecast (leafProfile leafFuel LeafReserved forceProfile)
end Shared
local notation "operands" => SourceEqualityClassTarget.operandPaths
local notation "inflate" => InternedFreshOrdinaryResultMass.inflate

/-- Join all four numeric component bounds. -/
def join (first last : Profile) : Profile :=
  ⟨max first.nodes last.nodes, max first.edges last.edges,
    max first.domains last.domains, max first.mass last.mass⟩

/-- The first profile is contained in its join. -/
theorem join_left (first last : Profile) : Le first (join first last) :=
  ⟨Nat.le_max_left _ _, Nat.le_max_left _ _, Nat.le_max_left _ _, Nat.le_max_left _ _⟩

/-- The last profile is contained in its join. -/
theorem join_right (first last : Profile) : Le last (join first last) :=
  ⟨Nat.le_max_right _ _, Nat.le_max_right _ _, Nat.le_max_right _ _, Nat.le_max_right _ _⟩

/-- A common component bound contains the join. -/
theorem join_le {first last bound : Profile} (one : Le first bound) (two : Le last bound) :
    Le (join first last) bound :=
  ⟨Nat.max_le.mpr ⟨one.1, two.1⟩, Nat.max_le.mpr ⟨one.2.1, two.2.1⟩,
    Nat.max_le.mpr ⟨one.2.2.1, two.2.2.1⟩, Nat.max_le.mpr ⟨one.2.2.2, two.2.2.2⟩⟩

/-- Larger components retain a joined bound. -/
theorem join_mono {first last otherFirst otherLast : Profile}
    (one : Le first last) (two : Le otherFirst otherLast) :
    Le (join first otherFirst) (join last otherLast) :=
  join_le (one.trans (join_left _ _)) (two.trans (join_right _ _))

/-- One scalar bounds constructor counts and stored payload mass. -/
def scalar (profile : Profile) : Nat := SourceCurrentConstrainedCapTargetForecast.scalar profile

/-- Larger component bounds retain the scalar. -/
theorem scalar_mono {first last : Profile} (increase : Le first last) : scalar first ≤ scalar last :=
  SourceCurrentConstrainedCapTargetForecast.scalar_mono increase

/-- A complete recursive head changes only the constructor heap bounds. -/
def headProfile (profile : Profile) : Profile :=
  let bound := SourceCurrentProjectionUnionResources.headGrowth (scalar profile)
  ⟨bound, bound, profile.domains, bound⟩

/-- The current head read has one initial shared read ceiling. -/
def headFuel (profile : Profile) : Nat :=
  SourceCurrentProjectionUnionResources.readFuel (SourceCurrentProjectionUnionResources.headGrowth (scalar profile))

/-- Head normalization retains all original component bounds. -/
theorem headProfile_ge (profile : Profile) : Le profile (headProfile profile) := by
  have grows := SourceCurrentProjectionUnionResources.headGrowth_ge (scalar profile)
  exact ⟨Nat.le_trans (SourceCurrentConstrainedCapTargetForecast.scalar_nodes profile) grows,
    Nat.le_trans (SourceCurrentConstrainedCapTargetForecast.scalar_edges profile) grows,
    Nat.le_refl _, Nat.le_trans (SourceCurrentConstrainedCapTargetForecast.scalar_mass profile) grows⟩

/-- Larger original components retain the head profile. -/
theorem headProfile_mono {first last : Profile} (increase : Le first last) :
    Le (headProfile first) (headProfile last) := by
  have grow := SourceCurrentProjectionUnionResources.headGrowth_mono (scalar_mono increase)
  exact ⟨grow, grow, increase.2.2.1, grow⟩

/-- Larger original components retain the head read ceiling. -/
theorem headFuel_mono {first last : Profile} (increase : Le first last) : headFuel first ≤ headFuel last :=
  SourceCurrentProjectionUnionResources.readFuel_mono
    (SourceCurrentProjectionUnionResources.headGrowth_mono (scalar_mono increase))

/-- One raw node or edge request pays its literal input list. -/
def constructorProfile (length : Nat) (profile : Profile) : Profile :=
  ⟨profile.nodes + 1, profile.edges + 1, profile.domains, inflate length profile.mass⟩

/-- A constructor forecast retains its original profile. -/
theorem constructorProfile_ge (length : Nat) (profile : Profile) : Le profile (constructorProfile length profile) :=
  ⟨Nat.le_succ _, Nat.le_succ _, Nat.le_refl _, InternedFreshOrdinaryResultMass.inflate_ge _ _⟩

/-- Larger input lists and original components retain constructor bounds. -/
theorem constructorProfile_mono {firstLength lastLength : Nat} (lengths : firstLength ≤ lastLength)
    {first last : Profile} (increase : Le first last) :
    Le (constructorProfile firstLength first) (constructorProfile lastLength last) := by
  have width := SourceRecursiveIntersectionWorkMass.inflate_width lengths first.mass
  have mass := InternedFreshOrdinaryResultMass.inflate_mono lastLength increase.2.2.2
  exact ⟨Nat.add_le_add_right increase.1 1, Nat.add_le_add_right increase.2.1 1,
    increase.2.2.1, Nat.le_trans width mass⟩

/-- Join every original callback token at the same original profile. -/
def leafProfiles (record : SourceEqualityClassOrder.Record) (count : Nat) :
    List EqualityNormalize.Path → Profile → Profile
  | [], profile => profile
  | path :: rest, profile =>
      join (Shared.leafProfile count (operands record.paths path) false profile) (leafProfiles record count rest profile)

/-- Take the largest callback fuel at the same original profile. -/
def leafFuels (record : SourceEqualityClassOrder.Record) (count : Nat) :
    List EqualityNormalize.Path → Profile → Nat
  | [], _ => 0
  | path :: rest, profile =>
      max (Shared.leafFuel count (operands record.paths path) false profile) (leafFuels record count rest profile)

/-- The callback join retains its original profile. -/
theorem leafProfiles_ge (record : SourceEqualityClassOrder.Record) (count : Nat) (paths : List EqualityNormalize.Path)
    (profile : Profile) : Le profile (leafProfiles record count paths profile) := by
  induction paths with
  | nil => exact Le.refl _
  | cons path paths ih => exact ih.trans (join_right _ _)

/-- Larger profiles retain the complete callback join. -/
theorem leafProfiles_mono (record : SourceEqualityClassOrder.Record) (count : Nat) (paths : List EqualityNormalize.Path)
    {first last : Profile} (increase : Le first last) :
    Le (leafProfiles record count paths first) (leafProfiles record count paths last) := by
  induction paths with
  | nil => exact increase
  | cons path paths ih =>
      exact join_mono (SourceCurrentConstrainedCapSharedMonotone.leafProfile_mono count _ false increase) ih

/-- Larger profiles retain the callback fuel ceiling. -/
theorem leafFuels_mono (record : SourceEqualityClassOrder.Record) (count : Nat) (paths : List EqualityNormalize.Path)
    {first last : Profile} (increase : Le first last) :
    leafFuels record count paths first ≤ leafFuels record count paths last := by
  induction paths with
  | nil => exact Nat.le_refl _
  | cons path paths ih =>
      exact Nat.max_le.mpr ⟨Nat.le_trans (SourceCurrentConstrainedCapSharedMonotone.leafFuel_mono count _ false increase)
        (Nat.le_max_left _ _), Nat.le_trans ih (Nat.le_max_right _ _)⟩

/-- Every listed token fits its callback join. -/
theorem leafProfiles_member (record : SourceEqualityClassOrder.Record) (count : Nat)
    {paths : List EqualityNormalize.Path} {path : EqualityNormalize.Path} (member : path ∈ paths) (profile : Profile) :
    Le (Shared.leafProfile count (operands record.paths path) false profile) (leafProfiles record count paths profile) := by
  induction paths with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact join_left _ _
      · exact (ih member).trans (join_right _ _)

/-- Every listed token fits its callback fuel ceiling. -/
theorem leafFuels_member (record : SourceEqualityClassOrder.Record) (count : Nat)
    {paths : List EqualityNormalize.Path} {path : EqualityNormalize.Path} (member : path ∈ paths) (profile : Profile) :
    Shared.leafFuel count (operands record.paths path) false profile ≤ leafFuels record count paths profile := by
  induction paths with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

/-- One stage covers head normalization, raw construction, and every original callback. -/
def stageProfile (record : SourceEqualityClassOrder.Record) (count : Nat) (profile : Profile) : Profile :=
  join (headProfile profile)
    (join (constructorProfile (scalar profile) profile) (leafProfiles record count record.paths profile))

/-- One stage ceiling covers the actual head and every original callback fuel. -/
def stageFuel (record : SourceEqualityClassOrder.Record) (count : Nat) (profile : Profile) : Nat :=
  max (headFuel profile) (leafFuels record count record.paths profile)

/-- A stage retains the original profile. -/
theorem stage_ge (record : SourceEqualityClassOrder.Record) (count : Nat) (profile : Profile) :
    Le profile (stageProfile record count profile) := (headProfile_ge profile).trans (join_left _ _)

/-- Larger original components retain the stage profile. -/
theorem stage_mono (record : SourceEqualityClassOrder.Record) (count : Nat) {first last : Profile}
    (increase : Le first last) : Le (stageProfile record count first) (stageProfile record count last) :=
  join_mono (headProfile_mono increase)
    (join_mono (constructorProfile_mono (scalar_mono increase) increase)
      (leafProfiles_mono record count record.paths increase))

/-- Larger original components retain the complete stage fuel ceiling. -/
theorem stageFuel_mono (record : SourceEqualityClassOrder.Record) (count : Nat) {first last : Profile}
    (increase : Le first last) : stageFuel record count first ≤ stageFuel record count last :=
  Nat.max_le.mpr ⟨Nat.le_trans (headFuel_mono increase) (Nat.le_max_left _ _),
    Nat.le_trans (leafFuels_mono record count record.paths increase) (Nat.le_max_right _ _)⟩

/-- The actual head return fits its stage. -/
theorem stage_head_profile (record : SourceEqualityClassOrder.Record) (count : Nat) (profile : Profile) :
    Le (headProfile profile) (stageProfile record count profile) := join_left _ _

/-- The actual head read uses at most the common stage ceiling. -/
theorem stage_head_fuel (record : SourceEqualityClassOrder.Record) (count : Nat) (profile : Profile) :
    headFuel profile ≤ stageFuel record count profile := Nat.le_max_left _ _

/-- Any literal constructor list within the entry scalar fits its stage. -/
theorem stage_constructor_profile (record : SourceEqualityClassOrder.Record) (count : Nat) (profile : Profile)
    {length : Nat} (width : length ≤ scalar profile) :
    Le (constructorProfile length profile) (stageProfile record count profile) :=
  (constructorProfile_mono width (Le.refl profile)).trans ((join_left _ _).trans (join_right _ _))

/-- Either actual slot branch fits the all-miss callback stage. -/
theorem stage_leaf_profile (record : SourceEqualityClassOrder.Record) (count : Nat) (path : EqualityNormalize.Path)
    (found : Bool) (profile : Profile) (member : path ∈ record.paths) :
    Le (Shared.leafProfile count (operands record.paths path) found profile) (stageProfile record count profile) :=
  (SourceCurrentConstrainedCapSharedMonotone.leafProfile_le_miss count _ found (Le.refl profile)).trans
    ((leafProfiles_member record count member profile).trans ((join_right _ _).trans (join_right _ _)))

/-- Either actual slot branch uses at most the common stage ceiling. -/
theorem stage_leaf_fuel (record : SourceEqualityClassOrder.Record) (count : Nat) (path : EqualityNormalize.Path)
    (found : Bool) (profile : Profile) (member : path ∈ record.paths) :
    Shared.leafFuel count (operands record.paths path) found profile ≤ stageFuel record count profile :=
  Nat.le_trans (SourceCurrentConstrainedCapSharedMonotone.leafFuel_le_miss count _ found (Le.refl profile))
    (Nat.le_trans (leafFuels_member record count member profile) (Nat.le_max_right _ _))

private theorem leaf_reserved_of_room (bits count : Nat) (paths : List (List Int)) (profile : Profile)
    (room : Room bits (Shared.leafProfile count paths false profile)) :
    Shared.LeafReserved bits count paths false profile := by
  have forceRoom := room.mono (SourceCurrentConstrainedCapSharedForecast.forceProfile_le_leafProfile count paths false profile)
  refine ⟨?_, forceRoom⟩
  cases paths with
  | nil => trivial
  | cons seed rest =>
      exact SourceCurrentConstrainedCapTargetForecast.reserved_of_final_room bits count seed rest profile forceRoom

/-- One stage room test supplies either actual callback branch at every smaller entry. -/
theorem stage_leaf_reserved (record : SourceEqualityClassOrder.Record) (count bits : Nat)
    (path : EqualityNormalize.Path) (found : Bool) {first last : Profile} (increase : Le first last)
    (member : path ∈ record.paths) (room : Room bits (stageProfile record count last)) :
    Shared.LeafReserved bits count (operands record.paths path) found first :=
  SourceCurrentConstrainedCapSharedMonotone.leafReserved_of_miss bits count _ found increase
    (leaf_reserved_of_room bits count _ last (room.mono (stage_leaf_profile record count path false last member)))

/-- Apply one growing profile transformation a fixed number of times. -/
def scan (next : Profile → Profile) : Nat → Profile → Profile
  | 0, profile => profile
  | count + 1, profile => scan next count (next profile)

/-- An empty scan retains its entry profile. -/
theorem scan_zero (next : Profile → Profile) (profile : Profile) : scan next 0 profile = profile := rfl

/-- One scan step precedes its remaining fixed scan. -/
theorem scan_succ (next : Profile → Profile) (count : Nat) (profile : Profile) :
    scan next (count + 1) profile = scan next count (next profile) := rfl

/-- A growing transformation retains the original scan entry. -/
theorem scan_ge (next : Profile → Profile) (grows : ∀ profile, Le profile (next profile))
    (count : Nat) (profile : Profile) : Le profile (scan next count profile) := by
  induction count generalizing profile with
  | zero => exact Le.refl _
  | succ count ih => exact (grows profile).trans (ih (next profile))

/-- A monotone transformation retains larger scan entries. -/
theorem scan_mono (next : Profile → Profile)
    (mono : ∀ {first last}, Le first last → Le (next first) (next last))
    (count : Nat) {first last : Profile} (increase : Le first last) :
    Le (scan next count first) (scan next count last) := by
  induction count generalizing first last with
  | zero => exact increase
  | succ count ih => exact ih (mono increase)

/-- Consecutive scans compose at the exact intermediate forecast. -/
theorem scan_add (next : Profile → Profile) (first last : Nat) (profile : Profile) :
    scan next (first + last) profile = scan next last (scan next first profile) := by
  induction first generalizing profile with
  | zero => rfl
  | succ first ih => simpa only [Nat.succ_add, scan] using ih (next profile)

/-- A longer growing scan retains every earlier forecast. -/
theorem scan_count_mono (next : Profile → Profile) (grows : ∀ profile, Le profile (next profile))
    {first last : Nat} (counts : first ≤ last) (profile : Profile) :
    Le (scan next first profile) (scan next last profile) := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le counts
  rw [scan_add]
  exact scan_ge next grows extra _

/-- A pointwise larger monotone transformation retains a fixed scan. -/
theorem scan_compare (firstStep lastStep : Profile → Profile)
    (mono : ∀ {first last}, Le first last → Le (lastStep first) (lastStep last))
    (compare : ∀ profile, Le (firstStep profile) (lastStep profile))
    (count : Nat) {first last : Profile} (increase : Le first last) :
    Le (scan firstStep count first) (scan lastStep count last) := by
  induction count generalizing first last with
  | zero => exact increase
  | succ count ih => exact ih ((compare first).trans (mono increase))

/-- Larger scan counts, transformations, and entries compose. -/
theorem scan_joint (firstStep lastStep : Profile → Profile)
    (grows : ∀ profile, Le profile (lastStep profile))
    (mono : ∀ {first last}, Le first last → Le (lastStep first) (lastStep last))
    (compare : ∀ profile, Le (firstStep profile) (lastStep profile))
    {firstCount lastCount : Nat} (counts : firstCount ≤ lastCount) {first last : Profile} (increase : Le first last) :
    Le (scan firstStep firstCount first) (scan lastStep lastCount last) :=
  (scan_compare firstStep lastStep mono compare firstCount increase).trans
    (scan_count_mono lastStep grows counts last)

/-- Each selected child's complete return fits any nonempty enclosing scan. -/
theorem scan_child (next : Profile → Profile) (grows : ∀ profile, Le profile (next profile))
    {count : Nat} (positive : 0 < count) (profile : Profile) : Le (next profile) (scan next count profile) :=
  scan_count_mono next grows (show 1 ≤ count by omega) profile

/-- Every earlier scan entry fits the complete scan. -/
theorem scan_prefix (next : Profile → Profile) (grows : ∀ profile, Le profile (next profile))
    {index count : Nat} (inside : index ≤ count) (profile : Profile) :
    Le (scan next index profile) (scan next count profile) := scan_count_mono next grows inside profile

/-- Reserve one stage around fixed row and child scans at each finite syntax level. -/
def planProfile (record : SourceEqualityClassOrder.Record) (count : Nat) : Nat → Profile → Profile
  | 0, profile => stageProfile record count profile
  | level + 1, profile =>
      let start := stageProfile record count profile
      let width := scalar start
      let row := fun current => stageProfile record count (scan (planProfile record count level) width current)
      stageProfile record count (scan row width start)

/-- One original row scans its fixed child limit before the edge stage. -/
def rowStep (record : SourceEqualityClassOrder.Record) (count level width : Nat) (profile : Profile) : Profile :=
  stageProfile record count (scan (planProfile record count level) width profile)

/-- The base reserves its own actual stage. -/
theorem plan_zero (record : SourceEqualityClassOrder.Record) (count : Nat) (profile : Profile) :
    planProfile record count 0 profile = stageProfile record count profile := rfl

/-- A successor fixes its row and child widths before either scan. -/
theorem plan_succ (record : SourceEqualityClassOrder.Record) (count level : Nat) (profile : Profile) :
    planProfile record count (level + 1) profile =
      stageProfile record count (scan (rowStep record count level (scalar (stageProfile record count profile)))
        (scalar (stageProfile record count profile)) (stageProfile record count profile)) := rfl

/-- Every finite plan retains its original entry. -/
theorem plan_ge (record : SourceEqualityClassOrder.Record) (count level : Nat) (profile : Profile) :
    Le profile (planProfile record count level profile) := by
  induction level generalizing profile with
  | zero => exact stage_ge record count profile
  | succ level ih =>
      let start := stageProfile record count profile
      let width := scalar start
      have rowGrows : ∀ current, Le current (rowStep record count level width current) :=
        fun current => (scan_ge _ ih width current).trans (stage_ge record count _)
      exact (stage_ge record count profile).trans
        ((scan_ge _ rowGrows width start).trans (stage_ge record count _))

/-- One row retains its original entry. -/
theorem rowStep_ge (record : SourceEqualityClassOrder.Record) (count level width : Nat) (profile : Profile) :
    Le profile (rowStep record count level width profile) :=
  (scan_ge _ (plan_ge record count level) width profile).trans (stage_ge record count _)

/-- Larger initial component bounds retain the complete finite plan. -/
theorem plan_mono (record : SourceEqualityClassOrder.Record) (count level : Nat)
    {first last : Profile} (increase : Le first last) :
    Le (planProfile record count level first) (planProfile record count level last) := by
  induction level generalizing first last with
  | zero => exact stage_mono record count increase
  | succ level ih =>
      have start := stage_mono record count increase
      have widths := scalar_mono start
      have rowMono : ∀ width, ∀ {first last}, Le first last →
          Le (rowStep record count level width first) (rowStep record count level width last) :=
        fun width _ _ enough => stage_mono record count (scan_mono _ ih width enough)
      have rowCompare : ∀ current,
          Le (rowStep record count level (scalar (stageProfile record count first)) current)
            (rowStep record count level (scalar (stageProfile record count last)) current) :=
        fun current => stage_mono record count (scan_count_mono _ (plan_ge record count level) widths current)
      exact stage_mono record count
        (scan_joint _ _ (rowStep_ge record count level _) (rowMono _) rowCompare widths start)

/-- Larger child limits and row entries retain the complete row forecast. -/
theorem rowStep_mono (record : SourceEqualityClassOrder.Record) (count level : Nat)
    {firstWidth lastWidth : Nat} (widths : firstWidth ≤ lastWidth)
    {first last : Profile} (increase : Le first last) :
    Le (rowStep record count level firstWidth first) (rowStep record count level lastWidth last) :=
  stage_mono record count
    (scan_joint _ _ (plan_ge record count level) (plan_mono record count level) (fun value => Le.refl _) widths increase)

/-- A plan contains the initial head, constructor, and callback stage. -/
theorem plan_stage (record : SourceEqualityClassOrder.Record) (count level : Nat) (profile : Profile) :
    Le (stageProfile record count profile) (planProfile record count level profile) := by
  cases level with
  | zero => exact Le.refl _
  | succ level =>
      exact (scan_ge _ (rowStep_ge record count level _) _ _).trans (stage_ge record count _)

/-- The last scan step acts at the exact preceding forecast. -/
theorem scan_succ_right (next : Profile → Profile) (count : Nat) (profile : Profile) :
    scan next (count + 1) profile = next (scan next count profile) := by
  exact scan_add next count 1 profile

/-- Any scheduled row entry fits the complete plan. -/
theorem plan_row_entry (record : SourceEqualityClassOrder.Record) (count level : Nat) (profile : Profile)
    {index : Nat} (inside : index ≤ scalar (stageProfile record count profile)) :
    Le (scan (rowStep record count level (scalar (stageProfile record count profile))) index
      (stageProfile record count profile)) (planProfile record count (level + 1) profile) :=
  (scan_count_mono _ (rowStep_ge record count level _) inside _).trans (stage_ge record count _)

/-- Any scheduled row return fits the complete plan. -/
theorem plan_row_return (record : SourceEqualityClassOrder.Record) (count level : Nat) (profile : Profile)
    {index : Nat} (inside : index < scalar (stageProfile record count profile)) :
    Le (rowStep record count level (scalar (stageProfile record count profile))
      (scan (rowStep record count level (scalar (stageProfile record count profile))) index
        (stageProfile record count profile))) (planProfile record count (level + 1) profile) := by
  have enough := plan_row_entry record count level profile (show index + 1 ≤ scalar (stageProfile record count profile) by omega)
  rw [scan_succ_right] at enough
  exact enough

/-- Every scheduled child entry fits its row return and complete plan. -/
theorem plan_child_entry (record : SourceEqualityClassOrder.Record) (count level : Nat) (profile : Profile)
    {row child : Nat} (rowInside : row < scalar (stageProfile record count profile))
    (childInside : child ≤ scalar (stageProfile record count profile)) :
    Le (scan (planProfile record count level) child
      (scan (rowStep record count level (scalar (stageProfile record count profile))) row
        (stageProfile record count profile))) (planProfile record count (level + 1) profile) :=
  (scan_count_mono _ (plan_ge record count level) childInside _).trans
    ((stage_ge record count _).trans (plan_row_return record count level profile rowInside))

/-- A selected child's complete forecast fits its enclosing row and complete plan. -/
theorem plan_child_return (record : SourceEqualityClassOrder.Record) (count level : Nat) (profile : Profile)
    {row child : Nat} (rowInside : row < scalar (stageProfile record count profile))
    (childInside : child < scalar (stageProfile record count profile)) :
    Le (planProfile record count level (scan (planProfile record count level) child
      (scan (rowStep record count level (scalar (stageProfile record count profile))) row
        (stageProfile record count profile)))) (planProfile record count (level + 1) profile) := by
  have enough := plan_child_entry record count level profile rowInside
    (show child + 1 ≤ scalar (stageProfile record count profile) by omega)
  rw [scan_succ_right] at enough
  exact enough

end MicroCFTA.SourceCurrentConstrainedCapEditForecast
