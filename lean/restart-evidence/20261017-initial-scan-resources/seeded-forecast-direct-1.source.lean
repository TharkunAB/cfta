import MicroCFTA.SourceCurrentProjectionNumericControl
import MicroCFTA.SourceCurrentOpenRowReadResources
import MicroCFTA.SourceCurrentConstrainedCapTargetForecast

/-!
# Initial profiles for first-seeded supported queries

Projection permits supported open warm heads. The fold projects its head,
then its tail, then runs the checked native query. Projection performs no
Merge call. The first original path remains the final source seed.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapSeededForecast
open SourceCurrentAllocatedNativeResourceForecast (Profile Le Room step)
open SourceCurrentProjectionNumericControl (ordinary rowsBound)
export SourceCurrentConstrainedCapTargetForecast (scalar scalar_nodes scalar_edges scalar_mass scalar_mono queryFuel)

/-- A proper node path first pays its possible supported open Head. -/
def nodeBound : Nat → Nat → Nat
  | 0, resource => resource + 1
  | depth + 1, resource => ordinary (nodeBound depth) (SourceCurrentOpenRowReadResources.headGrowth resource)

/-- Each finite selected path retains its initial scalar. -/
theorem nodeBound_ge (depth resource : Nat) : resource ≤ nodeBound depth resource := by
  cases depth with
  | zero => exact Nat.le_succ _
  | succ depth => exact Nat.le_trans (SourceCurrentOpenRowReadResources.headGrowth_ge resource)
      (SourceCurrentProjectionNumericControl.ordinary_ge _ _)

/-- Larger initial scalars retain the selected node forecast. -/
theorem nodeBound_mono (depth : Nat) {first last : Nat} (increase : first ≤ last) :
    nodeBound depth first ≤ nodeBound depth last := by
  induction depth generalizing first last with
  | zero => exact Nat.add_le_add_right increase 1
  | succ depth ih => exact SourceCurrentProjectionNumericControl.ordinary_mono _ (fun enough => ih enough)
      (SourceCurrentOpenRowReadResources.headGrowth_mono increase)

/-- A direct ordinary step fits the branch that also reserves a Head. -/
theorem ordinary_le_nodeBound (depth resource : Nat) : ordinary (nodeBound depth) resource ≤ nodeBound (depth + 1) resource :=
  SourceCurrentProjectionNumericControl.ordinary_mono _ (nodeBound_mono depth)
    (SourceCurrentOpenRowReadResources.headGrowth_ge resource)

/-- The reached Head return fits the following ordinary phase. -/
theorem head_le_nodeBound (depth resource : Nat) :
    SourceCurrentOpenRowReadResources.headGrowth resource ≤ nodeBound (depth + 1) resource :=
  SourceCurrentProjectionNumericControl.ordinary_ge _ _

/-- Root union visits all original values; proper paths select one original value. -/
def forestBound (path : List Int) (count resource : Nat) : Nat :=
  match path with
  | [] => SourceCurrentProjectionUnionResources.unionGrowth count resource
  | _ :: rest => nodeBound rest.length resource

/-- Every forest projection retains its initial scalar. -/
theorem forestBound_ge (path : List Int) (count resource : Nat) : resource ≤ forestBound path count resource := by
  cases path with
  | nil => exact SourceCurrentProjectionUnionResources.unionGrowth_ge _ _
  | cons => exact nodeBound_ge _ _

/-- Projection changes constructor supplies and mass, while retaining the domain supply. -/
def projectionProfile (path : List Int) (count : Nat) (profile : Profile) : Profile :=
  let resource := forestBound path count (scalar profile)
  ⟨resource, resource, profile.domains, resource⟩

/-- Projection retains all original numeric components. -/
theorem projection_ge (path : List Int) (count : Nat) (profile : Profile) : Le profile (projectionProfile path count profile) := by
  have enough := forestBound_ge path count (scalar profile)
  exact ⟨Nat.le_trans (scalar_nodes profile) enough, Nat.le_trans (scalar_edges profile) enough,
    Nat.le_refl _, Nat.le_trans (scalar_mass profile) enough⟩

/-- One projection ceiling covers its path worker and every demanded supported read. -/
def projectionFuel (path : List Int) (count : Nat) (profile : Profile) : Nat :=
  max (SourceCurrentProjectionNumeric.workFuel path)
    (SourceCurrentOpenRowReadResources.readFuel (forestBound path count (scalar profile)))

/-- A fold predicts the literal head, tail, and final query order. -/
def foldProfile (count : Nat) (seed : List Int) : List (List Int) → Profile → Profile
  | [], profile => projectionProfile seed count profile
  | path :: rest, profile => step (foldProfile count seed rest (projectionProfile path count profile))

/-- An empty seeded query keeps its original state. -/
def finalProfile (count : Nat) : List (List Int) → Profile → Profile
  | [], profile => profile
  | seed :: rest, profile => foldProfile count seed rest profile

/-- Query room is required only at the pure predicted native entries. -/
def Reserved (bits count : Nat) (seed : List Int) : List (List Int) → Profile → Prop
  | [], _ => True
  | path :: rest, profile => Reserved bits count seed rest (projectionProfile path count profile) ∧
      Room bits (foldProfile count seed rest (projectionProfile path count profile))

/-- Empty input needs no query room; nonempty input retains its first seed. -/
def SeededReserved (bits count : Nat) : List (List Int) → Profile → Prop
  | [], _ => True
  | seed :: rest, profile => Reserved bits count seed rest profile

/-- Every complete fold retains its original numeric profile. -/
theorem fold_ge (count : Nat) (seed : List Int) (paths : List (List Int)) (profile : Profile) :
    Le profile (foldProfile count seed paths profile) := by
  induction paths generalizing profile with
  | nil => exact projection_ge seed count profile
  | cons path rest ih => exact (projection_ge path count profile).trans
      ((ih _).trans (SourceCurrentAllocatedNativeResourceForecast.step_ge _))

/-- The query-entry profile fits the final fold profile. -/
theorem fold_tail_le (count : Nat) (seed path : List Int) (rest : List (List Int)) (profile : Profile) :
    Le (foldProfile count seed rest (projectionProfile path count profile)) (foldProfile count seed (path :: rest) profile) :=
  SourceCurrentAllocatedNativeResourceForecast.step_ge _

/-- The final pure profile supplies every earlier native entry reservation. -/
theorem reserved_of_final_room (bits count : Nat) (seed : List Int) (paths : List (List Int)) (profile : Profile)
    (room : Room bits (foldProfile count seed paths profile)) : Reserved bits count seed paths profile := by
  induction paths generalizing profile with
  | nil => trivial
  | cons path rest ih =>
      have earlier := room.mono (fold_tail_le count seed path rest profile)
      exact ⟨ih _ earlier, earlier⟩

/-- One shared ceiling covers every literal fold stage. -/
def foldFuel (count : Nat) (seed : List Int) : List (List Int) → Profile → Nat
  | [], profile => projectionFuel seed count profile
  | path :: rest, profile => max (projectionFuel path count profile)
      (max (foldFuel count seed rest (projectionProfile path count profile))
        (queryFuel (foldProfile count seed rest (projectionProfile path count profile))))

/-- Empty input needs no fuel; nonempty input uses its exact first-seed fold. -/
def fuel (count : Nat) : List (List Int) → Profile → Nat
  | [], _ => 0
  | seed :: rest, profile => foldFuel count seed rest profile

/-- The fold ceiling includes its actual head projection. -/
theorem fuel_head (count : Nat) (seed path : List Int) (rest : List (List Int)) (profile : Profile) :
    projectionFuel path count profile ≤ foldFuel count seed (path :: rest) profile := Nat.le_max_left _ _
/-- The fold ceiling includes its complete actual tail. -/
theorem fuel_tail (count : Nat) (seed path : List Int) (rest : List (List Int)) (profile : Profile) :
    foldFuel count seed rest (projectionProfile path count profile) ≤ foldFuel count seed (path :: rest) profile :=
  Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
/-- The fold ceiling includes the native query at the exact tail return. -/
theorem fuel_query (count : Nat) (seed path : List Int) (rest : List (List Int)) (profile : Profile) :
    queryFuel (foldProfile count seed rest (projectionProfile path count profile)) ≤ foldFuel count seed (path :: rest) profile :=
  Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
end MicroCFTA.SourceCurrentConstrainedCapSeededForecast
