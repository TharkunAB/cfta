import MicroCFTA.SourceCurrentConstrainedCapOperandNumeric
import MicroCFTA.SourceCurrentAllocatedNativeResourceForecast

/-!
# Initial forecasts for interleaved Target execution

The schedule runs a head Operand, then the remaining Fold, then its native
query. Each reservation checks the numeric profile at that query entry.
The shared fuel ceiling covers all five literal Target worker fuels.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapTargetForecast
open SourceCurrentAllocatedNativeResourceForecast (Profile Le Room)
local notation "Forecast" => SourceCurrentAllocatedNativeResourceForecast.step
local notation "OperandWork" => SourceCurrentConstrainedCapOperandNumeric.workFuel
local notation "instructionBound" => SourceCurrentAllocatedNativeComputedBudget.instructionBound

/-- One scalar covers both issued constructor counters and causal payload mass. -/
def scalar (profile : Profile) : Nat := max (max profile.nodes profile.edges) profile.mass

/-- Projection and Merge retain the domain counter and update the three heap bounds. -/
def operand (path : List Int) (count : Nat) (profile : Profile) : Profile :=
  let bound := OperandWork path count (scalar profile)
  ⟨bound, bound, profile.domains, bound⟩

/-- Each Fold forecasts its head Operand before its tail and final native query. -/
def foldProfile (count : Nat) (seed : List Int) : List (List Int) → Profile → Profile
  | [], profile => operand seed count profile
  | path :: rest, profile => Forecast (foldProfile count seed rest (operand path count profile))

/-- An empty Target keeps the complete initial profile. -/
def targetProfile (count : Nat) : List (List Int) → Profile → Profile
  | [], profile => profile
  | seed :: rest, profile => foldProfile count seed rest profile

/-- Initial reservations check the exact forecast entry of each interposed query. -/
def Reserved (bits count : Nat) (seed : List Int) : List (List Int) → Profile → Prop
  | [], _ => True
  | path :: rest, profile =>
      Reserved bits count seed rest (operand path count profile) ∧
        Room bits (foldProfile count seed rest (operand path count profile))

/-- Target reservations preserve the empty branch and its distinct seed. -/
def TargetReserved (bits count : Nat) : List (List Int) → Profile → Prop
  | [], _ => True
  | seed :: rest, profile => Reserved bits count seed rest profile

/-- The scalar covers the initial node counter. -/
theorem scalar_nodes (profile : Profile) : profile.nodes ≤ scalar profile := by unfold scalar; omega

/-- The scalar covers the initial edge counter. -/
theorem scalar_edges (profile : Profile) : profile.edges ≤ scalar profile := by unfold scalar; omega

/-- The scalar covers every initial payload mass. -/
theorem scalar_mass (profile : Profile) : profile.mass ≤ scalar profile := by unfold scalar; omega

/-- Larger component bounds retain the scalar heap bound. -/
theorem scalar_mono {first last : Profile} (increase : Le first last) : scalar first ≤ scalar last := by
  unfold scalar
  rcases increase with ⟨nodes, edges, domains, mass⟩
  omega

/-- The complete Operand work ceiling retains its original scalar. -/
theorem scalar_le_operand (path : List Int) (count : Nat) (profile : Profile) :
    scalar profile ≤ OperandWork path count (scalar profile) := by
  have projected := SourceCurrentProjectionInitialResources.forestBound_ge path count (scalar profile)
  have merged := SourceCurrentMemoMergeNumericControl.bound_ge
    (SourceCurrentConstrainedCapOperandNumeric.projectionBound path count (scalar profile))
    (SourceCurrentConstrainedCapOperandNumeric.projectionBound path count (scalar profile))
  change SourceCurrentConstrainedCapOperandNumeric.projectionBound path count (scalar profile) + 2 ≤
    OperandWork path count (scalar profile) at merged
  exact Nat.le_trans projected (by omega)

/-- An Operand forecast retains every initial profile component. -/
theorem operand_ge (path : List Int) (count : Nat) (profile : Profile) : Le profile (operand path count profile) := by
  have retained := scalar_le_operand path count profile
  exact ⟨Nat.le_trans (scalar_nodes profile) retained, Nat.le_trans (scalar_edges profile) retained,
    Nat.le_refl _, Nat.le_trans (scalar_mass profile) retained⟩

/-- Projection and Merge leave the domain counter forecast unchanged. -/
theorem operand_domains (path : List Int) (count : Nat) (profile : Profile) :
    (operand path count profile).domains = profile.domains := rfl

/-- A Fold base forecasts only its original seed Operand. -/
theorem foldProfile_nil (count : Nat) (seed : List Int) (profile : Profile) :
    foldProfile count seed [] profile = operand seed count profile := rfl

/-- A Fold step retains the exact profile between its head, tail, and query. -/
theorem foldProfile_cons (count : Nat) (seed path : List Int) (rest : List (List Int)) (profile : Profile) :
    foldProfile count seed (path :: rest) profile =
      Forecast (foldProfile count seed rest (operand path count profile)) := rfl

/-- The complete Fold schedule retains its initial profile. -/
theorem foldProfile_ge (count : Nat) (seed : List Int) (paths : List (List Int)) (profile : Profile) :
    Le profile (foldProfile count seed paths profile) := by
  induction paths generalizing profile with
  | nil => exact operand_ge seed count profile
  | cons path rest ih =>
      exact (operand_ge path count profile).trans
        ((ih (operand path count profile)).trans (SourceCurrentAllocatedNativeResourceForecast.step_ge _))

/-- The completed head Operand profile fits the full remaining Fold forecast. -/
theorem fold_head_le (count : Nat) (seed path : List Int) (rest : List (List Int)) (profile : Profile) :
    Le (operand path count profile) (foldProfile count seed (path :: rest) profile) :=
  (foldProfile_ge count seed rest _).trans (SourceCurrentAllocatedNativeResourceForecast.step_ge _)

/-- The exact query-entry profile fits the Fold return forecast. -/
theorem fold_tail_le (count : Nat) (seed path : List Int) (rest : List (List Int)) (profile : Profile) :
    Le (foldProfile count seed rest (operand path count profile)) (foldProfile count seed (path :: rest) profile) :=
  SourceCurrentAllocatedNativeResourceForecast.step_ge _

/-- An empty Target returns its original profile. -/
theorem targetProfile_nil (count : Nat) (profile : Profile) : targetProfile count [] profile = profile := rfl

/-- A nonempty Target uses its original seed and remaining Fold schedule. -/
theorem targetProfile_cons (count : Nat) (seed : List Int) (rest : List (List Int)) (profile : Profile) :
    targetProfile count (seed :: rest) profile = foldProfile count seed rest profile := rfl

/-- The complete Target forecast retains every original profile component. -/
theorem targetProfile_ge (count : Nat) (paths : List (List Int)) (profile : Profile) :
    Le profile (targetProfile count paths profile) := by
  cases paths with
  | nil => exact Le.refl _
  | cons seed rest => exact foldProfile_ge count seed rest profile

/-- A Fold with no interposed query needs no query-entry reservation. -/
theorem reserved_nil (bits count : Nat) (seed : List Int) (profile : Profile) : Reserved bits count seed [] profile := trivial

/-- A Fold reservation has exactly its tail reservation and reached query-entry room. -/
theorem reserved_cons_iff (bits count : Nat) (seed path : List Int) (rest : List (List Int)) (profile : Profile) :
    Reserved bits count seed (path :: rest) profile ↔
      Reserved bits count seed rest (operand path count profile) ∧
        Room bits (foldProfile count seed rest (operand path count profile)) := Iff.rfl

/-- The initial reservation supplies the remaining Fold at its head Operand forecast. -/
theorem Reserved.tail {bits count : Nat} {seed path : List Int} {rest : List (List Int)} {profile : Profile}
    (reserved : Reserved bits count seed (path :: rest) profile) :
    Reserved bits count seed rest (operand path count profile) := reserved.1

/-- The same reservation supplies room at the actual scheduled query entry. -/
theorem Reserved.query {bits count : Nat} {seed path : List Int} {rest : List (List Int)} {profile : Profile}
    (reserved : Reserved bits count seed (path :: rest) profile) :
    Room bits (foldProfile count seed rest (operand path count profile)) := reserved.2

/-- One stronger room test at the final profile supplies every earlier query-entry reservation. -/
theorem reserved_of_final_room (bits count : Nat) (seed : List Int) (paths : List (List Int)) (profile : Profile)
    (room : Room bits (foldProfile count seed paths profile)) : Reserved bits count seed paths profile := by
  induction paths generalizing profile with
  | nil => trivial
  | cons path rest ih =>
      have earlier := room.mono (fold_tail_le count seed path rest profile)
      exact ⟨ih (operand path count profile) earlier, earlier⟩

/-- An empty Target needs no native query-entry room. -/
theorem targetReserved_nil (bits count : Nat) (profile : Profile) : TargetReserved bits count [] profile := trivial

/-- A nonempty Target retains the Fold reservation at its original seed. -/
theorem targetReserved_cons_iff (bits count : Nat) (seed : List Int) (rest : List (List Int)) (profile : Profile) :
    TargetReserved bits count (seed :: rest) profile ↔ Reserved bits count seed rest profile := Iff.rfl

/-- The shared Operand ceiling covers projection, read, Merge, and selection fuels. -/
def operandFuel (path : List Int) (count : Nat) (profile : Profile) : Nat :=
  max (SourceCurrentProjectionNumeric.workFuel path)
    (max (SourceCurrentProjectionNumeric.readFuel path count (scalar profile))
      (max (OperandWork path count (scalar profile))
        (SourceCurrentConstrainedCapOperandNumeric.selectionFuel path count (scalar profile))))

/-- One native query uses its initial instruction bound and final pure return step. -/
def queryFuel (profile : Profile) : Nat := instructionBound profile.nodes profile.edges profile.mass + 1

/-- One shared ceiling covers the literal head, tail, and query fuels in source order. -/
def foldFuel (count : Nat) (seed : List Int) : List (List Int) → Profile → Nat
  | [], profile => operandFuel seed count profile
  | path :: rest, profile =>
      max (operandFuel path count profile)
        (max (foldFuel count seed rest (operand path count profile))
          (queryFuel (foldProfile count seed rest (operand path count profile))))

/-- Empty Targets use no fuel; nonempty Targets use their complete Fold ceiling. -/
def targetFuel (count : Nat) : List (List Int) → Profile → Nat
  | [], _ => 0
  | seed :: rest, profile => foldFuel count seed rest profile

/-- The shared Operand fuel covers its literal projection worker. -/
theorem operandFuel_projection (path : List Int) (count : Nat) (profile : Profile) :
    SourceCurrentProjectionNumeric.workFuel path ≤ operandFuel path count profile := Nat.le_max_left _ _

/-- The shared Operand fuel covers every recursive projection read. -/
theorem operandFuel_read (path : List Int) (count : Nat) (profile : Profile) :
    SourceCurrentProjectionNumeric.readFuel path count (scalar profile) ≤ operandFuel path count profile :=
  Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

/-- The shared Operand fuel covers the complete Merge worker. -/
theorem operandFuel_merge (path : List Int) (count : Nat) (profile : Profile) :
    OperandWork path count (scalar profile) ≤ operandFuel path count profile :=
  Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))

/-- The shared Operand fuel covers every Merge selection. -/
theorem operandFuel_selection (path : List Int) (count : Nat) (profile : Profile) :
    SourceCurrentConstrainedCapOperandNumeric.selectionFuel path count (scalar profile) ≤ operandFuel path count profile :=
  Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))

/-- A Fold base uses exactly its seed Operand ceiling. -/
theorem foldFuel_nil (count : Nat) (seed : List Int) (profile : Profile) :
    foldFuel count seed [] profile = operandFuel seed count profile := rfl

/-- A Fold step uses the exact head, tail, and query-entry profiles. -/
theorem foldFuel_cons (count : Nat) (seed path : List Int) (rest : List (List Int)) (profile : Profile) :
    foldFuel count seed (path :: rest) profile =
      max (operandFuel path count profile)
        (max (foldFuel count seed rest (operand path count profile))
          (queryFuel (foldProfile count seed rest (operand path count profile)))) := rfl

/-- The shared Fold ceiling covers its actual head Operand. -/
theorem foldFuel_head (count : Nat) (seed path : List Int) (rest : List (List Int)) (profile : Profile) :
    operandFuel path count profile ≤ foldFuel count seed (path :: rest) profile := Nat.le_max_left _ _

/-- The shared Fold ceiling covers its tail at the reached head profile. -/
theorem foldFuel_tail (count : Nat) (seed path : List Int) (rest : List (List Int)) (profile : Profile) :
    foldFuel count seed rest (operand path count profile) ≤ foldFuel count seed (path :: rest) profile :=
  Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

/-- The shared Fold ceiling covers the native query at its exact tail-return profile. -/
theorem foldFuel_query (count : Nat) (seed path : List Int) (rest : List (List Int)) (profile : Profile) :
    queryFuel (foldProfile count seed rest (operand path count profile)) ≤ foldFuel count seed (path :: rest) profile :=
  Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

/-- The literal empty Target uses zero of every worker fuel. -/
theorem targetFuel_nil (count : Nat) (profile : Profile) : targetFuel count [] profile = 0 := rfl

/-- A nonempty Target shares the complete Fold ceiling across all worker fuels. -/
theorem targetFuel_cons (count : Nat) (seed : List Int) (rest : List (List Int)) (profile : Profile) :
    targetFuel count (seed :: rest) profile = foldFuel count seed rest profile := rfl

end MicroCFTA.SourceCurrentConstrainedCapTargetForecast
