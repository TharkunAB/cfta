import MicroCFTA.SourceCurrentAllocatedPartialGraph
import MicroCFTA.EqualityModel

/-!
# Strict inherited descent at an actual outer child request

A ready nonempty live payload has a positive maximum path length.
Actual indexed descent strictly lowers that length, including completed
memo hits. The result therefore has a different canonical identity.
This result covers immediate descent without new local combination.
It does not order all ancestors or prove general outer completion.
-/
namespace MicroCFTA.SourceCurrentOuterInheritedDescent
open EqualityNormalize SourceEqualityClassOrder SourceEqualityConstraintAllocation
local notation "Operations" => SourceEqualityConstraintMemoAllocation.State

/-- The longest class path in the complete physical inherited payload. -/
def pathHeight : Value → Nat
  | .contradiction => 0
  | .live _ records => EqualityModel.depth (records.flatMap Record.paths)

private theorem path_le (records : List Record) (record : Record) (member : record ∈ records)
    (path : Path) (included : path ∈ record.paths) :
    path.length ≤ EqualityModel.depth (records.flatMap Record.paths) :=
  EqualityModel.le_maxOn List.length _ path (List.mem_flatMap.mpr ⟨record, member, included⟩)

/-- A well-formed nonempty inherited payload contains a positive-length path. -/
theorem positive (identity : Nat) (records : List Record) (nonempty : records ≠ [])
    (wellFormed : SourceEqualityDescend.WellFormed (some records)) :
    0 < pathHeight (.live identity records) := by
  obtain ⟨record, member⟩ := List.exists_mem_of_ne_nil records nonempty
  obtain ⟨left, leftMember, right, rightMember, different⟩ := (wellFormed records rfl record member).2.2
  have leftBound := path_le records record member left leftMember
  have rightBound := path_le records record member right rightMember
  change 0 < EqualityModel.depth (records.flatMap Record.paths)
  cases left with
  | nil =>
      cases right with
      | nil => exact (different rfl).elim
      | cons index rest => simp only [List.length_cons] at rightBound; omega
  | cons index rest => simp only [List.length_cons] at leftBound; omega

/-- The literal source descent lowers maximum path length on every nonempty ready payload. -/
theorem records_lt (records : List Record) (nonempty : records ≠ [])
    (wellFormed : SourceEqualityDescend.WellFormed (some records)) (index : Nat) :
    EqualityModel.depth ((SourceEqualityDescend.records index records).flatMap Record.paths) <
      EqualityModel.depth (records.flatMap Record.paths) := by
  have grows := positive 0 records nonempty wellFormed
  change 0 < EqualityModel.depth (records.flatMap Record.paths) at grows
  have bounded : EqualityModel.depth ((SourceEqualityDescend.records index records).flatMap Record.paths) ≤
      EqualityModel.depth (records.flatMap Record.paths) - 1 := by
    apply (EqualityModel.maxOn_le List.length _ _).mpr
    intro suffix member
    obtain ⟨output, outputMember, suffixMember⟩ := List.mem_flatMap.mp member
    obtain ⟨original, originalMember, actual⟩ := List.mem_filterMap.mp
      ((SourceEqualityDescend.records_perm index records).mem_iff.mp outputMember)
    have parentMember := (SourceEqualityDescend.record_pairs index original
      (wellFormed records rfl original originalMember).1 output actual suffix).mp suffixMember
    have parentBound := path_le records original originalMember (index :: suffix) parentMember
    simp only [List.length_cons] at parentBound
    omega
  omega

private theorem descend_payload_height (input : Value) (index : Nat) (state : Operations)
    (valid : SourceEqualityConstraintMemoAllocation.Valid state)
    (ready : Ready state.constraints input) :
    pathHeight (SourceEqualityConstraintMemoAllocation.descend input index state).1 =
      match SourceEqualityDescend.descend input.payload index with
      | none => 0
      | some records => EqualityModel.depth (records.flatMap Record.paths) := by
  have exactPayload := (SourceEqualityConstraintMemoAllocation.descend_correct input index state valid ready).2.2.1
  have measured := congrArg
    (fun payload => match payload with | none => 0 | some records => EqualityModel.depth (records.flatMap Record.paths))
    exactPayload
  cases result : (SourceEqualityConstraintMemoAllocation.descend input index state).1 with
  | contradiction => simpa only [result, Value.payload, pathHeight] using measured
  | live identity records => simpa only [result, Value.payload, pathHeight] using measured

/-- Actual cold or warm descent strictly lowers the ready input's complete path height. -/
theorem descend_lt (identity : Nat) (records : List Record) (index : Nat) (state : Operations)
    (valid : SourceEqualityConstraintMemoAllocation.Valid state)
    (ready : Ready state.constraints (.live identity records)) (nonempty : records ≠ []) :
    pathHeight (SourceEqualityConstraintMemoAllocation.descend (.live identity records) index state).1 <
      pathHeight (.live identity records) := by
  rw [descend_payload_height _ index state valid ready]
  cases records with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest =>
      exact records_lt (first :: rest) nonempty ready.2 index

/-- Canonical identity cannot be reused by actual descent of a nonempty ready payload. -/
theorem descend_identity_ne (identity : Nat) (records : List Record) (index : Nat) (state : Operations)
    (valid : SourceEqualityConstraintMemoAllocation.Valid state)
    (ready : Ready state.constraints (.live identity records)) (nonempty : records ≠ []) :
    (SourceEqualityConstraintMemoAllocation.descend (.live identity records) index state).1.identity ≠
      (.live identity records : Value).identity := by
  intro same
  have checked := SourceEqualityConstraintMemoAllocation.descend_correct (.live identity records) index state valid ready
  have inputReady := ready.grows checked.2.2.2.constraint_growth
  have values := SourceEqualityConstraintMemoAllocation.ready_eq_of_identity _ checked.1.constraints
    _ _ checked.2.1 inputReady same
  have strict := descend_lt identity records index state valid ready nonempty
  rw [values] at strict
  omega

/-- Immediate inherited descent separates even two requests with the same complete node value. -/
theorem node_key_ne (identity : Nat) (records : List Record) (index : Nat) (state : Operations)
    (valid : SourceEqualityConstraintMemoAllocation.Valid state)
    (ready : Ready state.constraints (.live identity records)) (nonempty : records ≠ [])
    (value : InternedConstructorTemplates.Value (SourceObservations.Label FullSyntax.Formula)
      (SourceSymbolicIndex.Constraint FullSyntax.Formula)) :
    (SourceCurrentAllocatedPartialState.NodeRequest.mk
      (SourceEqualityConstraintMemoAllocation.descend (.live identity records) index state).1 value).key ≠
      (SourceCurrentAllocatedPartialState.NodeRequest.mk (.live identity records) value).key := by
  intro same
  exact descend_identity_ne identity records index state valid ready nonempty (congrArg Prod.fst same)

end MicroCFTA.SourceCurrentOuterInheritedDescent
