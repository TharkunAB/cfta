import MicroCFTA.SourceCurrentConstrainedCapClassForecast
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

namespace MicroCFTA.ClassForecastKernels
open SourceCurrentAllocatedNativeResourceForecast (Profile Le Room)
open SourceCurrentConstrainedCapClassForecast
open SourceCurrentAllocatedClassEditPlan (compiled)
private theorem power_large (n : Nat) : n < 2 ^ (n + 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Nat.add_assoc, Nat.pow_succ]
      omega

private theorem exists_room (p : SourceCurrentAllocatedNativeResourceForecast.Profile) :
    ∃ bits, SourceCurrentAllocatedNativeResourceForecast.Room bits p := by
  let total := p.nodes + p.edges + p.domains + 2 ^ (p.nodes + p.nodes * p.nodes)
  refine ⟨total + 1, ?_⟩
  have large := power_large total
  have one := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show total + 1 ≤ total + 1 + 1 by omega)
  have two := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show total + 1 ≤ total + 1 + 2 by omega)
  change p.nodes < 2 ^ (total + 1) ∧ p.edges ≤ 2 ^ (total + 1 + 2) ∧
    p.domains + 2 ^ (p.nodes + p.nodes * p.nodes) < 2 ^ (total + 1 + 1)
  have nodes : p.nodes ≤ total := by
    exact Nat.le_trans (Nat.le_trans (Nat.le_add_right p.nodes p.edges)
      (Nat.le_add_right (p.nodes + p.edges) p.domains))
      (Nat.le_add_right (p.nodes + p.edges + p.domains) _)
  have edges : p.edges ≤ total := by
    exact Nat.le_trans (Nat.le_trans (Nat.le_add_left p.edges p.nodes)
      (Nat.le_add_right (p.nodes + p.edges) p.domains))
      (Nat.le_add_right (p.nodes + p.edges + p.domains) _)
  have domains : p.domains + 2 ^ (p.nodes + p.nodes * p.nodes) ≤ total :=
    Nat.add_le_add_right (Nat.le_add_left p.domains (p.nodes + p.edges)) _
  exact ⟨Nat.lt_of_le_of_lt nodes large,
    Nat.le_trans edges (Nat.le_trans (Nat.le_of_lt large) two),
    Nat.lt_of_le_of_lt domains (Nat.lt_of_lt_of_le large one)⟩

private def record : SourceEqualityClassOrder.Record :=
  match SourceEqualityClassOrder.recordOf [[0, 0], [0, 1]] with
  | some value => value
  | none => ⟨.empty, []⟩
private theorem record_built : SourceEqualityClassOrder.recordOf [[0, 0], [0, 1]] = some record := by cbv
private theorem record_paths : record.paths = [[0, 0], [0, 1]] := by cbv
private theorem record_coherent : SourceEqualityClassOrder.Coherent record := by
  obtain ⟨actual, done, coherent, _paths⟩ :=
    SourceEqualityClassOrder.recordOf_complete [[0, 0], [0, 1]]
      ((EqualityTrie.toPathTrie_succeeds_iff _).mp ⟨.branch [(0, .branch [(0, .terminal), (1, .terminal)])], by cbv⟩)
  have same : actual = record := Option.some.inj (done.symm.trans record_built)
  exact same ▸ coherent
private theorem record_active : EqualityNormalize.Nontrivial record.paths := by
  rw [record_paths]
  exact ⟨[0, 0], by simp, [0, 1], by simp, by decide⟩

/-- Two literal classes share one initial room and retain the tail-return head entry. -/
theorem constructed_two_class_schedule (profile : Profile) :
    ∃ actual bits, SourceEqualityClassOrder.recordOf [[0, 0], [0, 1]] = some actual ∧
      SourceEqualityClassOrder.Coherent actual ∧ EqualityNormalize.Nontrivial actual.paths ∧
      Reserved bits [actual, actual] 1 profile ∧
      SourceCurrentConstrainedCapEditListNumeric.Reserved bits actual 1 (compiled actual) 1 profile ∧
      SourceCurrentConstrainedCapEditListNumeric.Reserved bits actual 1 (compiled actual) 1
        (classProfile actual 1 profile) ∧
      classFuel actual 1 profile ≤ foldFuel [actual, actual] 1 profile ∧
      classFuel actual 1 (classProfile actual 1 profile) ≤ foldFuel [actual, actual] 1 profile := by
  obtain ⟨bits, room⟩ := exists_room (foldProfile [record, record] 1 profile)
  have reserved : Reserved bits [record, record] 1 profile := room
  refine ⟨record, bits, record_built, record_coherent, record_active, reserved, ?_, ?_, ?_, ?_⟩
  · exact reserved_class bits record [] 1 profile (reserved_tail bits record [record] 1 profile reserved)
  · exact reserved_class bits record [record] 1 profile reserved
  · exact Nat.le_trans (foldFuel_head record [] 1 profile) (foldFuel_tail record [record] 1 profile)
  · exact foldFuel_head record [record] 1 profile

/-- An appended schedule reserves each phase at its literal preceding profile. -/
theorem constructed_append_schedule (first last : List SourceEqualityClassOrder.Record) (count : Nat)
    (profile : Profile) :
    ∃ bits, Reserved bits (first ++ last) count profile ∧
      Reserved bits last count profile ∧ Reserved bits first count (foldProfile last count profile) ∧
      foldProfile (first ++ last) count profile = foldProfile first count (foldProfile last count profile) ∧
      foldFuel (first ++ last) count profile =
        max (foldFuel last count profile) (foldFuel first count (foldProfile last count profile)) := by
  obtain ⟨bits, room⟩ := exists_room (foldProfile (first ++ last) count profile)
  have roomFirst : Room bits (foldProfile first count (foldProfile last count profile)) := by
    rw [foldProfile_append] at room
    exact room
  have roomLast := roomFirst.mono (fold_ge first count (foldProfile last count profile))
  refine ⟨bits, ?_, ?_, ?_, foldProfile_append first last count profile, foldFuel_append first last count profile⟩
  · cases first ++ last with
    | nil => trivial
    | cons record records => exact room
  · cases last with
    | nil => trivial
    | cons record records => exact roomLast
  · cases first with
    | nil => trivial
    | cons record records => exact roomFirst

end MicroCFTA.ClassForecastKernels

#print axioms MicroCFTA.ClassForecastKernels.constructed_two_class_schedule
#check @MicroCFTA.ClassForecastKernels.constructed_two_class_schedule
#print MicroCFTA.ClassForecastKernels.constructed_two_class_schedule
#print axioms MicroCFTA.ClassForecastKernels.constructed_append_schedule
#check @MicroCFTA.ClassForecastKernels.constructed_append_schedule
#print MicroCFTA.ClassForecastKernels.constructed_append_schedule
