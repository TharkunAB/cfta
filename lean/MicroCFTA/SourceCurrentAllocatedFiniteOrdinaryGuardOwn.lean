import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardProfiles
import MicroCFTA.SourceCurrentAllocatedPrecheck

/-!
# Own-class limits from hereditary raw guard profiles

The actual own accessor derives its effective field from the raw constraint.
The live precheck retains only the ordered own records.
The initial guard vector bounds their count, path count, and path depth.
The inherited payload has no size premise.
These results do not bound signed child-index magnitudes or solver work.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardOwn
open EqualityNormalize SourceEqualityClassOrder
open SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope (Limits Bounds effectiveBudget)
local notation "Envelope" => SourceCurrentAllocatedFiniteOrdinaryConstraintEnvelope.Bounds
local notation "Constraint" => SourceSymbolicIndex.Constraint

/-- The effective own occurrence bound also bounds each class and the class count. -/
def classBudget (limits : Limits) : Nat := (effectiveBudget limits).1

/-- Every effective own path satisfies the depth from staged positive extraction. -/
def pathDepth (limits : Limits) : Nat := (effectiveBudget limits).2

/-- Each class contributes its path count and one final leaf query step. -/
def classSteps (records : List Record) : Nat := (records.map (fun record => record.paths.length + 1)).sum

/-- The literal class step sum is total path occurrences plus the number of classes. -/
theorem classSteps_eq (records : List Record) :
    classSteps records = (records.map Record.paths).flatten.length + records.length := by
  induction records with
  | nil => rfl
  | cons record rest ih =>
      simp only [classSteps, List.map_cons, List.sum_cons] at *
      simp only [List.flatten_cons, List.length_append, List.length_cons]
      omega

private theorem member_length {α : Type} (lists : List (List α)) (values : List α)
    (member : values ∈ lists) : values.length ≤ lists.flatten.length := by
  induction lists with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · simp only [List.flatten_cons, List.length_append]
        omega
      · have tail := ih member
        simp only [List.flatten_cons, List.length_append]
        omega

private theorem active_count (records : List Record)
    (active : ∀ record ∈ records, Nontrivial record.paths) :
    records.length ≤ (records.map Record.paths).flatten.length := by
  induction records with
  | nil => simp
  | cons record rest ih =>
      obtain ⟨path, member, _⟩ := active record List.mem_cons_self
      have positive : 0 < record.paths.length := List.length_pos_iff.mpr (List.ne_nil_of_mem member)
      have tail := ih (fun value included => active value (List.mem_cons_of_mem record included))
      simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
      omega

/-- A live actual precheck derives all own-class bounds from the initial raw vector. -/
theorem precheck (original : Constraint Formula) (limits : Limits)
    (profile : Bounds limits original) (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (own inherited : SourceEqualityPrecheck.Constraint)
    (read : SourceEqualityPhysicalPayload.own original = .ok own)
    (records : List Record)
    (done : SourceEqualityPrecheck.precheck own inherited = .ok (.classes records)) :
    Envelope (classBudget limits) (pathDepth limits) (records.map Record.paths) ∧
      records.length ≤ classBudget limits ∧
      (∀ record ∈ records, record.paths.length ≤ classBudget limits) ∧
      (∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ pathDepth limits) := by
  have physical := SourceEqualityPhysicalClassEntry.own_verified original cached own read
  have effective : SourceCurrentAllocatedFiniteOrdinaryConstraintEnvelope.PayloadBounds
      (classBudget limits) (pathDepth limits) own := by
    change SourceCurrentAllocatedFiniteOrdinaryConstraintEnvelope.OptionBounds _ _
      (SourceEqualityInheritedPayload.classes own)
    rw [physical.2]
    exact SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.effective original limits profile
  have bounded := SourceCurrentAllocatedFiniteOrdinaryConstraintEnvelope.precheck_bounds
    own inherited (classBudget limits) (pathDepth limits) effective records done
  obtain ⟨originals, present, same, _⟩ := SourceEqualityPrecheck.live_payload own inherited records done
  have active : ∀ record ∈ records, Nontrivial record.paths := by
    intro record member
    have included : record ∈ originals := (ordered_perm originals).mem_iff.mp (same ▸ member)
    exact (physical.1 originals present record included).2.2
  refine ⟨bounded, Nat.le_trans (active_count records active) bounded.occurrences, ?_, ?_⟩
  · intro record member
    exact Nat.le_trans (member_length _ record.paths (List.mem_map.mpr ⟨record, member, rfl⟩))
      bounded.occurrences
  · intro record member path included
    exact bounded.depth record.paths (List.mem_map.mpr ⟨record, member, rfl⟩) path included

/-- Total class guard growth depends only on the initial raw own vector. -/
theorem precheck_steps (original : Constraint Formula) (limits : Limits)
    (profile : Bounds limits original) (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (own inherited : SourceEqualityPrecheck.Constraint)
    (read : SourceEqualityPhysicalPayload.own original = .ok own)
    (records : List Record)
    (done : SourceEqualityPrecheck.precheck own inherited = .ok (.classes records)) :
    classSteps records ≤ 2 * classBudget limits := by
  have bounded := precheck original limits profile cached own inherited read records done
  rw [classSteps_eq]
  have paths := bounded.1.occurrences
  have count := bounded.2.1
  omega

/-- The same allocated prefix receipt supplies its own uniform class and path bounds. -/
theorem receipt
    [DecidableEq (SourceObservations.Label FullSyntax.Formula)]
    [DecidableEq (InternedConstructorTemplates.EdgeKey (SourceObservations.Label FullSyntax.Formula)
      (Constraint FullSyntax.Formula))]
    {width : Nat} {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {original : Constraint FullSyntax.Formula}
    {loaded : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula}
    {inherited own : SourceEqualityConstraintAllocation.Value}
    {before : SourceEqualityNativeDemand.State width} {records : List Record}
    (actual : SourceCurrentAllocatedPrecheck.Receipt formulas solver inventory original loaded inherited before own (.classes records))
    (limits : Limits) (profile : Bounds limits original) :
    Envelope (classBudget limits) (pathDepth limits) (records.map Record.paths) ∧
      records.length ≤ classBudget limits ∧
      (∀ record ∈ records, record.paths.length ≤ classBudget limits) ∧
      (∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ pathDepth limits) :=
  precheck original limits profile actual.cached own.payload inherited.payload actual.ownRead records actual.exact

/-- The allocated prefix derives the total class-step bound at its exact returned records. -/
theorem receipt_steps
    [DecidableEq (SourceObservations.Label FullSyntax.Formula)]
    [DecidableEq (InternedConstructorTemplates.EdgeKey (SourceObservations.Label FullSyntax.Formula)
      (Constraint FullSyntax.Formula))]
    {width : Nat} {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {original : Constraint FullSyntax.Formula}
    {loaded : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula}
    {inherited own : SourceEqualityConstraintAllocation.Value}
    {before : SourceEqualityNativeDemand.State width} {records : List Record}
    (actual : SourceCurrentAllocatedPrecheck.Receipt formulas solver inventory original loaded inherited before own (.classes records))
    (limits : Limits) (profile : Bounds limits original) :
    classSteps records ≤ 2 * classBudget limits :=
  precheck_steps original limits profile actual.cached own.payload inherited.payload actual.ownRead records actual.exact

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardOwn
