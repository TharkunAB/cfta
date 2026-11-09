import MicroCFTA.SourceCurrentConjunctionRequirementRows
import MicroCFTA.SourceCurrentConjunctionRequirementCellsSoundness

/-!
# Smaller witnesses in original requirement descriptors

An accepted tuple supplies a common child term for every literal column.
An active satisfied equality class supplies a common proper subtree for its
initial projection cursor. These claims describe the original descriptors.
They need no heap, projection result, or future successful force.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementDescriptorsSoundness
open Language EqualityNormalize EqualityReduction
open InternedConstructorTemplates (Value EdgeValue)
open InternedGuardedLanguage (meaning)
open SourceCurrentConjunctionCompletionReads (jobs)
open SourceCurrentConjunctionRequirementPull (start)
open SourceCurrentConjunctionRequirementPullSoundness (Common)
open SourceCurrentConjunctionRequirementCellsSoundness (CommonCell)
open SourceCurrentConjunctionEmptinessRows (Accepts)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard

/-- The original class cursor has one strictly smaller common accepted subtree. -/
theorem start_common (forests : List (List Node)) (paths : Class) (nonempty : forests ≠ [])
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (symbol : Symbol) (terms : List (Term Symbol))
    (original : ∀ forest ∈ forests, All₂ (meaning holds ambient) forest terms)
    (active : Nontrivial paths) (satisfied : ClassSat (.node symbol terms) paths) :
    ∃ part, Common holds ambient symbol terms part (start forests paths) ∧
      part.height < (Term.node symbol terms).height := by
  obtain ⟨first, firstIn, second, secondIn, different⟩ := active
  have active : Nontrivial paths := ⟨first, firstIn, second, secondIn, different⟩
  obtain ⟨part, found⟩ := class_member_exists (.node symbol terms) paths active satisfied first firstIn
  have proper := class_nonroot paths active (.node symbol terms) satisfied
  have jobNonempty : jobs forests paths ≠ [] := by
    cases forests with
    | nil => exact False.elim (nonempty rfl)
    | cons forest rest =>
        have member : (forest, first) ∈ jobs (forest :: rest) paths :=
          List.mem_flatMap.mpr ⟨forest, List.mem_cons_self, List.mem_map.mpr ⟨first, firstIn, rfl⟩⟩
        intro empty
        simp only [empty, List.not_mem_nil] at member
  refine ⟨part, ?_, ?_⟩
  · refine ⟨Or.inr jobNonempty, ?_, ?_⟩
    · intro value member
      cases member
    · intro job member
      obtain ⟨forest, forestIn, pathIn⟩ := List.mem_flatMap.mp member
      obtain ⟨path, actualPathIn, rfl⟩ := List.mem_map.mp pathIn
      refine ⟨original forest forestIn, proper path actualPathIn, ?_⟩
      obtain ⟨common, firstFound, pathFound⟩ := class_pair_equal (.node symbol terms) paths active
        satisfied first path firstIn actualPathIn
      have same := Option.some.inj (firstFound.symm.trans found)
      simpa only [same] using pathFound
  · have bound := atPath_height_bound (.node symbol terms) part first found
    have positive : 0 < first.length := by
      cases first with
      | nil => exact False.elim (proper [] firstIn rfl)
      | cons => simp
    omega

/-- Every literal column or class descriptor has a strictly smaller accepted common term. -/
theorem descriptors_witness (tuple : List Row) (constraints : Constraints) (nonempty : tuple ≠ [])
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (symbol : Symbol) (terms : List (Term Symbol))
    (original : ∀ edge ∈ tuple, All₂ (meaning holds ambient) edge.children terms)
    (active : Active constraints) (satisfied : Satisfies (.node symbol terms) constraints) :
    ∀ cell ∈ SourceCurrentConjunctionRequirementRows.descriptors tuple constraints,
      ∃ part, CommonCell holds ambient symbol terms part cell ∧
        part.height < (Term.node symbol terms).height := by
  have forests : ∀ forest ∈ tuple.map EdgeValue.children, All₂ (meaning holds ambient) forest terms := by
    intro forest member
    obtain ⟨edge, edgeIn, rfl⟩ := List.mem_map.mp member
    exact original edge edgeIn
  have forestsNonempty : tuple.map EdgeValue.children ≠ [] := by simpa using nonempty
  have commonArity : SourceCurrentConjunctionRequirements.arity tuple = terms.length := by
    cases tuple with
    | nil => exact False.elim (nonempty rfl)
    | cons edge rest => exact (original edge List.mem_cons_self).length_eq
  intro cell member
  change cell ∈ (SourceCurrentConjunctionRequirements.columns tuple).map _ ++ constraints.map _ at member
  rcases List.mem_append.mp member with column | group
  · obtain ⟨nodes, columnIn, rfl⟩ := List.mem_map.mp column
    have acceptedColumns := SourceCurrentConjunctionEmptinessRows.columns_accept
      (meaning holds ambient) (tuple.map EdgeValue.children) forestsNonempty terms forests
    have columnIn' : nodes ∈ MergedAlternativesGroups.columns (tuple.map EdgeValue.children) terms.length := by
      simpa only [SourceCurrentConjunctionRequirements.columns, commonArity] using columnIn
    obtain ⟨part, partIn, accepted⟩ := SymbolicSmartRows.all₂_child (Accepts (meaning holds ambient)) _ terms
      acceptedColumns nodes columnIn'
    refine ⟨part, accepted, ?_⟩
    have bound := height_le_forestHeight terms part partIn
    simpa only [Term.height, forestHeight] using Nat.lt_succ_of_le bound
  · obtain ⟨paths, pathsIn, rfl⟩ := List.mem_map.mp group
    exact start_common (tuple.map EdgeValue.children) paths forestsNonempty holds ambient symbol terms
      forests (active paths pathsIn) (satisfied paths pathsIn)

end MicroCFTA.SourceCurrentConjunctionRequirementDescriptorsSoundness
