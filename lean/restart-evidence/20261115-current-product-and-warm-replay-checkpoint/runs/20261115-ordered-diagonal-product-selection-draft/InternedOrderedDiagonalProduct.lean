import MicroCFTA.SourceRecursiveIntersectionKernelCalls
import MicroCFTA.InternedNodeSetCongruence
import MicroCFTA.BinderSchedule

/-!
# Ordered diagonal selection from a complete row product

Every source row has its diagonal occurrence in the literal product.
The ordered raw results supply a related diagonal target for each source.
Non-diagonal rows with an empty child do not survive.
Scoped functionality identifies the surviving targets with the selected list.
-/
namespace MicroCFTA.InternedOrderedDiagonalProduct
open Language InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open SourceRecursiveIntersectionKernel (pairs pairs_member)
variable {Symbol Guard : Type}

set_option autoImplicit false

private theorem select_in_source_order
    (relation : EdgeValue Symbol Guard → EdgeValue Symbol Guard → Prop)
    (sources rawResults : List (EdgeValue Symbol Guard))
    (available : ∀ source ∈ sources, ∃ target ∈ rawResults, relation source target) :
    ∃ selected, All₂ relation sources selected ∧ ∀ target ∈ selected, target ∈ rawResults := by
  revert available
  induction sources with
  | nil => intro _; exact ⟨[], .nil, by intro target member; cases member⟩
  | cons source sources ih =>
      intro available
      obtain ⟨target, targetIn, related⟩ := available source List.mem_cons_self
      have tailAvailable : ∀ later ∈ sources, ∃ target ∈ rawResults, relation later target := by
        intro later member
        exact available later (List.mem_cons_of_mem _ member)
      obtain ⟨selected, aligned, retained⟩ := ih tailAvailable
      refine ⟨target :: selected, .cons related aligned, ?_⟩
      intro row member
      rcases List.mem_cons.mp member with rfl | tail
      · exact targetIn
      · exact retained row tail

/-- Complete paired rows derive an ordered selection with the same canonical surviving product. -/
theorem ordered_diagonal_selection
    [DecidableEq Symbol]
    (heap : State Symbol Guard) (facts : Facts heap)
    (sources rawResults : List (EdgeValue Symbol Guard))
    (relation : EdgeValue Symbol Guard → EdgeValue Symbol Guard → Prop)
    (resident : ∀ row ∈ rawResults, EdgeResident heap row)
    (actual : All₂ (fun (pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard) (row : EdgeValue Symbol Guard) =>
      (pair.1 = pair.2 → relation pair.1 row) ∧
      (pair.1 ≠ pair.2 → row.children = [.empty])) (pairs sources sources) rawResults)
    (functional : ∀ source ∈ sources, ∀ first ∈ rawResults, ∀ second ∈ rawResults,
      relation source first → relation source second → first = second)
    (live : ∀ source ∈ sources, ∀ target ∈ rawResults,
      relation source target → target ∈ surviving rawResults) :
    ∃ selected,
      All₂ relation sources selected ∧
      (∀ target ∈ selected, target ∈ rawResults) ∧
      (∀ target ∈ selected, EdgeResident heap target) ∧
      (∀ row, row ∈ surviving rawResults ↔ row ∈ selected) ∧
      canonicalEdges (surviving rawResults) = canonicalEdges selected := by
  classical
  have diagonals : ∀ source ∈ sources, ∃ target ∈ rawResults, relation source target := by
    intro source member
    have diagonal : (source, source) ∈ pairs sources sources :=
      (pairs_member sources sources (source, source)).mpr ⟨member, member, rfl⟩
    obtain ⟨target, targetIn, rowLaw⟩ := BinderSchedule.related_target _ actual (source, source) diagonal
    exact ⟨target, targetIn, rowLaw.1 rfl⟩
  obtain ⟨selected, aligned, selectedRaw⟩ := select_in_source_order relation sources rawResults diagonals
  have selectedResident : ∀ target ∈ selected, EdgeResident heap target :=
    fun target member => resident target (selectedRaw target member)
  have same : ∀ row, row ∈ surviving rawResults ↔ row ∈ selected := by
    intro row
    constructor
    · intro present
      have raw : row ∈ rawResults := (List.mem_filter.mp present).1
      obtain ⟨pair, pairIn, rowLaw⟩ := BinderSchedule.related_origin _ actual row raw
      have self : pair.1 = pair.2 := by
        by_contra different
        have empty := rowLaw.2 different
        have survives := (List.mem_filter.mp present).2
        simp [empty, Value.referenceOf] at survives
      have sourceIn : pair.1 ∈ sources := ((pairs_member sources sources pair).mp pairIn).1
      have related := rowLaw.1 self
      obtain ⟨target, targetIn, targetRelated⟩ :=
        BinderSchedule.related_target relation aligned pair.1 sourceIn
      have equal := functional pair.1 sourceIn row raw target (selectedRaw target targetIn) related targetRelated
      rw [equal]
      exact targetIn
    · intro present
      obtain ⟨source, sourceIn, related⟩ := BinderSchedule.related_origin relation aligned row present
      exact live source sourceIn row (selectedRaw row present) related
  have canonical : canonicalEdges (surviving rawResults) = canonicalEdges selected := by
    apply InternedNodeSetCongruence.canonical_same heap facts.coherent _ _
      (fun row member => resident row (List.mem_filter.mp member).1) selectedResident
    intro identity
    simp only [List.mem_map]
    constructor <;> rintro ⟨row, member, equal⟩
    · exact ⟨row, (same row).mp member, equal⟩
    · exact ⟨row, (same row).mpr member, equal⟩
  exact ⟨selected, aligned, selectedRaw, selectedResident, same, canonical⟩

end MicroCFTA.InternedOrderedDiagonalProduct
