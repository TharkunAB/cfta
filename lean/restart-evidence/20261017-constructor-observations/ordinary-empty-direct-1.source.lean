import MicroCFTA.SourceCurrentStoredOrdinaryUnionObservations

/-!
# Physical Empty agreement for ordinary observations

A resident ordinary node in a normal heap has an outgoing row. Therefore
one row depth detects physical Empty among available ordinary roots.
Mu roots do not satisfy this statement. Actual warm ordinary union calls
derive their output availability before the observation lemma is applied.
-/
namespace MicroCFTA.SourceCurrentOrdinaryObservationEmpty
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedNestedConstruction (Outcome)
open InternedStoredMuOrigins (Normal)
open SourceEqualityRequiredCache (Ready)
open SourceCurrentOpenObservations (Same)
open MergedFreshOrdinaryGraph (Origin)
open InternedStoredSubstitution (Environment Replacements leaves input encode)
open InternedFreshOrdinaryStoredSubstitution (execute)
open Language

/-- An available ordinary root is physically Empty exactly when it has no exposed row. -/
theorem ordinary_empty_iff_no_origins [DecidableEq (EdgeKey Symbol Guard)]
    (common view : State Symbol Guard) (normal : Normal common) (value : Value Symbol Guard)
    (ordinary : SourceEqualityRequiredCache.Ordinary value) (available : Available common value) :
    value.referenceOf = .empty ↔ ∀ row, ¬ Origin view [value] row := by
  cases value with
  | empty => exact ⟨fun _ row => MergedFreshOrdinaryGraph.origin_empty view row, fun _ => rfl⟩
  | node entry rows level free =>
      constructor
      · intro impossible
        cases impossible
      · intro absent
        have nonempty := InternedNonemptyRecords.resident_nonempty common normal.proper _ available.resident
        cases rows with
        | nil => exact False.elim (nonempty rfl)
        | cons row rest =>
            exact False.elim (absent row
              ((MergedFreshOrdinaryGraph.origin_node view entry _ level free row).mpr List.mem_cons_self))
  | reference | union | mu => cases ordinary

/-- One full row observation detects Empty for ordinary roots and ordinary seed lists. -/
theorem ordinary_empty_iff [DecidableEq (EdgeKey Symbol Guard)]
    (common view : State Symbol Guard) (normal : Normal common)
    (result : Value Symbol Guard) (outputs : List (Value Symbol Guard))
    (resultOrdinary : SourceEqualityRequiredCache.Ordinary result)
    (outputsOrdinary : ∀ output ∈ outputs, SourceEqualityRequiredCache.Ordinary output)
    (resultAvailable : Available common result) (outputsAvailable : Values common outputs)
    (observed : Same 1 view [result] outputs) :
    result.referenceOf = .empty ↔ ∀ output ∈ outputs, output.referenceOf = .empty := by
  constructor
  · intro empty output member
    apply (ordinary_empty_iff_no_origins common view normal output
      (outputsOrdinary output member) (outputsAvailable output member)).mpr
    intro row origin
    have seeded := (MergedFreshOrdinaryGraph.origin_seeds view outputs row).mpr ⟨output, member, origin⟩
    obtain ⟨other, returned, _⟩ := observed.2.2 row seeded
    exact (ordinary_empty_iff_no_origins common view normal result resultOrdinary resultAvailable).mp empty other returned
  · intro allEmpty
    apply (ordinary_empty_iff_no_origins common view normal result resultOrdinary resultAvailable).mpr
    intro row origin
    obtain ⟨other, returned, _⟩ := observed.2.1 row origin
    obtain ⟨output, member, selected⟩ := (MergedFreshOrdinaryGraph.origin_seeds view outputs other).mp returned
    exact (ordinary_empty_iff_no_origins common view normal output
      (outputsOrdinary output member) (outputsAvailable output member)).mp (allEmpty output member) other selected

private theorem pair_right {α β : Type} {relation : α → β → Prop} {first : List α} {second : List β}
    (paired : All₂ relation first second) (value : β) (member : value ∈ second) :
    ∃ original ∈ first, relation original value := by
  induction paired with
  | nil => cases member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨_, List.mem_cons_self, head⟩
      · obtain ⟨original, included, matched⟩ := ih later
        exact ⟨original, List.mem_cons_of_mem _ included, matched⟩

private theorem execute_available [DecidableEq (EdgeKey Symbol Guard)]
    (value output : Value Symbol Guard) (environment : Environment Symbol Guard) (common : State Symbol Guard)
    (normal : Normal common) (available : Available common value) (replacements : Replacements common environment)
    (actual : execute value environment common = .done output common) : Available common output :=
  (InternedFreshOrdinaryFacts.build_verified (encode (leaves value) [] value) ((leaves value).map (input environment))
    common normal.facts (InternedStoredSubstitution.inputs_available value environment common available replacements)).result
    output common actual

private theorem execute_ordinary [DecidableEq (EdgeKey Symbol Guard)]
    (value output : Value Symbol Guard) (environment : Environment Symbol Guard) (common : State Symbol Guard)
    (normal : Normal common) (available : Available common value) (replacements : Replacements common environment)
    (ordinary : SourceEqualityRequiredCache.Ordinary value)
    (actual : execute value environment common = .done output common) : SourceEqualityRequiredCache.Ordinary output := by
  cases value with
  | empty =>
      have same := (Outcome.done.inj
        ((SourceCurrentStoredUnionObservations.closed (.empty : Value Symbol Guard) environment common rfl).symm.trans actual)).1
      subst output
      trivial
  | node entry rows level free =>
      obtain ⟨_, _, plain, _⟩ := SourceCurrentStoredNodeExpansion.node_warm entry rows level free
        environment common normal available replacements output actual
      exact plain
  | reference | union | mu => cases ordinary

private theorem union_ordinary [DecidableEq (EdgeKey Symbol Guard)]
    (originals : List (Value Symbol Guard)) (common : State Symbol Guard) (ready : Ready common)
    (available : Values common originals) (ordinary : ∀ value ∈ originals, SourceEqualityRequiredCache.Ordinary value) :
    SourceEqualityRequiredCache.Ordinary (run (makeUnion originals) common).1 := by
  have nodes : ∀ value ∈ distinctNodes (originals.flatMap unionMembers), EqualityLeafProjectionUnion.NodeRoot value := by
    intro value member
    obtain ⟨source, included, inner⟩ := List.mem_flatMap.mp (distinctNodes_member _ value member)
    have plain := ordinary source included
    cases source <;> simp_all [SourceEqualityRequiredCache.Ordinary, unionMembers,
      EqualityLeafProjectionUnion.NodeRoot]
  cases shape : distinctNodes (originals.flatMap unionMembers) with
  | nil => simp only [makeUnion, shape, run, SourceEqualityRequiredCache.Ordinary]
  | cons first rest =>
      cases rest with
      | nil =>
          have firstNode := nodes first (by simp only [shape, List.mem_singleton])
          cases first <;> simp_all [makeUnion, SourceEqualityRequiredCache.Ordinary,
            EqualityLeafProjectionUnion.NodeRoot, run]
      | cons second tail =>
          have extracted := EqualityLeafProjectionUnion.ordinary_edges (first :: second :: tail)
            (by intro value member; exact nodes value (by rw [shape]; exact member))
          have resident := ordinaryEdges_resident (first :: second :: tail) _ common ready.semantic.1.normal.facts.linked
            (fun value member => (InternedUnionFilterFusion.selected_available originals common available value
              (by rw [shape]; exact member)).resident) extracted
          have output := SourceEqualityRequiredCache.node_ordinary _ common ready.semantic.1.normal.facts resident
          simpa only [makeUnion, shape, extracted] using output

/-- Actual warm ordinary union calls agree on physical Empty without supplied output availability. -/
theorem warm_union_empty [DecidableEq (EdgeKey Symbol Guard)]
    {originals outputs : List (Value Symbol Guard)} {environment : Environment Symbol Guard}
    {common : State Symbol Guard} {normalized result : Value Symbol Guard}
    (ready : Ready common) (available : Values common originals) (replacements : Replacements common environment)
    (ordinary : ∀ value ∈ originals, SourceEqualityRequiredCache.Ordinary value)
    (paired : All₂ (fun original output => execute original environment common = .done output common) originals outputs)
    (made : run (makeUnion originals) common = (normalized, common))
    (called : execute normalized environment common = .done result common) :
    result.referenceOf = .empty ↔ ∀ output ∈ outputs, output.referenceOf = .empty := by
  have observed := SourceCurrentStoredOrdinaryUnionObservations.warm ready available replacements ordinary paired made called
  have resultAvailable := execute_available normalized result environment common ready.semantic.1.normal
    ((InternedNestedFacts.union_verified originals common ready.semantic.1.normal.facts available).result
      normalized common (by simp only [InternedNestedConstruction.work, made])) replacements called
  have outputsAvailable : Values common outputs := by
    intro output member
    obtain ⟨original, included, actual⟩ := pair_right paired output member
    exact execute_available original output environment common ready.semantic.1.normal (available original included) replacements actual
  have outputsOrdinary : ∀ output ∈ outputs, SourceEqualityRequiredCache.Ordinary output := by
    intro output member
    obtain ⟨original, included, actual⟩ := pair_right paired output member
    exact execute_ordinary original output environment common ready.semantic.1.normal (available original included)
      replacements (ordinary original included) actual
  have normalizedOrdinary : SourceEqualityRequiredCache.Ordinary normalized := by
    simpa only [made] using union_ordinary originals common ready available ordinary
  have resultOrdinary := execute_ordinary normalized result environment common ready.semantic.1.normal
    ((InternedNestedFacts.union_verified originals common ready.semantic.1.normal.facts available).result
      normalized common (by simp only [InternedNestedConstruction.work, made])) replacements normalizedOrdinary called
  exact ordinary_empty_iff common common ready.semantic.1.normal result outputs resultOrdinary outputsOrdinary
    resultAvailable outputsAvailable (observed 1 common)

end MicroCFTA.SourceCurrentOrdinaryObservationEmpty
