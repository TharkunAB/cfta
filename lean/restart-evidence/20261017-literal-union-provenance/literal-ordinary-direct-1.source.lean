import MicroCFTA.SourceCurrentLiteralRootParts
import MicroCFTA.SourceCurrentStoredNodeExpansion
import MicroCFTA.SourceCurrentStoredCallsReplay
import MicroCFTA.SourceCurrentStoredUnionObservations

/-!
# Exact literal parts of ordinary union reconstruction

Actual warm child calls determine exact rebuilt rows. Ordinary union
normalization and reconstruction retain the same rows. Mu children remain
inside each complete row. No root Mu body is unfolded by these predicates.
-/
namespace MicroCFTA.SourceCurrentLiteralOrdinaryParts
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Outcome)
open InternedNestedProvenance (Values)
open InternedStoredSubstitution (Environment Replacements)
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceEqualityRequiredCache (Ready)
open SourceCurrentStoredNodeExpansion (Expansion RowCalls)
open SourceCurrentLiteralRootParts (Literal Row)
open MergedFreshOrdinaryGraph (Origin)
open Language

private theorem pair_left {α β : Type} {relation : α → β → Prop} {first : List α} {second : List β}
    (paired : All₂ relation first second) (value : α) (member : value ∈ first) :
    ∃ output ∈ second, relation value output := by
  induction paired with
  | nil => cases member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨_, List.mem_cons_self, head⟩
      · obtain ⟨output, included, matched⟩ := ih later
        exact ⟨output, List.mem_cons_of_mem _ included, matched⟩

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

private theorem row_unique [DecidableEq (EdgeKey Symbol Guard)]
    {environment : Environment Symbol Guard} {common : State Symbol Guard}
    {original first second : EdgeValue Symbol Guard} (valid : Valid common)
    (left : RowCalls environment common original first) (right : RowCalls environment common original second) :
    first = second := by
  have children := SourceCurrentStoredCallsReplay.same left.1 right.1 common valid valid
    (grows_refl _) (grows_refl _)
  have made := left.2.1
  rw [children] at made
  exact congrArg Prod.fst (made.symm.trans right.2.1)

private theorem ordinary_origins [DecidableEq (EdgeKey Symbol Guard)]
    (value : Value Symbol Guard) (ordinary : SourceEqualityRequiredCache.Ordinary value)
    (view : State Symbol Guard) (row : EdgeValue Symbol Guard) :
    Origin view [value] row ↔ row ∈ nodeEdges value := by
  cases value with
  | empty => exact iff_of_false (MergedFreshOrdinaryGraph.origin_empty view row) List.not_mem_nil
  | node entry rows level free => exact MergedFreshOrdinaryGraph.origin_node view entry rows level free row
  | reference | union | mu => cases ordinary

private theorem ordinary_literal (value atom : Value Symbol Guard)
    (ordinary : SourceEqualityRequiredCache.Ordinary value) : ¬ Literal value atom := by
  cases value <;> try cases ordinary
  all_goals intro impossible; cases impossible

private theorem ordinary_row [DecidableEq (EdgeKey Symbol Guard)]
    (value : Value Symbol Guard) (ordinary : SourceEqualityRequiredCache.Ordinary value)
    (view : State Symbol Guard) (row : EdgeValue Symbol Guard) :
    Row value row ↔ Origin view [value] row := by
  rw [ordinary_origins value ordinary view row]
  cases value with
  | empty =>
      constructor
      · intro impossible; cases impossible
      · intro impossible; cases impossible
  | node entry rows level free => exact SourceCurrentLiteralRootParts.row_node entry rows level free row
  | reference | union | mu => cases ordinary

private theorem ordinary_expansion [DecidableEq (EdgeKey Symbol Guard)]
    (value output : Value Symbol Guard) (environment : Environment Symbol Guard) (common : State Symbol Guard)
    (ready : Ready common) (available : Available common value) (replacements : Replacements common environment)
    (ordinary : SourceEqualityRequiredCache.Ordinary value)
    (actual : execute value environment common = .done output common) :
    Expansion environment (nodeEdges value) common output := by
  cases value with
  | empty =>
      have done := SourceCurrentStoredUnionObservations.closed (.empty : Value Symbol Guard) environment common rfl
      have same := (Outcome.done.inj (done.symm.trans actual)).1
      subst output
      refine ⟨[], .nil, trivial, ?_⟩
      intro view row
      exact iff_of_false (MergedFreshOrdinaryGraph.origin_empty view row) List.not_mem_nil
  | node entry rows level free =>
      exact SourceCurrentStoredNodeExpansion.node_warm entry rows level free environment common
        ready.semantic.1.normal available replacements output actual
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

/-- Actual ordinary union reconstruction retains exact rows and has no literal root atoms. -/
theorem warm [DecidableEq (EdgeKey Symbol Guard)]
    {originals outputs : List (Value Symbol Guard)} {environment : Environment Symbol Guard}
    {common : State Symbol Guard} {normalized result : Value Symbol Guard}
    (ready : Ready common) (available : Values common originals) (replacements : Replacements common environment)
    (ordinary : ∀ value ∈ originals, SourceEqualityRequiredCache.Ordinary value)
    (paired : All₂ (fun original output => execute original environment common = .done output common) originals outputs)
    (made : run (makeUnion originals) common = (normalized, common))
    (called : execute normalized environment common = .done result common) :
    (∀ atom, Literal result atom ↔ ∃ output ∈ outputs, Literal output atom) ∧
      ∀ row, Row result row ↔ ∃ output ∈ outputs, Row output row := by
  have normalizedAvailable := (InternedNestedFacts.union_verified originals common ready.semantic.1.normal.facts available).result
    normalized common (by simp only [InternedNestedConstruction.work, made])
  have normalizedOrdinary : SourceEqualityRequiredCache.Ordinary normalized := by
    simpa only [made] using union_ordinary originals common ready available ordinary
  obtain ⟨rebuilt, normalizedRows, resultOrdinary, resultOrigins⟩ :=
    ordinary_expansion normalized result environment common ready normalizedAvailable replacements normalizedOrdinary called
  have expanded (value output : Value Symbol Guard) (member : value ∈ originals)
      (actual : execute value environment common = .done output common) :
      Expansion environment (nodeEdges value) common output :=
    ordinary_expansion value output environment common ready (available value member) replacements (ordinary value member) actual
  have sourceRows (row : EdgeValue Symbol Guard) :
      row ∈ nodeEdges normalized ↔ ∃ value ∈ originals, row ∈ nodeEdges value := by
    have origins := MergedFreshOrdinaryUnionOrigins.union_origins common common ready.semantic.1.normal.facts
      ready.semantic.1.normal.live originals available row
    rw [made] at origins
    rw [ordinary_origins normalized normalizedOrdinary] at origins
    constructor
    · intro member
      obtain ⟨value, included, origin⟩ := origins.mp member
      exact ⟨value, included, (ordinary_origins value (ordinary value included) common row).mp origin⟩
    · rintro ⟨value, included, member⟩
      exact origins.mpr ⟨value, included, (ordinary_origins value (ordinary value included) common row).mpr member⟩
  have outputOrdinary : ∀ output ∈ outputs, SourceEqualityRequiredCache.Ordinary output := by
    intro output member
    obtain ⟨value, included, actual⟩ := pair_right paired output member
    obtain ⟨_, _, plain, _⟩ := expanded value output included actual
    exact plain
  have rows (view : State Symbol Guard) (row : EdgeValue Symbol Guard) :
      Origin view [result] row ↔ Origin view outputs row := by
    rw [MergedFreshOrdinaryGraph.origin_seeds view outputs row]
    constructor
    · intro origin
      have retained := (resultOrigins view row).mp origin
      obtain ⟨sourceRow, sourceMember, rebuiltRow⟩ := pair_right normalizedRows row (List.mem_filter.mp retained).1
      obtain ⟨value, included, sourceMember⟩ := (sourceRows sourceRow).mp sourceMember
      obtain ⟨output, outputMember, actual⟩ := pair_left paired value included
      obtain ⟨otherRows, otherPaired, _, otherOrigins⟩ := expanded value output included actual
      obtain ⟨otherRow, otherMember, rebuiltOther⟩ := pair_left otherPaired sourceRow sourceMember
      have same := row_unique ready.semantic.1.normal.facts.coherent.valid rebuiltRow rebuiltOther
      subst otherRow
      exact ⟨output, outputMember, (otherOrigins view row).mpr
        (List.mem_filter.mpr ⟨otherMember, (List.mem_filter.mp retained).2⟩)⟩
    · rintro ⟨output, outputMember, origin⟩
      obtain ⟨value, included, actual⟩ := pair_right paired output outputMember
      obtain ⟨otherRows, otherPaired, _, otherOrigins⟩ := expanded value output included actual
      have retained := (otherOrigins view row).mp origin
      obtain ⟨sourceRow, sourceMember, rebuiltRow⟩ := pair_right otherPaired row (List.mem_filter.mp retained).1
      have sourceMember := (sourceRows sourceRow).mpr ⟨value, included, sourceMember⟩
      obtain ⟨otherRow, otherMember, rebuiltOther⟩ := pair_left normalizedRows sourceRow sourceMember
      have same := row_unique ready.semantic.1.normal.facts.coherent.valid rebuiltRow rebuiltOther
      subst otherRow
      exact (resultOrigins view row).mpr (List.mem_filter.mpr ⟨otherMember, (List.mem_filter.mp retained).2⟩)
  constructor
  · intro atom
    exact iff_of_false (ordinary_literal result atom resultOrdinary) (by
      rintro ⟨output, member, part⟩
      exact ordinary_literal output atom (outputOrdinary output member) part)
  · intro row
    rw [ordinary_row result resultOrdinary common row, rows common row,
      MergedFreshOrdinaryGraph.origin_seeds]
    constructor
    · rintro ⟨output, member, part⟩
      exact ⟨output, member, (ordinary_row output (outputOrdinary output member) common row).mpr part⟩
    · rintro ⟨output, member, part⟩
      exact ⟨output, member, (ordinary_row output (outputOrdinary output member) common row).mp part⟩

end MicroCFTA.SourceCurrentLiteralOrdinaryParts
