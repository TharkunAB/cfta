import MicroCFTA.SourceCurrentActualRequiredRowOrigins
import MicroCFTA.SourceCurrentClassPositionalFootprints

/-!
# Source path footprints for actual Required compilation

A compiled child demand has a complete source path extending that child.
Canonical selected-path union preserves membership through sorting and
deduplication. Source path exclusions therefore derive actual absent keys.
These laws do not assume future Required or class execution.
-/
namespace MicroCFTA.SourceCurrentRequiredPathFootprints
open SourceEqualityNeeded SourceEqualityNeededMap
local notation "Record" => SourceEqualityClassOrder.Record

/-- Source paths outside a forest slot leave its actual Required key absent. -/
theorem build_absent (paths : List Path) (forestIndex : Nat)
    (excluded : ∀ path ∈ paths, ¬ [Int.ofNat forestIndex].IsPrefix path)
    {entries : List (Int × Needed)} (built : build paths = .node entries) :
    lookup (forestIndex : Int) entries = none := by
  cases found : lookup (forestIndex : Int) entries with
  | none => rfl
  | some needed =>
      have demanded : demands (build paths) [Int.ofNat forestIndex] = true := by
        simp only [built,demands,Int.ofNat_eq_natCast,found]
      rcases (demands_build paths [Int.ofNat forestIndex]).mp demanded with empty | ⟨path,member,initial⟩
      · cases empty
      · exact False.elim (excluded path member initial)

/-- Source path exclusion derives an absent indexed child in the actual Needed trie. -/
theorem build_unselected (paths : List Path) (forestIndex childIndex : Nat)
    (excluded : ∀ path ∈ paths, ¬ [Int.ofNat forestIndex,Int.ofNat childIndex].IsPrefix path)
    {entries : List (Int × Needed)} (built : build paths = .node entries) :
    SourceCurrentActualRequiredRowOrigins.Unselected entries forestIndex childIndex := by
  intro needed found children shape
  cases next : lookup (childIndex : Int) children with
  | none => rfl
  | some child =>
      have demanded : demands (build paths) [Int.ofNat forestIndex,Int.ofNat childIndex] = true := by
        simp only [built,demands,Int.ofNat_eq_natCast,found,shape,next]
      rcases (demands_build paths [Int.ofNat forestIndex,Int.ofNat childIndex]).mp demanded with empty | ⟨path,member,initial⟩
      · cases empty
      · exact False.elim (excluded path member initial)

private theorem selected_member (records : List Record) (path : Path)
    (member : path ∈ SourceEqualitySelectedRequired.paths (records.map SourceEqualityClassOrder.Record.paths)) :
    ∃ record ∈ records, ∃ natural ∈ record.paths, path = natural.map Int.ofNat := by
  obtain ⟨natural,canonical,same⟩ := List.mem_map.mp member
  have flattened : natural ∈ (records.map SourceEqualityClassOrder.Record.paths).flatten :=
    (EqualityNormalize.mem_canonicalClass natural _).mp canonical
  obtain ⟨paths,included,contained⟩ := List.mem_flatten.mp flattened
  obtain ⟨record,retained,samePaths⟩ := List.mem_map.mp included
  subst paths
  exact ⟨record,retained,natural,contained,same.symm⟩

/-- Every original record's path exclusion survives selected-path sorting and deduplication. -/
theorem selected_records (records : List Record) (forestIndex childIndex : Nat)
    (unselected : ∀ record ∈ records,
      SourceCurrentClassPositionalFootprints.Unselected record forestIndex childIndex)
    {entries : List (Int × Needed)}
    (built : build (SourceEqualitySelectedRequired.paths (records.map SourceEqualityClassOrder.Record.paths)) = .node entries) :
    SourceCurrentActualRequiredRowOrigins.Unselected entries forestIndex childIndex := by
  apply build_unselected _ forestIndex childIndex _ built
  intro path member
  obtain ⟨record,retained,natural,included,rfl⟩ := selected_member records path member
  exact (unselected record retained natural included).2

/-- A source forest-slot exclusion also survives selected-record flattening and canonicalization. -/
theorem selected_records_absent (records : List Record) (forestIndex : Nat)
    (excluded : ∀ record ∈ records, ∀ path ∈ record.paths, ¬ [Int.ofNat forestIndex].IsPrefix (path.map Int.ofNat))
    {entries : List (Int × Needed)}
    (built : build (SourceEqualitySelectedRequired.paths (records.map SourceEqualityClassOrder.Record.paths)) = .node entries) :
    lookup (forestIndex : Int) entries = none := by
  apply build_absent _ forestIndex _ built
  intro path member
  obtain ⟨record,retained,natural,included,rfl⟩ := selected_member records path member
  exact excluded record retained natural included

end MicroCFTA.SourceCurrentRequiredPathFootprints
