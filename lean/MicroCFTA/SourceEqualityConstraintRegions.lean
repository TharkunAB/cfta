import MicroCFTA.EqualityNormalizeRightIdeal
import MicroCFTA.SourceEqualityInheritedPayload

/-!
# Path regions in actual inherited physical constraints

Normalization can extend endpoints inside a region closed under extension.
Physical readback retains these endpoints. Actual trie descent removes the
selected child index. The caller must derive its input region predicates.
-/
namespace MicroCFTA.SourceEqualityConstraintRegions
open EqualityNormalize SourceEqualityClassOrder
open SourceEqualityDescend (WellFormed)

/-- Every physical endpoint belongs to the supplied path region. -/
def Within (region : Path → Prop) : SourceEqualityPrecheck.Constraint → Prop
  | none => True
  | some records => ∀ record ∈ records, ∀ path ∈ record.paths, region path

private theorem classes_within (region : Path → Prop) (input : SourceEqualityPrecheck.Constraint)
    (within : Within region input) (classes : Constraints)
    (same : SourceEqualityInheritedPayload.classes input = some classes) :
    ∀ path ∈ members classes, region path := by
  cases input with
  | none => cases same
  | some records =>
      have equal : records.map Record.paths = classes := Option.some.inj same
      rw [← equal]
      intro path member
      obtain ⟨paths, included, found⟩ := (mem_members _ _).mp member
      obtain ⟨record, present, rfl⟩ := List.mem_map.mp included
      exact within record present path found

/-- Successful cached physical readback preserves every input endpoint region. -/
theorem read_preserves (region : Path → Prop) (equalities : Option Constraints)
    (cached : SourceEqualityGuardReadback.Cached equalities)
    (input : ∀ classes, equalities = some classes → ∀ path ∈ members classes, region path)
    (payload : SourceEqualityPrecheck.Constraint)
    (done : SourceEqualityPhysicalPayload.read equalities = .ok payload) : Within region payload := by
  cases equalities with
  | none =>
      have same : payload = none := by
        simpa only [SourceEqualityPhysicalPayload.read, Except.ok.injEq] using done.symm
      subst payload
      trivial
  | some classes =>
      obtain ⟨records, built, _valid, paths⟩ := SourceEqualityPhysicalPayload.normal_records classes (cached classes rfl)
      have same : payload = some records := by
        simpa only [SourceEqualityPhysicalPayload.read, built, Except.ok.injEq] using done.symm
      subst payload
      intro record present path found
      have included : record.paths ∈ classes := paths ▸ List.mem_map.mpr ⟨record, present, rfl⟩
      exact input classes rfl path ((mem_members _ _).mpr ⟨record.paths, included, found⟩)

private theorem combined_paths (region : Path → Prop)
    (rightClosed : ∀ path, region path → ∀ suffix, region (path ++ suffix))
    (first second : Option Constraints)
    (firstWithin : ∀ classes, first = some classes → ∀ path ∈ members classes, region path)
    (secondWithin : ∀ classes, second = some classes → ∀ path ∈ members classes, region path)
    (output : Constraints) (done : SourceCompactGuards.combineEqualities first second = some output) :
    ∀ path ∈ members output, region path := by
  cases first with
  | none => cases done
  | some first =>
      cases second with
      | none => cases done
      | some second =>
          by_cases empty : first = [] ∧ second = []
          · obtain ⟨rfl, rfl⟩ := empty
            have same : output = [] := Option.some.inj done.symm
            subst output
            simp [members]
          · have normalized : SourceCompactGuards.normalize (first ++ second) = some output := by
              cases first <;> cases second <;>
                first | exact done | exact False.elim (empty ⟨rfl, rfl⟩)
            apply EqualityNormalizeRightIdeal.normalize_preserves region rightClosed (first ++ second) output
              ?_ normalized
            intro path member
            obtain ⟨paths, included, found⟩ := (mem_members _ _).mp member
            rcases List.mem_append.mp included with left | right
            · exact firstWithin first rfl path ((mem_members _ _).mpr ⟨paths, left, found⟩)
            · exact secondWithin second rfl path ((mem_members _ _).mpr ⟨paths, right, found⟩)

/-- The actual inherited combiner retains regions closed under generated suffixes. -/
theorem combine_preserves (region : Path → Prop)
    (rightClosed : ∀ path, region path → ∀ suffix, region (path ++ suffix))
    (inherited own combined : SourceEqualityPrecheck.Constraint)
    (inheritedWithin : Within region inherited) (ownWithin : Within region own)
    (done : SourceEqualityInheritedPayload.combine inherited own = .ok combined) :
    Within region combined := by
  apply read_preserves region
    (SourceCompactGuards.combineEqualities (SourceEqualityInheritedPayload.classes inherited)
      (SourceEqualityInheritedPayload.classes own))
    (SourceEqualityGuardReadback.combine_cached _ _) ?_ combined done
  intro output normalized
  exact combined_paths region rightClosed _ _ (classes_within region inherited inheritedWithin)
    (classes_within region own ownWithin) output normalized

/-- Actual physical trie descent retains the selected-index suffix region. -/
theorem descend_preserves (region : Path → Prop) (input : SourceEqualityPrecheck.Constraint)
    (wellFormed : WellFormed input) (within : Within region input) (index : Nat) :
    Within (fun suffix => region (index :: suffix)) (SourceEqualityDescend.descend input index) := by
  cases input with
  | none => trivial
  | some originals =>
      cases originals with
      | nil => simp [SourceEqualityDescend.descend, Within]
      | cons first rest =>
          intro output present suffix found
          have selected := (SourceEqualityDescend.records_perm index (first :: rest)).mem_iff.mp present
          obtain ⟨original, included, built⟩ := List.mem_filterMap.mp selected
          have originalPath := (SourceEqualityDescend.record_pairs index original
            (wellFormed (first :: rest) rfl original included).1 output built suffix).mp found
          exact within original included (index :: suffix) originalPath

/-- Actual combination derives complete well-formed payloads and every child region internally. -/
theorem combine_descend_preserves (region : Path → Prop)
    (rightClosed : ∀ path, region path → ∀ suffix, region (path ++ suffix))
    (inherited own : SourceEqualityPrecheck.Constraint)
    (inheritedWithin : Within region inherited) (ownWithin : Within region own) :
    ∃ combined, SourceEqualityInheritedPayload.combine inherited own = .ok combined ∧
      WellFormed combined ∧ Within region combined ∧
      ∀ index, Within (fun suffix => region (index :: suffix)) (SourceEqualityDescend.descend combined index) := by
  obtain ⟨combined, done, wellFormed, _meaning⟩ :=
    SourceEqualityInheritedPayload.combine_complete (Symbol := Unit) inherited own
  have within := combine_preserves region rightClosed inherited own combined inheritedWithin ownWithin done
  exact ⟨combined, done, wellFormed, within, descend_preserves region combined wellFormed within⟩

end MicroCFTA.SourceEqualityConstraintRegions
