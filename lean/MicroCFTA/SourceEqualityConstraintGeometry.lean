import MicroCFTA.SourceEqualityGuardReadback

/-!
# Original finite geometry of source equality conjunctions

Stored classes retain bounded prefix gaps, an original path in each
component, and original child indices. Completion and each actual source
step preserve these properties. Successful source conjunction therefore
preserves the same original finite geometry.
-/
namespace MicroCFTA.SourceEqualityConstraintGeometry
open Language EqualityNormalize EqualitySaturation EqualityTermination
open SourceEqualityGuardReadback

/-- Original bounds and anchors for one stored equality payload. -/
structure Region (gap : Nat) (anchors : List (List Nat)) (alphabet : List Nat) (classes : Constraints) : Prop where
  active : Active classes
  segmented : SegmentedState gap classes
  anchored : Anchored anchors classes
  allowed : UsesAlphabet alphabet classes

/-- The empty source payload satisfies every original geometry bound. -/
theorem empty (gap : Nat) (anchors : List (List Nat)) (alphabet : List Nat) :
    Region gap anchors alphabet [] := by
  constructor <;> simp [Active, SegmentedState, Anchored, UsesAlphabet, members]

private theorem append_members (first second : Constraints) (path : List Nat) :
    path ∈ members (first ++ second) ↔ path ∈ members first ∨ path ∈ members second := by
  simp [mem_members, List.mem_append, or_and_right, exists_or]

/-- Original geometry is closed under the actual pre-normalization concatenation. -/
theorem append {gap : Nat} {anchors : List (List Nat)} {alphabet : List Nat} {first second : Constraints}
    (firstRegion : Region gap anchors alphabet first) (secondRegion : Region gap anchors alphabet second) :
    Region gap anchors alphabet (first ++ second) := by
  constructor
  · intro paths member
    rcases List.mem_append.mp member with member | member
    · exact firstRegion.active paths member
    · exact secondRegion.active paths member
  · intro path member
    rcases (append_members first second path).mp member with member | member
    · exact segments_mono gap first _ (fun _ present => (append_members _ _ _).mpr (Or.inl present))
        [] path (firstRegion.segmented path member)
    · exact segments_mono gap second _ (fun _ present => (append_members _ _ _).mpr (Or.inr present))
        [] path (secondRegion.segmented path member)
  · intro paths member
    rcases List.mem_append.mp member with member | member
    · exact firstRegion.anchored paths member
    · exact secondRegion.anchored paths member
  · intro path member index present
    rcases (append_members first second path).mp member with member | member
    · exact firstRegion.allowed path member index present
    · exact secondRegion.allowed path member index present

/-- Actual component completion preserves original geometry. -/
theorem complete {gap : Nat} {anchors : List (List Nat)} {alphabet : List Nat} {classes : Constraints}
    (region : Region gap anchors alphabet classes) :
    Region gap anchors alphabet (EqualityNormalize.complete classes) := by
  constructor
  · exact complete_active classes region.active
  · intro path member
    exact segments_mono gap classes _ (fun _ present => (complete_members _ _).mpr present)
      [] path (region.segmented path ((complete_members _ _).mp member))
  · intro component member
    obtain ⟨path, present, _, _, _⟩ := complete_active classes region.active component member
    obtain ⟨source, sourceMember, inSource⟩ := (mem_members _ _).mp
      ((complete_members _ _).mp ((mem_members _ _).mpr ⟨component, member, present⟩))
    obtain ⟨retained, retainedMember, included⟩ := complete_covers classes source sourceMember
    have same := components_equal _ (complete_disjoint classes) retained component retainedMember member path
      (included path inSource) present
    obtain ⟨anchor, anchorMember, original⟩ := region.anchored source sourceMember
    exact ⟨anchor, by simpa [same] using included anchor anchorMember, original⟩
  · intro path member index present
    exact region.allowed path ((complete_members _ _).mp member) index present

/-- A successful actual source step preserves the original geometry. -/
theorem step {gap : Nat} {anchors : List (List Nat)} {alphabet : List Nat} {classes output : Constraints}
    (region : Region gap anchors alphabet classes) (done : congruenceStep classes = some output) :
    Region gap anchors alphabet output :=
  ⟨(step_normal classes output region.active done).1, step_segmented gap classes output region.segmented done,
    step_anchored anchors classes output region.active region.anchored done,
    step_alphabet alphabet classes output region.allowed done⟩

/-- Every completed source fixed-point loop preserves original geometry. -/
theorem fixMaybe {gap : Nat} {anchors : List (List Nat)} {alphabet : List Nat}
    (fuel : Nat) (classes output : Constraints) (region : Region gap anchors alphabet classes)
    (done : EqualityNormalize.fixMaybe fuel classes = .normalized output) : Region gap anchors alphabet output := by
  induction fuel generalizing classes with
  | zero => simp [EqualityNormalize.fixMaybe] at done
  | succ fuel ih =>
      cases advanced : congruenceStep classes with
      | none => simp [EqualityNormalize.fixMaybe, advanced] at done
      | some next =>
          by_cases stable : next = classes
          · have same : output = classes := by simpa [EqualityNormalize.fixMaybe, advanced, stable] using done.symm
            simpa [same] using region
          · exact ih next (step region advanced)
              (by simpa [EqualityNormalize.fixMaybe, advanced, stable] using done)

private theorem eraseDups_self (paths : Class) (unique : paths.Nodup) : paths.eraseDups = paths := by
  induction paths with
  | nil => rfl
  | cons first rest ih =>
      have filtered : rest.filter (fun path => !path == first) = rest := by
        apply List.filter_eq_self.mpr
        intro path member
        have different : path ≠ first := by
          intro same
          exact (List.nodup_cons.mp unique).1 (same ▸ member)
        simpa using different
      rw [List.eraseDups_cons, filtered, ih (List.nodup_cons.mp unique).2]

private theorem prepare_eq (classes : Constraints) (active : Active classes)
    (canonical : ∀ paths ∈ classes, canonicalClass paths = paths) : prepare classes = classes := by
  have mapped : classes.map List.eraseDups = classes := by
    calc
      classes.map List.eraseDups = classes.map id := by
        apply List.map_congr_left
        intro paths member
        have unique := canonicalClass_nodup paths
        rw [canonical paths member] at unique
        exact eraseDups_self paths unique
      _ = classes := List.map_id classes
  unfold prepare
  rw [mapped]
  exact List.filter_eq_self.mpr (fun paths member => (nontrivialB_correct paths).mpr (active paths member))

/-- Successful actual array normalization retains original geometry and canonical source classes. -/
theorem normalize {gap : Nat} {anchors : List (List Nat)} {alphabet : List Nat}
    (classes output : Constraints) (region : Region gap anchors alphabet classes)
    (canonical : ∀ paths ∈ classes, canonicalClass paths = paths)
    (done : SourceCompactGuards.normalize classes = some output) :
    Region gap anchors alphabet output ∧ NormalState output ∧ isContradicting output = false := by
  unfold SourceCompactGuards.normalize at done
  rw [SourceCompactGuards.arrayNormalize_eq] at done
  cases finished : mkEqConstraints (normalizationBound classes) classes with
  | timeout | contradiction => simp [finished, SymbolicEqualityBridge.resultClasses] at done
  | normalized result =>
      have same : result = output := by simpa [finished, SymbolicEqualityBridge.resultClasses] using done
      subst result
      obtain ⟨active, consistent, _, fixed⟩ := mkEqConstraints_invariants _ _ _ finished
      have prepared : EqualityNormalize.fixMaybe (normalizationBound classes) (EqualityNormalize.complete classes) =
          .normalized output := by
        simpa only [mkEqConstraints, prepare_eq classes region.active canonical] using finished
      exact ⟨fixMaybe _ _ _ (complete region) prepared, step_normal output output active fixed, consistent⟩

/-- Successful source conjunction preserves the common original geometry of its actual cached operands. -/
theorem combine (gap : Nat) (anchors : List (List Nat)) (alphabet : List Nat)
    (first second : Option Constraints) (firstCached : Cached first) (secondCached : Cached second)
    (firstRegion : ∀ classes, first = some classes → Region gap anchors alphabet classes)
    (secondRegion : ∀ classes, second = some classes → Region gap anchors alphabet classes)
    (output : Constraints) (done : SourceCompactGuards.combineEqualities first second = some output) :
    Region gap anchors alphabet output ∧ NormalState output ∧ isContradicting output = false := by
  cases first with
  | none => simp [SourceCompactGuards.combineEqualities] at done
  | some first => cases second with
    | none => simp [SourceCompactGuards.combineEqualities] at done
    | some second =>
        have region := append (firstRegion first rfl) (secondRegion second rfl)
        have canonical : ∀ paths ∈ first ++ second, canonicalClass paths = paths := by
          intro paths member
          rcases List.mem_append.mp member with member | member
          · exact (firstCached first rfl).2.2 paths member
          · exact (secondCached second rfl).2.2 paths member
        cases first with
        | nil => cases second with
          | nil =>
              have same : output = [] := by simpa [SourceCompactGuards.combineEqualities] using done.symm
              subst output
              exact ⟨empty gap anchors alphabet, by simp [NormalState, Active], by simp [isContradicting]⟩
          | cons paths rest => exact normalize _ _ region canonical done
        | cons paths rest => cases second <;> exact normalize _ _ region canonical done

end MicroCFTA.SourceEqualityConstraintGeometry
