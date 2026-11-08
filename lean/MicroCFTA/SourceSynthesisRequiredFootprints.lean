import MicroCFTA.SourceCurrentRequiredPathFootprints
import MicroCFTA.SourceEqualityClassEdits
import MicroCFTA.SourceSynthesisGuardRegions

/-!
# Actual Required footprints from synthesis path regions

The selected path list retains the source signed conversion and canonical
union. Type-region paths leave each program child's non-annotation children
unselected. These laws require the current region. They do not establish
future row roles or termination of program execution.
-/
namespace MicroCFTA.SourceSynthesisRequiredFootprints
open InternedConstructorTemplates EqualityNormalize
open InternedSourceClassSelection (Query Trace selected)
open SourceEqualityNeeded (Needed)
open SourceCurrentActualRequiredRowOrigins (Unselected)
open SourceSynthesisGuardRegions

/-- Natural endpoint exclusions supply actual absent internal keys after selected-path compilation. -/
theorem classes_unselected (classes : Constraints) (forestIndex childIndex : Nat)
    (excluded : ∀ path ∈ members classes, ¬ [forestIndex, childIndex].IsPrefix path)
    {entries : List (Int × Needed)}
    (built : SourceEqualityNeeded.build (SourceEqualitySelectedRequired.paths classes) = .node entries) :
    Unselected entries forestIndex childIndex := by
  apply SourceCurrentRequiredPathFootprints.build_unselected _ forestIndex childIndex ?_ built
  intro path member initial
  obtain ⟨natural, canonical, rfl⟩ := List.mem_map.mp member
  have original : natural ∈ members classes := by
    simpa only [members, List.mem_eraseDups] using (mem_canonicalClass natural classes.flatten).mp canonical
  exact excluded natural original ((SourceEqualityClassEdits.signed_prefix [forestIndex, childIndex] natural).mp initial)

private theorem program_excluded (region : Path → Prop) (forestIndex childIndex : Nat)
    (program : ∀ path, region (forestIndex :: path) → annotationRegion path)
    (nonzero : childIndex ≠ 0) (path : Path) (inside : region path) :
    ¬ [forestIndex, childIndex].IsPrefix path := by
  intro initial
  obtain ⟨suffix, rfl⟩ := initial
  obtain ⟨rest, equal⟩ := program (childIndex :: suffix) inside
  change 0 :: rest = childIndex :: suffix at equal
  exact nonzero (List.cons.inj equal).1.symm

/-- Actual application Type regions leave internal non-annotation children of both programs unselected. -/
theorem application_unselected (classes : Constraints)
    (within : ∀ path ∈ members classes, applicationRegion path)
    (childIndex : Nat) (nonzero : childIndex ≠ 0) {entries : List (Int × Needed)}
    (built : SourceEqualityNeeded.build (SourceEqualitySelectedRequired.paths classes) = .node entries) :
    Unselected entries 2 childIndex ∧ Unselected entries 3 childIndex := by
  constructor
  · apply classes_unselected classes 2 childIndex ?_ built
    intro path member
    exact program_excluded applicationRegion 2 childIndex
      (fun path inside => (application_descend_function path).mp inside) nonzero path (within path member)
  · apply classes_unselected classes 3 childIndex ?_ built
    intro path member
    exact program_excluded applicationRegion 3 childIndex
      (fun path inside => (application_descend_argument path).mp inside) nonzero path (within path member)

/-- Actual filter Type regions leave the candidate program's internal non-annotation children unselected. -/
theorem filter_unselected (classes : Constraints)
    (within : ∀ path ∈ members classes, filterRegion path)
    (childIndex : Nat) (nonzero : childIndex ≠ 0) {entries : List (Int × Needed)}
    (built : SourceEqualityNeeded.build (SourceEqualitySelectedRequired.paths classes) = .node entries) :
    Unselected entries 1 childIndex := by
  apply classes_unselected classes 1 childIndex ?_ built
  intro path member
  exact program_excluded filterRegion 1 childIndex
    (fun path inside => (filter_descend_program path).mp inside) nonzero path (within path member)

private theorem selected_within [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {values : List (Value Symbol Guard)}
    {classes : Constraints} {before after : State Symbol Guard} {queries : List (Query Symbol Guard)}
    (trace : Trace unconstrained values classes before queries after)
    (region : Path → Prop) (within : ∀ path ∈ members classes, region path) :
    ∀ path ∈ members (selected queries), region path := by
  intro path member
  obtain ⟨paths, present, found⟩ := (mem_members _ _).mp member
  exact within path ((mem_members _ _).mpr ⟨paths, trace.sublist.subset present, found⟩)

/-- A real ordered application selection derives its Required footprints from the input region. -/
theorem application_queries [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {values : List (Value Symbol Guard)}
    {classes : Constraints} {before after : State Symbol Guard} {queries : List (Query Symbol Guard)}
    (trace : Trace unconstrained values classes before queries after)
    (within : ∀ path ∈ members classes, applicationRegion path)
    (childIndex : Nat) (nonzero : childIndex ≠ 0) {entries : List (Int × Needed)}
    (built : SourceEqualityNeeded.build (SourceEqualitySelectedRequired.paths (selected queries)) = .node entries) :
    Unselected entries 2 childIndex ∧ Unselected entries 3 childIndex :=
  application_unselected (selected queries) (selected_within trace applicationRegion within) childIndex nonzero built

/-- A real ordered filter selection derives its Required footprint from the input region. -/
theorem filter_queries [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {values : List (Value Symbol Guard)}
    {classes : Constraints} {before after : State Symbol Guard} {queries : List (Query Symbol Guard)}
    (trace : Trace unconstrained values classes before queries after)
    (within : ∀ path ∈ members classes, filterRegion path)
    (childIndex : Nat) (nonzero : childIndex ≠ 0) {entries : List (Int × Needed)}
    (built : SourceEqualityNeeded.build (SourceEqualitySelectedRequired.paths (selected queries)) = .node entries) :
    Unselected entries 1 childIndex :=
  filter_unselected (selected queries) (selected_within trace filterRegion within) childIndex nonzero built

end MicroCFTA.SourceSynthesisRequiredFootprints
