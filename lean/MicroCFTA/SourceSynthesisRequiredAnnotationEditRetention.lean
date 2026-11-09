import MicroCFTA.SourceSynthesisTypeRouteProgramFields
import MicroCFTA.SourceSynthesisGuardRegions
import MicroCFTA.SourceSynthesisActualSharedSelectedProgramFootprints

/-!
# Annotation heads through actual class edits

A selected subtree retains its exact original source address. A leaf edit
therefore identifies an endpoint at that address. A below-edit retains an
ordinary input head. These facts do not identify an enumeration bucket.
The application guard excludes the function annotation and its ancestors.
Inherited regions require a separate source provenance argument.
-/
namespace MicroCFTA.SourceSynthesisRequiredAnnotationEditRetention
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityEdits SourceEqualityEditLeafPaths
open SourceCurrentAllocatedClassEditPlan

/-- A retained leaf token is the exact source address plus its remaining suffix. -/
def Placed (record : SourceEqualityClassOrder.Record) (address : EqualityNormalize.Path)
    (edits : Edits EqualityNormalize.Path) : Prop :=
  ∀ path token, (path, token) ∈ leaves edits → token ∈ record.paths ∧
    ∃ suffix : EqualityNormalize.Path, path = suffix.map Int.ofNat ∧ token = address ++ suffix

/-- The actual coherent compiler places every token at its original source address. -/
theorem compiled_placed (record : SourceEqualityClassOrder.Record)
    (coherent : SourceEqualityClassOrder.Coherent record) : Placed record [] (compiled record) := by
  intro path token retained
  have original := (SourceEqualityEditCompiledPaths.build_leaves _
    (compiled_disjoint record coherent)).mem_iff.mp retained
  obtain ⟨source, member, same⟩ := List.mem_map.mp original
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  exact ⟨member, source, rfl, rfl⟩

/-- An actual selected child extends the same source address by its literal index. -/
theorem child_placed {record address entries edits} (index : Nat)
    (placed : Placed record address (.editBelow entries))
    (found : SourceEqualityNeededMap.lookup (index : Int) entries = some edits) :
    Placed record (address ++ [index]) edits := by
  intro path token retained
  obtain ⟨member, suffix, signed, original⟩ := placed (Int.ofNat index :: path) token
    (below_member entries _ edits (SourceEqualityNeededMap.lookup_mem _ _ _ found) path token retained)
  cases suffix with
  | nil => cases signed
  | cons next rest =>
      have parts := List.cons.inj signed
      have sameIndex : index = next := Int.ofNat.inj parts.1
      subst next
      exact ⟨member, rest, parts.2,
        by simpa only [List.append_assoc, List.singleton_append] using original⟩

private def AvoidsFunctionAnnotation (path : EqualityNormalize.Path) : Prop :=
  ¬ path.IsPrefix [2, 0]

private theorem avoids_rightClosed (path : EqualityNormalize.Path)
    (avoids : AvoidsFunctionAnnotation path) (suffix : EqualityNormalize.Path) :
    AvoidsFunctionAnnotation (path ++ suffix) := by
  intro retained
  exact avoids ((show path.IsPrefix (path ++ suffix) from ⟨suffix, rfl⟩).trans retained)

private theorem application_inputs : ∀ path ∈ EqualityNormalize.members
    [[[1], [2, 0, 0]], [[3, 0], [2, 0, 1]], [[0], [2, 0, 2]]],
    AvoidsFunctionAnnotation path := by
  intro path member
  simp [EqualityNormalize.members] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [AvoidsFunctionAnnotation] <;> decide

/-- Normalized own application endpoints cannot replace the function annotation or its ancestors. -/
theorem application_guard_avoids_function_annotation
    (types function argument : SourceSynthesisFirstOrderConstruction.Expression)
    (symbol : String) (guard : SourceSynthesisGeneralizeSyntax.Guard)
    (children : List SourceSynthesisFirstOrderConstruction.Expression)
    (actual : SourceSynthesisFirstOrderConstruction.application types function argument =
      .node [.mk symbol guard children]) :
    ∀ path ∈ EqualityNormalize.members ((SourceCompactGuards.sourceEqualities guard).getD []),
      ¬ path.IsPrefix [2, 0] := by
  cases actual
  rw [SourceSynthesisGuardRegions.eqGuard_accessor]
  intro path member
  cases computed : SourceCompactGuards.normalize
      [[[1], [2, 0, 0]], [[3, 0], [2, 0, 1]], [[0], [2, 0, 2]]] with
  | none =>
      simp [SourceSynthesisGeneralizeSyntax.eqGuard_eq_source, computed,
        EqualityNormalize.members] at member
  | some output =>
      have included : path ∈ EqualityNormalize.members output := by
        simpa only [SourceSynthesisGeneralizeSyntax.eqGuard_eq_source, computed, Option.getD] using member
      exact EqualityNormalizeRightIdeal.normalize_preserves AvoidsFunctionAnnotation avoids_rightClosed
        _ output application_inputs computed path included

/-- An inherited path confined to child zero cannot edit the function annotation or its ancestors. -/
theorem annotation_region_avoids_function_annotation (path : EqualityNormalize.Path)
    (region : SourceSynthesisGuardRegions.annotationRegion path) : ¬ path.IsPrefix [2, 0] := by
  obtain ⟨suffix, rfl⟩ := region
  simp [List.cons_prefix_cons]

open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceCurrentAllocatedSharedEditGraph
open SourceCurrentHereditaryTypePaths (ForestPath)
open SourceCurrentHereditaryTypeEditPlan (NodePaths)
open SourceCurrentEditDomains (Populated)
open SourceEqualityRequiredCache (Ordinary)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Ready" => SourceSynthesisNativeTypeSharedState.Ready
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- An actual annotation edit retains an ordinary head or edits that exact original endpoint. -/
theorem edit_retains_annotation (lib : Library) {record originals address edits input output}
    {before after : SharedState width}
    (actual : EditNode record originals edits input before output after)
    (placed : Placed record address edits) (ready : Ready lib before)
    (originalAvailable : Values before.checked.native.machine.heap originals)
    (originalClosed : ClosedValues originals)
    (originalRoutes : ∀ own ∈ record.paths, ForestPath (Origin lib) (own.map Int.ofNat) originals)
    (populated : Populated edits) (available : Available before.checked.native.machine.heap input)
    (closed : input.free = []) (paths : NodePaths (Origin lib) edits input) (ordinary : Ordinary input) :
    Ordinary output ∨ address ∈ record.paths := by
  cases edits with
  | editAt token =>
      obtain ⟨member, suffix, signed, original⟩ := placed [] token (by simp [leaves])
      have emptySuffix : suffix = [] := List.map_eq_nil_iff.mp signed.symm
      subst suffix
      simp only [List.append_nil] at original
      exact Or.inr (original ▸ member)
  | editBelow entries =>
      exact Or.inl (SourceSynthesisTypeRouteProgramFields.below_ordinary lib actual ready
        originalAvailable originalClosed originalRoutes populated available closed paths ordinary)

section Selected
open SourceSynthesisFirstOrderConstruction (Expression application)
variable [DecidableEq (Value Symbol Guard)]
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
variable {guard : Guard} {loaded : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula}
variable {inherited own : SourceEqualityConstraintAllocation.Value}
variable {start scanned : SourceEqualityNativeDemand.State width}
variable {records kept : List SourceEqualityClassOrder.Record}
variable {budget : Nat} {values : List (Value Symbol Guard)}
variable {fourth savedFourth : SourceCurrentEmptinessMemo.Memo}
variable {outcome : Option EqualityNormalize.Class} {memos final : EndpointMemoGateTrace.Memos}

/-- The actual own-record scan excludes every prefix of the function annotation for any inherited payload. -/
theorem selected_application_avoids_function_annotation (types function argument : Expression)
    (sourceName : String) (sourceChildren : List Expression)
    (occurrence : application types function argument = .node [.mk sourceName guard sourceChildren])
    (receipt : SourceCurrentAllocatedPrecheck.Receipt formulas solver inventory guard loaded
      inherited start own (.classes records))
    (scan : SourceCurrentSharedScanCallerNumeric.ScanReads budget values records
      (SourceCurrentAllocatedPrecheck.state start loaded inherited) fourth
      outcome kept scanned savedFourth memos final) :
    ∀ record ∈ kept, SourceEqualityClassOrder.Coherent record ∧
      ∀ path ∈ record.paths, ¬ path.IsPrefix [2, 0] :=
  SourceSynthesisActualSharedSelectedProgramFootprints.selected_regions receipt scan
    (fun path => ¬ path.IsPrefix [2, 0])
    (application_guard_avoids_function_annotation types function argument sourceName guard sourceChildren occurrence)

/-- A selected own application edit retains its ordinary function annotation at the actual edit endpoint. -/
theorem selected_application_annotation_ordinary (lib : Library) (types function argument : Expression)
    (sourceName : String) (sourceChildren : List Expression)
    (occurrence : application types function argument = .node [.mk sourceName guard sourceChildren])
    (receipt : SourceCurrentAllocatedPrecheck.Receipt formulas solver inventory guard loaded
      inherited start own (.classes records))
    (scan : SourceCurrentSharedScanCallerNumeric.ScanReads budget values records
      (SourceCurrentAllocatedPrecheck.state start loaded inherited) fourth
      outcome kept scanned savedFourth memos final)
    {record originals edits input output} (member : record ∈ kept)
    {before after : SharedState width}
    (actual : EditNode record originals edits input before output after)
    (placed : Placed record [2, 0] edits) (ready : Ready lib before)
    (originalAvailable : Values before.checked.native.machine.heap originals)
    (originalClosed : ClosedValues originals)
    (originalRoutes : ∀ path ∈ record.paths, ForestPath (Origin lib) (path.map Int.ofNat) originals)
    (populated : Populated edits) (available : Available before.checked.native.machine.heap input)
    (closed : input.free = []) (paths : NodePaths (Origin lib) edits input) (ordinary : Ordinary input) :
    Ordinary output := by
  have excluded := (selected_application_avoids_function_annotation types function argument
    sourceName sourceChildren occurrence receipt scan record member).2
  rcases edit_retains_annotation lib actual placed ready originalAvailable originalClosed
    originalRoutes populated available closed paths ordinary with retained | terminal
  · exact retained
  · exact False.elim (excluded [2, 0] terminal ⟨[], rfl⟩)
end Selected

end MicroCFTA.SourceSynthesisRequiredAnnotationEditRetention
