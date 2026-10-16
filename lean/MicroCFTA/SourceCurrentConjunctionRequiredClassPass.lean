import MicroCFTA.SourceCurrentConjunctionRequiredGlobalMemos
import MicroCFTA.SourceCurrentAllocatedClassPass

/-!
# Current required paths followed by the checked class pass

The required receipt supplies every selected path domain. The class right
fold starts at its literal returned checked state. Its final language
narrows the original forest and retains each class-satisfying required
term. Unselected siblings can remain open.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequiredClassPass
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedGuardedLanguage (meaning)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedClassPass (Pass PassReads Ranges)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

omit [DecidableEq Symbol] in
/-- Exact selected record paths derive all class-entry domains from required execution. -/
theorem selected_domains
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {selected : Constraints} {originals values : List (Value Symbol Guard)}
    {before prepared : Checked width}
    (required : SourceCurrentConjunctionRequired.Receipt formulas solver inventory selected originals values before prepared)
    (records : List SourceEqualityClassOrder.Record)
    (selectedEq : records.map SourceEqualityClassOrder.Record.paths = selected) :
    ∀ record ∈ records, ∀ path ∈ record.paths,
      SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) values := by
  intro record member path present
  have selectedMember : record.paths ∈ selected := selectedEq ▸ List.mem_map.mpr ⟨record, member, rfl⟩
  exact required.paths path (List.mem_flatten.mpr ⟨record.paths, selectedMember, present⟩)

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
/-- Satisfied nontrivial classes supply the literal compiled forest requirements. -/
theorem satisfied_required (classes : Constraints) (symbol : S) (terms : List (Term S))
    (active : ∀ paths ∈ classes, Nontrivial paths)
    (satisfied : ∀ paths ∈ classes, ClassSat (.node symbol terms) paths) :
    SourceEqualityRequiredAPI.ForestRequired (SourceEqualitySelectedRequired.paths classes) terms := by
  have existsPath : ∀ path ∈ classes.flatten, ∃ part, (Term.node symbol terms).atPath path = some part := by
    intro path member
    obtain ⟨paths, included, present⟩ := List.mem_flatten.mp member
    exact class_member_exists (.node symbol terms) paths (active paths included) (satisfied paths included) path present
  have matched := (SourceEqualityNeededMeaning.build_exact
    (SourceEqualitySelectedRequired.paths classes) (.node symbol terms)).mpr
      ((SourceEqualitySelectedRequired.paths_exist _ _).mpr existsPath)
  have valid := SourceEqualityNeeded.build_valid (SourceEqualitySelectedRequired.paths classes)
  cases compiled : SourceEqualityNeeded.build (SourceEqualitySelectedRequired.paths classes) with
  | node entries =>
      rw [SourceEqualityRequiredAPI.ForestRequired, compiled]
      have ordered := (show SourceEqualityNeededMap.Ascending entries ∧ _ from
        by simpa only [SourceEqualityNeeded.Valid, compiled] using valid).1
      apply (SourceEqualityRequiredForestMeaning.required_zero entries ordered terms).mpr
      rw [compiled, SourceEqualityNeededMeaning.Matches] at matched
      intro index needed member term selected
      obtain ⟨actual, found, actualMatched⟩ := matched index needed member
      have same : actual = term := Option.some.inj (found.symm.trans selected)
      subst actual
      exact actualMatched

/-- The class receipt retains its exact required entry and original forest language. -/
structure Receipt (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (records : List SourceEqualityClassOrder.Record) (selected : Constraints)
    (originals values : List (Value Symbol Guard)) (before prepared : Checked width) (memo : Memo)
    (results : List (Value Symbol Guard)) (after : Checked width) (saved : Memo) (memos final : Memos) : Prop where
  pass : SourceCurrentAllocatedClassPass.Receipt formulas solver inventory records values prepared memo results after saved memos final
  effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before) (physical after)
  extension : SourceRecursiveIntersectionKernel.Extension before.native.machine after.native.machine
  originals_available : Values after.native.machine.heap originals
  language : ∀ ambient symbol terms,
    (All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) results terms →
      All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) originals terms ∧
        SourceEqualityRequiredAPI.ForestRequired (SourceEqualitySelectedRequired.paths selected) terms) ∧
    ((∀ paths ∈ selected, ClassSat (.node symbol terms) paths) →
      (All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) results terms ↔
        All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) originals terms))

omit [DecidableEq Symbol] in
private theorem receipt
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory next : Inventory} {selected : Constraints} {records : List SourceEqualityClassOrder.Record}
    {originals values results : List (Value Symbol Guard)} {before prepared after : Checked width}
    {memo saved : Memo} {memos final : Memos}
    (required : SourceCurrentConjunctionRequired.Receipt formulas solver inventory selected originals values before prepared)
    (selectedEq : records.map SourceEqualityClassOrder.Record.paths = selected)
    (active : ∀ record ∈ records, Nontrivial record.paths)
    (passed : SourceCurrentAllocatedClassPass.Receipt formulas solver next records values prepared memo results after saved memos final) :
    Receipt formulas solver next records selected originals values before prepared memo results after saved memos final := by
  refine ⟨passed, required.effects.trans passed.effects, required.extension.trans passed.extension,
    (fun value member => passed.effects.keeps.available value (required.originals value member)), ?_⟩
  intro ambient symbol terms
  have requiredLanguage := required.language (SourceEqualityPCSGuard.holds formulas solver) ambient terms
  have passLanguage := passed.language ambient symbol terms
  refine ⟨fun accepted => requiredLanguage.mp (passLanguage.1 accepted), ?_⟩
  intro satisfied
  have classSatisfied : ∀ record ∈ records, ClassSat (.node symbol terms) record.paths := by
    intro record member
    exact satisfied record.paths (selectedEq ▸ List.mem_map.mpr ⟨record, member, rfl⟩)
  have selectedActive : ∀ paths ∈ selected, Nontrivial paths := by
    intro paths member
    rw [← selectedEq] at member
    obtain ⟨record, present, same⟩ := List.mem_map.mp member
    rw [← same]
    exact active record present
  have requiredSatisfied := satisfied_required selected symbol terms selectedActive satisfied
  exact (passLanguage.2 classSatisfied).trans (requiredLanguage.trans
    ⟨And.left, fun accepted => ⟨accepted, requiredSatisfied⟩⟩)

/-- Actual annotated class execution derives the composed receipt at its own returned state. -/
theorem verified
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) {selected : Constraints} {originals values : List (Value Symbol Guard)}
    {before prepared : Checked width}
    (required : SourceCurrentConjunctionRequired.Receipt formulas solver inventory selected originals values before prepared)
    (records : List SourceEqualityClassOrder.Record)
    (selectedEq : records.map SourceEqualityClassOrder.Record.paths = selected)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, Nontrivial record.paths)
    {memo saved : Memo} {results : List (Value Symbol Guard)} {after : Checked width} {memos final : Memos}
    {actual : Pass records values prepared memo results after saved}
    (reads : PassReads formulas solver actual memos final)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : Valid prepared.native.machine.heap memos) :
    ∃ next, Receipt formulas solver next records selected originals values before prepared memo results after saved memos final := by
  obtain ⟨next, passed⟩ := SourceCurrentAllocatedClassPass.Pass.verified formulas solver inventory reads coherent active
    required.ready required.admitted required.resident (selected_domains required records selectedEq)
    (stored.grows required.effects.keeps) covered valid
  exact ⟨next, receipt formulas solver required selectedEq active passed⟩

/-- Required domains and actual-prefix ranges construct the complete checked class pass. -/
theorem finite
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) {selected : Constraints} {originals values : List (Value Symbol Guard)}
    {before prepared : Checked width}
    (required : SourceCurrentConjunctionRequired.Receipt formulas solver inventory selected originals values before prepared)
    (records : List SourceEqualityClassOrder.Record)
    (selectedEq : records.map SourceEqualityClassOrder.Record.paths = selected)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, Nontrivial record.paths)
    (memo : Memo) (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : Ranges records values prepared memo) (memos : Memos) (valid : Valid prepared.native.machine.heap memos) :
    ∃ results after saved next final, ∃ actual : Pass records values prepared memo results after saved,
      PassReads formulas solver actual memos final ∧
      Receipt formulas solver next records selected originals values before prepared memo results after saved memos final := by
  obtain ⟨results, after, saved, next, final, actual, reads, passed⟩ := SourceCurrentAllocatedClassPass.pass_complete
    formulas solver inventory ranges coherent active required.ready required.admitted required.resident
    (selected_domains required records selectedEq) (stored.grows required.effects.keeps) covered memos valid
  exact ⟨results, after, saved, next, final, actual, reads, receipt formulas solver required selectedEq active passed⟩

omit [DecidableEq Symbol] in
/-- The unchanged fourth memo retains correctness through required execution and the class pass. -/
theorem Receipt.fourth_correct
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {records : List SourceEqualityClassOrder.Record} {selected : Constraints}
    {originals values results : List (Value Symbol Guard)} {before prepared after : Checked width}
    {memo saved : Memo} {memos final : Memos}
    (checked : Receipt formulas solver inventory records selected originals values before prepared memo results after saved memos final)
    (fourth : SourceCurrentEmptinessMemo.Memo)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth) :
    SourceCurrentEmptinessMemo.Correct formulas solver after.native.machine.heap fourth :=
  SourceCurrentEmptinessMemo.grows formulas solver checked.effects.keeps fourth correct

end MicroCFTA.SourceCurrentConjunctionRequiredClassPass
