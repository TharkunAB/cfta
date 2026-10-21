import MicroCFTA.SourceCurrentPositiveOwnerPair
import MicroCFTA.SourceCurrentRequiredPositiveChronology
import MicroCFTA.SourceCurrentAllocatedPrecheck
import MicroCFTA.SourceCurrentConjunctionSelectedRecords
import MicroCFTA.SourceCurrentOuterOriginDependencies

/-!
# A same-owner copy retains a pair in the actual combined family

The selected precheck and Scan retain the original owner row. The completed
Required and class pass supply its backwards positive relation. Whole-class
coverage transfers that relation to the actual inherited-first combination.
The finite-path theorem then supplies a distinct pair through the same child.
-/
namespace MicroCFTA.SourceCurrentActualOwnerPair
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentConjunctionClassScan (Scan)
open SourceCurrentConjunctionSelectedRecords (Retained)
open SourceCurrentAllocatedClassPass (Pass PassReads)
open SourceCurrentNativeMuPublication (History)
open SourceCurrentNormalizedChildSeparation (Rel)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Record" => SourceEqualityClassOrder.Record
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Operations" => SourceEqualityConstraintMemoAllocation.State
local notation "Inventory" => SourceCurrentAllocatedNativeInventoryState.Inventory
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source

private theorem rel_covers {classes others : EqualityNormalize.Constraints}
    (covered : EqualityNormalize.Covers classes others) {left right}
    (related : Rel classes left right) : Rel others left right := by
  induction related with
  | refl path => exact .refl path
  | member paths selected left right first second suffix =>
      obtain ⟨larger, included, preserves⟩ := covered paths selected
      exact .member larger included left right (preserves left first) (preserves right second) suffix
  | trans _ _ first second => exact .trans first second

private theorem prefix_family (original : Guard) (inherited : EqValue)
    (before : Operations) (valid : SourceEqualityConstraintMemoAllocation.Valid before)
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.constraints inherited)
    (field : SourceCurrentConjunctionEquality.FieldAvailable before original)
    (combined : EqValue)
    (actual : (SourceCurrentAllocatedInheritedPrefix.run original inherited before).1 = .ok (some combined))
    (outputs : List Record) (payload : combined.payload = some outputs)
    (selected : EqualityNormalize.Constraints)
    (ownSelected : ∀ paths ∈ selected, paths ∈ (SourceCompactGuards.sourceEqualities original).getD []) :
    EqualityNormalize.Covers selected (outputs.map SourceEqualityClassOrder.Record.paths) ∧
      EqualityNormalize.congruenceStep (outputs.map SourceEqualityClassOrder.Record.paths) = some (outputs.map SourceEqualityClassOrder.Record.paths) := by
  cases inherited with
  | contradiction =>
      change (Except.ok (some (.contradiction : EqValue)) : Except String (Option EqValue)) =
        Except.ok (some combined) at actual
      have same : combined = .contradiction := (Option.some.inj (Except.ok.inj actual)).symm
      subst combined
      cases payload
  | live identity records =>
      obtain ⟨own, loaded, accessorValid, ownReady, ownClasses, _ownRead, accessorGrowth⟩ :=
        SourceCurrentConjunctionEquality.accessor_correct original before valid field
      obtain ⟨result, combinedActual, _finalValid, _ready, _growth, fixed, covers⟩ :=
        SourceCurrentOuterOriginDependencies.combine_covers (.live identity records) own
          (SourceCurrentConjunctionEquality.accessor original before).2 accessorValid
          (inheritedReady.grows accessorGrowth.constraint_growth) ownReady
      have resultActual : (SourceCurrentAllocatedInheritedPrefix.run original (.live identity records) before).1 =
          .ok (some result) := by
        rw [SourceCurrentAllocatedInheritedPrefix.run_combine original identity records before own loaded]
        simp only [combinedActual, Except.map]
      have same : result = combined := Option.some.inj (Except.ok.inj (resultActual.symm.trans actual))
      subst result
      refine ⟨?_, (SourceCurrentEqualityNormalizationFixed.invariants _ (fixed outputs payload)).2.2.2⟩
      intro paths member
      apply covers outputs payload paths
      apply List.mem_append.mpr
      apply Or.inr
      rw [ownClasses]
      exact ownSelected paths member

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}

/-- The same selected owner row forces a distinct pair in its actual combined payload. -/
theorem required_pair
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (writerInventory preparedInventory : Inventory)
    {row : Row} {ownerEntry ownerDepth ownerFree} {ownerRows : List Row} {index : Nat}
    (member : row ∈ ownerRows)
    {writer : Checked width} {loaded : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula}
    {inherited own : EqValue} {records kept : List Record}
    (precheckReceipt : SourceCurrentAllocatedPrecheck.Receipt formulas solver writerInventory row.entry.key.constraint
      loaded inherited writer own (.classes records))
    {budget : Nat} {scanned prepared after : Checked width} {fourth savedFourth : Fourth}
    {trace : Scan budget source reaches row.children (records.map SourceEqualityClassOrder.Record.paths)
      (SourceCurrentAllocatedPrecheck.state writer loaded inherited) fourth none
      (kept.map SourceEqualityClassOrder.Record.paths) scanned savedFourth}
    (retained : Retained trace records kept) (nonempty : kept ≠ [])
    {preparedValues results : List Node}
    (required : SourceCurrentConjunctionRequired.Receipt formulas solver preparedInventory
      (kept.map SourceEqualityClassOrder.Record.paths) row.children preparedValues scanned prepared)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady scanned.native.machine.heap)
    (normal : SourceCurrentRequiredUnionNormal.UnionNormal scanned.native.machine.heap)
    (costs : InternedFreshOrdinaryCostHeap.Heap scanned.native.machine.heap)
    (available : Values scanned.native.machine.heap row.children)
    (primary : ∀ record ∈ kept, EndpointStatefulGateTrace.ClassTrace source reaches row.children record.paths
      scanned.native.machine.heap false scanned.native.machine.heap)
    (current : SourceCurrentConstrainedCapCurrentNative.At Plain scanned)
    (supported : SourceCurrentNativeRequestPositivePositions.Support scanned.native.machine.heap scanned.native)
    (causal : History empty scanned.native.machine.heap)
    {memo saved : Memo} {memos final : Memos}
    {actual : Pass kept preparedValues prepared memo results after saved}
    (reads : PassReads formulas solver actual memos final)
    (physical : SourceCurrentMemoMergeEffects.Stored scanned.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers
      (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : EndpointMemoGateTrace.Valid prepared.native.machine.heap memos)
    (merged : SourceCurrentConstrainedCapMemoMerge.Stored Plain memo)
    (positiveMemo : SourceCurrentMergePositivePosition.Support memo)
    (found : results[index]? = some (.node ownerEntry ownerRows ownerDepth ownerFree))
    (outerBefore : Operations) (outerValid : SourceEqualityConstraintMemoAllocation.Valid outerBefore)
    (inheritedReady : SourceEqualityConstraintAllocation.Ready outerBefore.constraints inherited)
    (field : SourceCurrentConjunctionEquality.FieldAvailable outerBefore row.entry.key.constraint)
    (combined : EqValue)
    (outerPrefix : (SourceCurrentAllocatedInheritedPrefix.run row.entry.key.constraint inherited outerBefore).1 =
      .ok (some combined))
    (outputs : List Record) (payload : combined.payload = some outputs) :
    SourceMemoGate.plain row.entry.key.constraint = false ∧
      EqualityNormalize.Covers (kept.map SourceEqualityClassOrder.Record.paths) (outputs.map SourceEqualityClassOrder.Record.paths) ∧
      EqualityNormalize.congruenceStep (outputs.map SourceEqualityClassOrder.Record.paths) = some (outputs.map SourceEqualityClassOrder.Record.paths) ∧
      ∃ paths ∈ outputs.map SourceEqualityClassOrder.Record.paths, ∃ left right,
        index::left ∈ paths ∧ index::right ∈ paths ∧ left ≠ right := by
  obtain ⟨_proper, raw, _rawRead, sourceClasses, order, recordFields⟩ := precheckReceipt.classes records rfl
  have retainedFields := retained.fields
  have nonplain : SourceMemoGate.plain row.entry.key.constraint = false := by
    apply Bool.eq_false_iff.mpr
    intro plain
    have ownEmpty : SourceCompactGuards.sourceEqualities row.entry.key.constraint = some [] := by
      simpa only [SourceMemoGate.plain, Bool.and_eq_true, decide_eq_true_eq] using
        (Bool.and_eq_true_iff.mp plain).1
    have rawEmpty : raw = [] := List.map_eq_nil_iff.mp
      (Option.some.inj (sourceClasses.symm.trans ownEmpty))
    have recordsEmpty : records = [] := by
      rw [order, rawEmpty]
      rfl
    have keptEmpty : kept = [] := List.sublist_nil.mp (recordsEmpty ▸ retainedFields.1)
    exact nonempty keptEmpty
  have ownSelected : ∀ paths ∈ kept.map SourceEqualityClassOrder.Record.paths,
      paths ∈ (SourceCompactGuards.sourceEqualities row.entry.key.constraint).getD [] := by
    intro paths chosen
    obtain ⟨record, member, rfl⟩ := List.mem_map.mp chosen
    have included : record ∈ records := retainedFields.1.subset member
    have rawMember : record ∈ raw := (SourceEqualityClassOrder.ordered_perm raw).mem_iff.mp
      (by simpa only [order] using included)
    rw [sourceClasses]
    exact List.mem_map.mpr ⟨record, rawMember, rfl⟩
  obtain ⟨coveredFamily, fixed⟩ := prefix_family row.entry.key.constraint inherited outerBefore
    outerValid inheritedReady field combined outerPrefix outputs payload (kept.map SourceEqualityClassOrder.Record.paths) ownSelected
  have coherent : ∀ record ∈ kept, SourceEqualityClassOrder.Coherent record := by
    intro record member
    exact (recordFields record (retainedFields.1.subset member)).1
  have active : ∀ record ∈ kept, EqualityNormalize.Nontrivial record.paths := by
    intro record member
    exact (recordFields record (retainedFields.1.subset member)).2.2
  have gates : ∀ paths ∈ kept.map SourceEqualityClassOrder.Record.paths,
      EndpointStatefulGateTrace.ClassTrace source reaches row.children paths
        scanned.native.machine.heap false scanned.native.machine.heap := by
    intro paths selected
    obtain ⟨record, member, rfl⟩ := List.mem_map.mp selected
    exact primary record member
  obtain ⟨_next, _receipt, _currentAfter, _mergedAfter, _corridors,
      _supportedAfter, _causalAfter, _positiveAfter, back⟩ :=
    SourceCurrentRequiredPositiveChronology.pass formulas solver preparedInventory required semantic normal
      costs available gates current supported causal kept rfl coherent active reads physical covered valid merged positiveMemo
  refine ⟨nonplain, coveredFamily, fixed, ?_⟩
  apply SourceCurrentPositiveOwnerPair.same_child_pair fixed index row member nonplain
  intro q positive
  obtain ⟨inputIndex, originalPath, original, originalFound, originalPositive, related⟩ :=
    back index (.node ownerEntry ownerRows ownerDepth ownerFree) found q positive
  exact ⟨inputIndex, originalPath, original, originalFound, originalPositive, rel_covers coveredFamily related⟩

end MicroCFTA.SourceCurrentActualOwnerPair

set_option linter.all true
set_option maxRecDepth 16384
set_option maxHeartbeats 0
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.SourceCurrentActualOwnerPair.required_pair
#print MicroCFTA.SourceCurrentActualOwnerPair.required_pair
#print axioms MicroCFTA.SourceCurrentActualOwnerPair.required_pair
