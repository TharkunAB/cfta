import MicroCFTA.SourceCurrentAllocatedNativeRowsPhysicalReadback
import MicroCFTA.InternedOrderedDiagonalProduct
import MicroCFTA.SourceCurrentAllocatedNativeRequestResults

/-!
# Canonical products from actual ordered edge queries

The actual physical trace supplies each child query and its resident result.
Exact smaller-query laws identify diagonal rows and discarded sentinel rows.
The complete scan then gives the ordered transformed source rows.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeDiagonalProductReadback
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open InternedStoredSubstitution (input)
open InternedStoredSubstitutionRebind (replacement)
open SourceRecursiveIntersectionControl (repeatedValue)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "Pair" => EdgeValue Symbol Guard × EdgeValue Symbol Guard
variable {width : Nat}

set_option autoImplicit false

/-- The complete physical scan derives the exact canonical diagonal product from smaller query laws. -/
theorem diagonal_product_of_smaller_queries
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (sourceName cutoffLeft cutoffRight : Nat) (domain : Interned DomainKey)
    (sources : List (EdgeValue Symbol Guard))
    (before after : Checked width) (fuel traceFuel : Nat) (result : Value Symbol Guard)
    (live : ∀ source ∈ sources,
      (source.children.map (input (replacement (.interned sourceName)
        (repeatedValue (SourceRecursiveIntersectionControl.pair cutoffLeft cutoffRight))))).any
          (fun child => child.referenceOf == .empty) = false)
    (physical : Physical before.native)
    (done : execute fuel (.code (compileRows domain sources sources)) before = .done result after)
    (actual : Trace traceFuel (.code (compileRows domain sources sources)) before (.code (.pure result)) after)
    (children : ∀ stepsBefore childFuel, stepsBefore + childFuel < fuel → childFuel < fuel →
      ∀ pair ∈ pairs sources sources,
      ∀ (next : EdgeValue Symbol Guard → Code Symbol Guard (Value Symbol Guard))
        (first last : Checked width) (row : EdgeValue Symbol Guard),
      Steps stepsBefore (.code (compileRows domain sources sources)) before
        (.code ((requestEdge domain pair.1 pair.2).bind next)) first →
      Physical first.native →
      execute childFuel (.code (requestEdge domain pair.1 pair.2)) first = .done row last →
      (pair.1 = pair.2 →
        row.children = pair.1.children.map (input (replacement (.interned sourceName)
          (repeatedValue (SourceRecursiveIntersectionControl.pair cutoffLeft cutoffRight)))) ∧
        row.entry.key = ⟨pair.1.entry.key.symbol,
          (pair.1.children.map (input (replacement (.interned sourceName)
            (repeatedValue (SourceRecursiveIntersectionControl.pair cutoffLeft cutoffRight))))).map Value.referenceOf,
          top⟩) ∧
      (pair.1 ≠ pair.2 → row.children = [.empty])) :
    ∃ (products rawRows : List (EdgeValue Symbol Guard)) (middle : Checked width) (count : Nat),
      count + 1 < fuel ∧
      All₂ (fun (source : EdgeValue Symbol Guard) target =>
        target.children = source.children.map (input (replacement (.interned sourceName)
          (repeatedValue (SourceRecursiveIntersectionControl.pair cutoffLeft cutoffRight)))) ∧
        target.entry.key = ⟨source.entry.key.symbol,
          (source.children.map (input (replacement (.interned sourceName)
            (repeatedValue (SourceRecursiveIntersectionControl.pair cutoffLeft cutoffRight))))).map Value.referenceOf,
          top⟩) sources products ∧
      (∀ row ∈ products, row ∈ rawRows) ∧
      (∀ row ∈ products, EdgeResident middle.native.machine.heap row) ∧
      Trace count (.code (compileRows domain sources sources)) before
        (.code (.work (makeNode rawRows) .pure)) middle ∧
      result = (run (makeNode rawRows) middle.native.machine.heap).1 ∧
      after = {middle with native := advance middle.native {middle.native.machine with heap :=
        (run (makeNode rawRows) middle.native.machine.heap).2}} ∧
      canonicalEdges (surviving rawRows) = canonicalEdges products ∧
      nodeEdges result = canonicalEdges products ∧
      result.free = childFree ((canonicalEdges products).flatMap EdgeValue.children) ∧
      Physical middle.native ∧ Extension before.native.machine middle.native.machine ∧
      Physical after.native ∧ Extension before.native.machine after.native.machine ∧
      Available after.native.machine.heap result ∧
      (∀ row ∈ products, EdgeResident after.native.machine.heap row) := by
  let rewrite := input (replacement (.interned sourceName)
    (repeatedValue (SourceRecursiveIntersectionControl.pair cutoffLeft cutoffRight)))
  let relation : EdgeValue Symbol Guard → EdgeValue Symbol Guard → Prop := fun source target =>
    target.children = source.children.map rewrite ∧
      target.entry.key = ⟨source.entry.key.symbol, (source.children.map rewrite).map Value.referenceOf, top⟩
  let rowLaw : Pair → EdgeValue Symbol Guard → Prop := fun pair row =>
    (pair.1 = pair.2 → relation pair.1 row) ∧ (pair.1 ≠ pair.2 → row.children = [.empty])
  have checked := SourceCurrentAllocatedNativeRowsPhysicalReadback.compile_rows_physical_readback_of_smaller_edges
    domain sources sources before after fuel traceFuel result rowLaw physical done actual
    (by
      intro stepsBefore childFuel room smaller pair member next first last row origin firstPhysical childDone
      have law := children stepsBefore childFuel room smaller pair member next first last row
        origin firstPhysical childDone
      obtain ⟨steps, _stepBound, raw⟩ := done_trace childFuel _ first last row childDone
      have appended := raw.bind _ _ _ _ _ next
      obtain ⟨_extra, _prefixCount, _prefixPhysical, tail⟩ :=
        SourceCurrentAllocatedNativeOpenUniverseRowPhysicalReadback.physical_prefix origin actual
      obtain ⟨_remaining, _queryCount, boundPhysical, _tailPhysical⟩ :=
        SourceCurrentAllocatedNativeOpenUniverseRowPhysicalReadback.physical_prefix appended tail
      have queryPhysical := SourceCurrentHereditaryNativePhysicalSplit.unbind raw next boundPhysical
      have resident := SourceCurrentAllocatedNativeRequestResults.edge_result steps
        ⟨domain, pair.1, pair.2⟩ first last row firstPhysical queryPhysical
      exact ⟨law, resident⟩)
  obtain ⟨rawRows, middle, count, bounded, _walked, ordered, middlePhysical, middleExtension,
      resident, throughWork, resultEq, afterEq, edgesEq, freeEq, afterPhysical, afterExtension,
      available, afterResident⟩ := checked
  have functional : ∀ source ∈ sources, ∀ first ∈ rawRows, ∀ second ∈ rawRows,
      relation source first → relation source second → first = second := by
    intro source _sourceIn first firstIn second secondIn firstRead secondRead
    have keys : first.entry.key = second.entry.key := firstRead.2.trans secondRead.2.symm
    apply Option.some.inj
    calc
      some first = middle.native.machine.heap.edgeRecords first.entry.key := (resident first firstIn).symm
      _ = middle.native.machine.heap.edgeRecords second.entry.key := congrArg _ keys
      _ = some second := resident second secondIn
  have liveRows : ∀ source ∈ sources, ∀ target ∈ rawRows,
      relation source target → target ∈ surviving rawRows := by
    intro source sourceIn target targetIn readback
    apply List.mem_filter.mpr
    refine ⟨targetIn, ?_⟩
    rw [readback.1]
    simp only [rewrite, live source sourceIn, Bool.not_false]
  obtain ⟨products, aligned, retained, productResident, _sameMembers, canonical⟩ :=
    InternedOrderedDiagonalProduct.ordered_diagonal_selection middle.native.machine.heap
      middlePhysical.machine.1 sources rawRows relation resident ordered functional liveRows
  refine ⟨products, rawRows, middle, count, bounded, aligned, retained, productResident,
    throughWork, resultEq, afterEq, canonical, edgesEq.trans canonical, ?_, middlePhysical,
    middleExtension, afterPhysical, afterExtension, available, ?_⟩
  · simpa only [canonical] using freeEq
  · intro row member
    exact afterResident row (retained row member)

end MicroCFTA.SourceCurrentAllocatedNativeDiagonalProductReadback
