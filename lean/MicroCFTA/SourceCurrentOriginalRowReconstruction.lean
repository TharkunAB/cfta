import MicroCFTA.SourceCurrentOriginalRowGroupChain
import MicroCFTA.SourceEqualityPartialNodeRebuild

namespace MicroCFTA.SourceCurrentOriginalRowReconstruction
open Cache Language IntersectSchedule InternedConstructorTemplates InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionInputView InternedProbeProvenance
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Edge" => EdgeValue Symbol Guard
local notation "Wrapper" => SourceCurrentSameSymbolEdgeControl.State
local notation "Stable" => SourceCurrentSameSymbolEdgeStable.Stable
local notation "NativeIdle" => SourceRecursiveIntersectionNative.Idle
local notation "guardHolds" => (@SourceEqualityPCSGuard.holds FullSyntax.Formula FormulaExecutable.formulaDecidableEq)

/-- Heap growth retains the exact pair memo and its fixed contextual laws. -/
private theorem stable_heap
    {width : Nat} (semanticView : View Symbol) (model : InputMeaning semanticView)
    (ranked : RankedInput semanticView model.valid) (holds : Guard → Term Symbol → Bool)
    (before : Wrapper width) (heap : InternedConstructorTemplates.State Symbol Guard)
    (stable : Stable semanticView model ranked holds before)
    (growth : Grows before.checked.native.machine.heap heap) :
    let after : Wrapper width :=
      { before with checked :=
        { before.checked with native := (SourceRecursiveIntersectionThunks.advance
          before.checked.native { before.checked.native.machine with heap := heap }) } }
    Stable semanticView model ranked holds after := by
  dsimp only
  refine ⟨?_, stable.returned, stable.canonical⟩
  apply FlatMemoThunk.Valid.map _ _ _ _ stable.valid
  intro cell cellGood
  refine ⟨edge_grows _ _ growth _ cellGood.1,
    edge_grows _ _ growth _ cellGood.2.1, ?_⟩
  rcases cell with ⟨_request, status⟩
  cases status with
  | suspended | evaluating => trivial
  | returned value =>
      exact ⟨edge_grows _ _ growth value cellGood.2.2.1, cellGood.2.2.2⟩

/-- Rebuild an original ordinary parent after its actual symbol-group runs. -/
theorem ordinary_complete
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (bits : Nat) (source : InternedConstructorTemplates.State Symbol Guard)
    (facts : InternedNestedFacts.Facts source)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inputModel : InputMeaning (view source (guardHolds formulas solver)))
    (inputRanked : RankedInput (view source (guardHolds formulas solver)) inputModel.valid)
    (parentEntry : Interned InternedBinderProtocol.NodeKey)
    (parentRows : List Edge) (parentDepth : Nat)
    (original : OriginalInput source (inputOf (.node parentEntry parentRows parentDepth [])))
    (available : Available source (.node parentEntry parentRows parentDepth []))
    (admitted : inputModel.valid (inputOf (.node parentEntry parentRows parentDepth [])))
    (entries : List (Symbol × List Edge))
    (iteration : SourceCurrentMergeGrouping.Iteration
      (SourceCurrentPrependGrouping.fromRows (fun edge : Edge => edge.entry.key.symbol)
        parentRows) entries)
    (initialDomains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey)
    (initialValid : Cache.Valid initialDomains)
    (before : Wrapper (bits + 2))
    (stable : Stable (view source (guardHolds formulas solver)) inputModel inputRanked
      (guardHolds formulas solver) before)
    (good : Good before.checked)
    (contextual : SourceCurrentAllocatedNativeContextCache.Contextual
      (view source (guardHolds formulas solver)) inputModel inputRanked
      (guardHolds formulas solver) before.checked.native)
    (semantic : SemanticReady before.checked.native.machine.heap)
    (growth : Grows source before.checked.native.machine.heap)
    (history : Extends source.nodes.issued before.checked.native.machine.heap.nodes.issued)
    (allocations : SourceRecursiveIntersectionDomainAllocation.Trace
      (SourceRecursiveIntersectionSourceInventory.domains source)
      initialDomains before.checked.native.machine.domains)
    (idle : NativeIdle before.checked.native)
    (room : SourceCurrentAllocatedNativeResourceForecast.Room bits
      ⟨source.nodes.next, source.edges.next,
        initialDomains.next + (SourceRecursiveIntersectionSourceInventory.domains source).length, 0⟩) :
    ∃ (fuels : Fin entries.length → Nat) (kept : Fin entries.length → List Edge)
      (states : Fin (entries.length + 1) → Wrapper (bits + 2)),
      let middle := states (Fin.last entries.length)
      let output := (List.ofFn kept).flatten
      let built := run (makeNode output) middle.checked.native.machine.heap
      let after : Wrapper (bits + 2) :=
        { middle with checked :=
          { middle.checked with native := (SourceRecursiveIntersectionThunks.advance
            middle.checked.native { middle.checked.native.machine with heap := built.2 }) } }
      states 0 = before ∧
      (∀ index : Fin entries.length,
        SourceCurrentOriginalRowClusterScan.execute (fuels index)
          (.cluster (entries.get index).2.reverse []) (states index.castSucc) =
          .done (kept index) (states index.succ) ∧
        (∀ edge ∈ kept index, edge ∈ (entries.get index).2.reverse) ∧
        (kept index).length ≤ (entries.get index).2.reverse.length) ∧
      (∀ index : Fin (entries.length + 1),
        Good (states index).checked ∧
        SourceCurrentAllocatedNativeContextCache.Contextual
          (view source (guardHolds formulas solver)) inputModel inputRanked
          (guardHolds formulas solver) (states index).checked.native ∧
        SemanticReady (states index).checked.native.machine.heap ∧
        Grows source (states index).checked.native.machine.heap ∧
        Extends source.nodes.issued (states index).checked.native.machine.heap.nodes.issued ∧
        Stable (view source (guardHolds formulas solver)) inputModel inputRanked
          (guardHolds formulas solver) (states index) ∧
        NativeIdle (states index).checked.native ∧
        SourceRecursiveIntersectionDomainAllocation.Trace
          (SourceRecursiveIntersectionSourceInventory.domains source)
          initialDomains (states index).checked.native.machine.domains) ∧
      SourceEqualityNativeDemand.execute 2 (.code (.work (makeNode output) .pure))
        middle.checked = .done built.1 after.checked ∧
      Good after.checked ∧
      SourceCurrentAllocatedNativeContextCache.Contextual
        (view source (guardHolds formulas solver)) inputModel inputRanked
        (guardHolds formulas solver) after.checked.native ∧
      SemanticReady after.checked.native.machine.heap ∧
      Grows source after.checked.native.machine.heap ∧
      Extends source.nodes.issued after.checked.native.machine.heap.nodes.issued ∧
      Stable (view source (guardHolds formulas solver)) inputModel inputRanked
        (guardHolds formulas solver) after ∧
      NativeIdle after.checked.native ∧
      SourceRecursiveIntersectionDomainAllocation.Trace
        (SourceRecursiveIntersectionSourceInventory.domains source)
        initialDomains after.checked.native.machine.domains ∧
      Extension before.checked.native.machine after.checked.native.machine ∧
      Extends before.memo.table after.memo.table ∧
      FlatMemoThunk.Returned before.memo after.memo ∧
      after.checked.native.nodes = middle.checked.native.nodes ∧
      after.checked.native.edges = middle.checked.native.edges ∧
      after.checked.operations = middle.checked.operations ∧
      after.memo = middle.memo ∧
      after.checked.native.machine.domains = middle.checked.native.machine.domains ∧
      Available after.checked.native.machine.heap built.1 ∧
      SourceEqualityRequiredCache.Ordinary built.1 ∧ built.1.free = [] ∧
      (∀ edge ∈ output, edge ∈ parentRows) ∧ output.length ≤ parentRows.length ∧
      ∀ ambient : InternedGuardedLanguage.Env Symbol, ∀ term : Term Symbol,
        InternedGuardedLanguage.meaning (guardHolds formulas solver) ambient built.1 term ↔
        InternedGuardedLanguage.meaning (guardHolds formulas solver) ambient
          (.node parentEntry parentRows parentDepth []) term := by
  obtain ⟨fuels, kept, states, start, steps, packets, extension, tables, retained,
      members, lengthBound, meaning⟩ :=
    SourceCurrentOriginalRowGroupChain.groups_complete bits source facts formulas solver
      inputModel inputRanked (.node parentEntry parentRows parentDepth [])
      original available rfl admitted entries iteration initialDomains initialValid before
      stable good contextual semantic growth history allocations idle room
  let middle := states (Fin.last entries.length)
  let output := (List.ofFn kept).flatten
  let built := run (makeNode output) middle.checked.native.machine.heap
  let after : Wrapper (bits + 2) :=
    { middle with checked :=
      { middle.checked with native := (SourceRecursiveIntersectionThunks.advance
        middle.checked.native { middle.checked.native.machine with heap := built.2 }) } }
  obtain ⟨midGood, midContextual, midSemantic, midGrowth, midHistory, midStable,
      midIdle, midTrace⟩ := packets (Fin.last entries.length)
  have parentClosed : childFree (parentRows.flatMap EdgeValue.children) = [] := by
    exact (InternedNormalizationFree.node_free source facts.coherent
      parentEntry parentRows parentDepth [] available.resident).symm
  have residentRows : InternedNestedProvenance.Edges middle.checked.native.machine.heap output := by
    intro edge member
    exact edge_grows source _ midGrowth edge
      (resident_edges source facts.linked _ available.resident edge (members edge member))
  have closedRows : MergedColdReaderClosedInputs.ClosedEdges output := by
    intro edge member child childMember
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro reference occurs
    cases (show reference ∈ ([] : List InternedBinderProtocol.Reference) from
      parentClosed ▸ (childFree_member (parentRows.flatMap EdgeValue.children) reference).mpr
        ⟨child, List.mem_flatMap.mpr ⟨edge, members edge member, childMember⟩, occurs⟩)
  have rebuilt : SourceEqualityRequiredCache.Keeps middle.checked.native.machine.heap built.2 ∧
    Available built.2 built.1 ∧ built.1.free = [] ∧ SourceEqualityRequiredCache.Ordinary built.1 := by
    exact SourceEqualityRequiredCache.node output middle.checked.native.machine.heap
      midSemantic.ready residentRows closedRows
  have rebuiltSemantic : SemanticReady built.2 := by
    exact SourceEqualityRequiredSemanticCache.node output middle.checked.native.machine.heap
      midSemantic residentRows closedRows
  have rebuildExtension : Extension middle.checked.native.machine
    { middle.checked.native.machine with heap := built.2 } := by
    exact ⟨rebuilt.1.growth, rebuilt.1.history, extends_refl _⟩
  have rebuiltGood : Good after.checked := by
    refine ⟨SourceCurrentAllocatedNativePhysicalCache.advance_valid middle.checked.native
      midGood.native _ ⟨rebuilt.1.ready.semantic.1.normal.facts, midGood.native.machine.2⟩
      rebuildExtension, rebuilt.1.ready, midGood.operations, ?_⟩
    exact SourceCurrentAllocatedNativeCodeFields.makeNode_heap middle.checked.operations
      output middle.checked.native.machine.heap midGood.fields
  have rawDone : SourceEqualityNativeDemand.execute 2 (.code (.work (makeNode output) .pure))
    middle.checked = .done built.1 after.checked := by
    rfl
  refine ⟨fuels, kept, states, start, steps, packets, rawDone, rebuiltGood,
    SourceCurrentAllocatedNativeContextCache.advance_contextual
      (view source (guardHolds formulas solver)) inputModel inputRanked
      (guardHolds formulas solver) middle.checked.native _ midContextual,
    rebuiltSemantic, grows_trans midGrowth rebuilt.1.growth,
    extends_trans midHistory rebuilt.1.history,
    stable_heap _ _ _ _ middle built.2 midStable rebuilt.1.growth,
    midIdle, midTrace, extension.trans rebuildExtension, tables, retained,
    rfl, rfl, rfl, rfl, rfl, rebuilt.2.1, rebuilt.2.2.2, rebuilt.2.2.1,
    members, lengthBound, ?_⟩
  intro ambient term
  apply (InternedGuardedLanguage.makeNode_exact middle.checked.native.machine.heap
    midGood.native.machine.1 (guardHolds formulas solver) ambient output residentRows term).trans
  apply (show (∃ edge ∈ output, MergedColdInterpretation.EdgeMeaning
      (InternedGuardedLanguage.meaning (guardHolds formulas solver) ambient)
      (guardHolds formulas solver) edge term) ↔
      ∃ edge ∈ output, InternedGuardedLanguage.edgeMeaning
        (guardHolds formulas solver) ambient edge term from
    exists_congr (fun edge => and_congr_right (fun _ =>
      (InternedGuardedLanguage.edgeMeaning_all (guardHolds formulas solver) ambient edge term).symm))).trans
  exact (meaning ambient term).trans
    (SourceEqualityPartialNodeRebuild.node_meaning (guardHolds formulas solver)
      ambient parentEntry parentRows parentDepth [] term).symm

end MicroCFTA.SourceCurrentOriginalRowReconstruction
