import MicroCFTA.SourceCurrentConstrainedCapSeededForecast
import MicroCFTA.SourceCurrentSecondaryProjectionComplete
import MicroCFTA.SourceCurrentConstrainedCapOperandFrame
import MicroCFTA.SourceCurrentConstrainedCapProjectionGuard
import MicroCFTA.SourceCurrentAllocatedSeededMemos
import MicroCFTA.SourceCurrentAllocatedSeededWorkerStability

/-!
# Initial numeric supported open projections for seeded queries

Only original selected paths supply closure support. Recursive heads use
same-heap warm support, while unrelated ordinary children can stay open.
The computed envelope preserves exact projection graphs and returned heaps.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapSeededProjection
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityProjectionGraph
open SourceCurrentSecondaryProjectionSupport (Support)
open SourceCurrentSecondaryProjectionComplete (ForestSupport)
open SourceCurrentConstrainedCapSeededForecast (nodeBound forestBound)
open SourceCurrentMemoMergeResourceControl (Fits)
open SourceCurrentProjectionNumericReplay (ProjectReady RowsReady ForestReady)
open SourceCurrentProjectionNumericControl (ordinary rowsStep rowsBound)
open SourceCurrentOpenRowReadResources (readFuel)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

private theorem select_natural (values : List A) (index : Nat) : select values (Int.ofNat index) = values[index]? := by
  simp only [select, Int.ofNat_eq_natCast]
  rw [ite_eq_right (Int.not_lt.mpr (Int.natCast_nonneg index))]
  rfl
private theorem old_read_le (resource : Nat) : SourceCurrentProjectionUnionResources.readFuel resource ≤ readFuel resource := by
  unfold readFuel
  omega

private theorem rows_bound (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (path : EqualityNormalize.Path) (index : Nat) (child : Nat → Nat)
    (childBound : ∀ {value result : Value Symbol Guard} {before after : State Symbol Guard}
      (actual : Project (path.map Int.ofNat) value before result after) (resource : Nat),
      SemanticReady before → CostHeap before → Available before value → Grows anchor before →
      Support unconstrained anchor path value → Fits resource before →
      Fits (child resource) after ∧ ProjectReady (readFuel (child resource)) actual)
    {edges : List (EdgeValue Symbol Guard)} {before after : State Symbol Guard} {values : List (Value Symbol Guard)}
    (actual : ProjectRows (path.map Int.ofNat) (Int.ofNat index) edges before values after) (resource : Nat)
    (semantic : SemanticReady before) (costs : CostHeap before) (resident : Edges before edges)
    (growth : Grows anchor before)
    (support : ∀ edge ∈ edges, ∀ value, edge.children[index]? = some value → Support unconstrained anchor path value)
    (fits : Fits resource before) :
    Fits (rowsBound child edges.length resource) after ∧
      RowsReady (readFuel (rowsBound child edges.length resource)) actual ∧ values.length ≤ edges.length := by
  induction edges generalizing before after values resource with
  | nil => cases actual; exact ⟨fits, .nil _ _ _, Nat.le_refl _⟩
  | cons edge edges ih =>
      cases actual with
      | missing absent rest =>
          have tail := ih rest resource semantic costs
            (fun row member => resident row (List.mem_cons_of_mem _ member)) growth
            (fun row member => support row (List.mem_cons_of_mem _ member)) fits
          have increase := SourceCurrentProjectionNumericControl.rowsBound_count_mono child (Nat.le_succ edges.length) resource
          exact ⟨tail.1.mono increase, .missing absent (tail.2.1.mono (SourceCurrentOpenRowReadResources.readFuel_mono increase)),
            Nat.le_trans tail.2.2 (by simp only [List.length_cons]; omega)⟩
      | selected found first rest =>
          have available := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge
            (resident edge List.mem_cons_self) _ (select_member found)
          have firstBound := childBound first resource semantic costs available growth
            (support edge List.mem_cons_self _ (by simpa only [select_natural] using found)) fits
          have effects := SourceEqualityProjectionCosts.project_effects first semantic costs available
          have tail := ih rest (rowsStep child resource) effects.2.1 effects.2.2.1
            (fun row member => InternedEdgeResidency.edge_grows before _ effects.1.growth row
              (resident row (List.mem_cons_of_mem _ member))) (grows_trans growth effects.1.growth)
            (fun row member => support row (List.mem_cons_of_mem _ member))
            (firstBound.1.mono (SourceCurrentProjectionNumericControl.rowsStep_child child resource))
          have increase : child resource ≤ rowsBound child (edge :: edges).length resource :=
            SourceCurrentProjectionNumericControl.child_le_rowsBound child (by simp only [List.length_cons]; omega)
          exact ⟨tail.1, .selected found
            (firstBound.2.mono (SourceCurrentOpenRowReadResources.readFuel_mono increase)) tail.2.1,
            by simp only [List.length_cons]; omega⟩

private theorem ordinary_bound (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : InternedFreshOrdinaryMemoGateTrace.Ready anchor)
    (path : EqualityNormalize.Path) (index : Nat)
    (childBound : ∀ {value result : Value Symbol Guard} {before after : State Symbol Guard}
      (actual : Project (path.map Int.ofNat) value before result after) (resource : Nat),
      SemanticReady before → CostHeap before → Available before value → Grows anchor before →
      Support unconstrained anchor path value → Fits resource before →
      Fits (nodeBound path.length resource) after ∧ ProjectReady (readFuel (nodeBound path.length resource)) actual)
    {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : Project ((index :: path).map Int.ofNat) value before result after) (resource : Nat)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value)
    (growth : Grows anchor before)
    (support : ∀ edge ∈ InternedEdgeResidency.nodeEdges value, ∀ child, edge.children[index]? = some child →
      Support unconstrained anchor path child)
    (fits : Fits resource before) (isOrdinary : Ordinary value) :
    Fits (ordinary (nodeBound path.length) resource) after ∧
      ProjectReady (readFuel (ordinary (nodeBound path.length) resource)) actual := by
  cases actual with
  | empty =>
      exact ⟨fits.mono (SourceCurrentProjectionNumericControl.ordinary_ge _ _), .empty _ _ _⟩
  | @ordinary path index edges before values middle result after entry depth free rows joined =>
      have facts := semantic.ready.semantic.1.normal.facts
      have resident := InternedEdgeResidency.resident_edges before facts.linked _ available.resident
      have first := rows_bound unconstrained anchor _ _ (nodeBound path.length) childBound rows resource semantic costs resident growth support fits
      have mass := InternedValueMassHeap.available before fits.stored (.node entry edges depth free) available
      have length : edges.length ≤ resource := Nat.le_trans (InternedStoredEncodingWidth.edges_length edges)
        (by simp only [InternedValueMass.value] at mass; omega)
      have padded := SourceCurrentProjectionNumericControl.rowsBound_count_mono (nodeBound path.length) length resource
      have physical := SourceEqualityProjectionCosts.rows_effects rows semantic costs resident
      have closed := SourceCurrentSecondaryProjectionComplete.rows_verified unconstrained anchor anchorSemantic anchorReady
        rows semantic resident growth support
      have last := SourceCurrentProjectionUnionResources.union joined resource (rowsBound (nodeBound path.length) resource resource)
        physical.2.1 physical.2.2.1 closed.2.2.1 closed.2.2.2 (first.1.mono padded) (Nat.le_trans first.2.2 length)
      have allRows := Nat.le_trans padded (SourceCurrentProjectionNumericControl.rowsBound_le_ordinary _ resource)
      exact ⟨last.2.1, .ordinary (first.2.1.mono (SourceCurrentOpenRowReadResources.readFuel_mono allRows))
        (last.2.2.2.2.mono (old_read_le _))⟩
  | recursive recursive head body => cases value <;> cases recursive <;> cases isOrdinary

/-- Anchored selected support bounds the actual open node projection and every demanded reader. -/
theorem node_bound (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : InternedFreshOrdinaryMemoGateTrace.Ready anchor)
    (path : EqualityNormalize.Path) {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : Project (path.map Int.ofNat) value before result after) (resource : Nat)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value)
    (growth : Grows anchor before) (support : Support unconstrained anchor path value) (fits : Fits resource before) :
    Fits (nodeBound path.length resource) after ∧ ProjectReady (readFuel (nodeBound path.length resource)) actual := by
  induction path generalizing value result before after resource with
  | nil => cases actual; exact ⟨fits.mono (SourceCurrentConstrainedCapSeededForecast.nodeBound_ge _ _), .root _ _⟩
  | cons index path ih =>
      cases actual with
      | empty => exact ⟨fits.mono (SourceCurrentConstrainedCapSeededForecast.nodeBound_ge _ _), .empty _ _ _⟩
      | ordinary rows joined =>
          have selected := fun edge member child found =>
            SourceCurrentSecondaryProjectionSupport.ordinary_selected_support support anchorSemantic semantic available edge member child found
          have first := ordinary_bound unconstrained anchor anchorSemantic anchorReady path index
            (fun actual resource => ih actual resource) (.ordinary rows joined) resource semantic costs available growth selected fits trivial
          have increase := SourceCurrentConstrainedCapSeededForecast.ordinary_le_nodeBound path.length resource
          exact ⟨first.1.mono increase, first.2.mono (SourceCurrentOpenRowReadResources.readFuel_mono increase)⟩
      | recursive recursive head body =>
          rename_i exposed middle
          have warm := SourceCurrentSecondaryProjectionSupport.support_warm_head support anchorSemantic before growth
          have first := SourceCurrentOpenRowReadResources.head head resource semantic costs available warm fits
          have physical := SourceEqualityProjectionCosts.head_effects head semantic costs available
          have selected : ∀ edge ∈ InternedEdgeResidency.nodeEdges exposed, ∀ child, edge.children[index]? = some child →
              Support unconstrained anchor path child := by
            rcases support with closed | ⟨known, gate⟩
            · have verified := head.verified semantic.ready available closed
              cases exposed with
              | empty => intro edge member; cases member
              | node own rows depth free =>
                  intro edge member child found
                  exact Or.inl (MergedColdReaderClosed.node_children_closed _ physical.2.1.ready.semantic.1.normal.facts
                    own rows depth free physical.2.2.2 verified.2.2.1 edge member child (List.mem_of_getElem? found))
              | reference | union | mu => cases verified.2.2.2
            · exact SourceCurrentSecondaryProjectionSupport.head_selected_support gate anchorSemantic known semantic available growth head
          have last := ordinary_bound unconstrained anchor anchorSemantic anchorReady path index
            (fun actual resource => ih actual resource) body (SourceCurrentOpenRowReadResources.headGrowth resource)
            physical.2.1 physical.2.2.1 physical.2.2.2 (grows_trans growth physical.1.growth) selected first.2.1 first.2.2.2.1
          have increase := SourceCurrentConstrainedCapSeededForecast.head_le_nodeBound path.length resource
          exact ⟨last.1, .recursive recursive (first.2.2.2.2.mono (SourceCurrentOpenRowReadResources.readFuel_mono increase)) last.2⟩

/-- Root or selected forest projection retains the original anchored support and exact returned heap. -/
theorem forest_bound (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : InternedFreshOrdinaryMemoGateTrace.Ready anchor)
    (path : EqualityNormalize.Path) {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : State Symbol Guard} (actual : Forest (path.map Int.ofNat) values before result after) (resource : Nat)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
    (growth : Grows anchor before) (support : ForestSupport unconstrained anchor path values) (fits : Fits resource before) :
    Fits (forestBound (path.map Int.ofNat) values.length resource) after ∧
      ForestReady (readFuel (forestBound (path.map Int.ofNat) values.length resource)) actual := by
  cases path with
  | nil =>
      cases actual with
      | root joined =>
          have first := SourceCurrentProjectionUnionResources.union joined values.length resource semantic costs available support fits (Nat.le_refl _)
          exact ⟨first.2.1, .root (first.2.2.2.2.mono (old_read_le _))⟩
  | cons index path =>
      cases actual with
      | missing absent => exact ⟨fits.mono (SourceCurrentConstrainedCapSeededForecast.nodeBound_ge _ _), .missing absent _ _⟩
      | selected found body =>
          have selected := support _ (by simpa only [select_natural] using found)
          have first := node_bound unconstrained anchor anchorSemantic anchorReady path body resource semantic costs
            (available _ (select_member found)) growth selected fits
          simpa only [List.map_cons, List.length_map, SourceCurrentConstrainedCapSeededForecast.forestBound] using
            And.intro first.1 (ForestReady.selected found first.2)

local notation "SourceSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "SourceGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Initial selected support constructs the exact checked projection and its numeric replay. -/
theorem complete [DecidableEq SourceSymbol]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : SourceCurrentAllocatedNativeInventoryState.Inventory)
    (unconstrained : Value SourceSymbol SourceGuard → Bool) (anchor : State SourceSymbol SourceGuard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : InternedFreshOrdinaryMemoGateTrace.Ready anchor)
    (path : List Int) (values : List (Value SourceSymbol SourceGuard))
    (before : SourceEqualityNativeDemand.State width)
    (profile : SourceCurrentAllocatedNativeResourceForecast.Profile)
    (frame : SourceCurrentConstrainedCapGeneratedQueryResources.Frame formulas solver inventory before)
    (fits : SourceCurrentConstrainedCapGeneratedQueryResources.Fits profile before)
    (available : Values before.native.machine.heap values) (growth : Grows anchor before.native.machine.heap)
    (supported : SourceCurrentSecondaryProjectionScoped.PathSupport unconstrained anchor path values)
    (memos : EndpointMemoGateTrace.Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    ∃ result after final, ∃ actual : SourceCurrentAllocatedSeededQuery.Operand path values before result after,
      SourceCurrentAllocatedSeededMemos.OperandReads actual memos final ∧
      SourceCurrentConstrainedCapGeneratedQueryResources.Frame formulas solver inventory after ∧
      SourceCurrentConstrainedCapGeneratedQueryResources.Fits
        (SourceCurrentConstrainedCapSeededForecast.projectionProfile path values.length profile) after ∧
      SourceCurrentConjunctionRowsAllocation.Effects (SourceCurrentAllocatedNativeEffects.physical before)
        (SourceCurrentAllocatedNativeEffects.physical after) ∧
      SourceRecursiveIntersectionKernel.Extension before.native.machine after.native.machine ∧
      Available after.native.machine.heap result ∧ result.free = [] ∧
      SourceCurrentSubsumesQueryMemos.Effect before.native.machine.heap after.native.machine.heap memos final ∧
      SourceCurrentAllocatedSeededWorker.operand
        (SourceCurrentConstrainedCapSeededForecast.projectionFuel path values.length profile)
        (SourceCurrentConstrainedCapSeededForecast.projectionFuel path values.length profile) path values before =
          .done result after := by
  rcases supported with ⟨natural, rfl, supported⟩
  have physicalReady := SourceCurrentAllocatedConjunctionMemo.ready before frame.ready.good frame.ready.semantic frame.ready.costs
  obtain ⟨result, heap, projected, effects, resident, closed⟩ := SourceCurrentAllocatedGateFields.forest_complete
    unconstrained anchor anchorSemantic anchorReady natural values (SourceCurrentAllocatedNativeEffects.physical before)
    physicalReady available growth supported
  let after := SourceCurrentAllocatedQueryMemo.advancePhysical before ⟨heap, before.operations⟩
  have extension := SourceCurrentAllocatedQueryMemo.advance_extension before ⟨heap, before.operations⟩ effects
  have guards := SourceCurrentConstrainedCapProjectionGuard.forest
    SourceCurrentConstrainedCapCheckedJointClosed.Plain projected frame.ready.semantic frame.ready.costs available frame.context.guards
  have finalFrame : SourceCurrentConstrainedCapGeneratedQueryResources.Frame formulas solver inventory after :=
    SourceCurrentConstrainedCapOperandFrame.advance frame
      (SourceCurrentConjunctionClassScan.advance_ready before ⟨heap, before.operations⟩ frame.ready effects)
      extension rfl rfl guards
  have initialFits : Fits (SourceCurrentConstrainedCapSeededForecast.scalar profile) before.native.machine.heap :=
    ⟨fits.stored.mono (SourceCurrentConstrainedCapSeededForecast.scalar_mass profile),
      Nat.le_trans fits.nodes (SourceCurrentConstrainedCapSeededForecast.scalar_nodes profile),
      Nat.le_trans fits.edges (SourceCurrentConstrainedCapSeededForecast.scalar_edges profile), Nat.zero_le _⟩
  have bounded := forest_bound unconstrained anchor anchorSemantic anchorReady natural projected _
    frame.ready.semantic frame.ready.costs available growth supported initialFits
  obtain ⟨final, reads, finalValid, retained⟩ := SourceEqualityQueryGlobalMemos.forest_memos projected
    frame.ready.semantic frame.ready.costs available memos valid
  refine ⟨result, after, final, .force result heap projected, .force reads, finalFrame,
    ⟨bounded.1.nodes, bounded.1.edges, fits.domains, bounded.1.stored⟩, effects, extension, resident, closed,
    ⟨effects.keeps, effects.ready.semantic, effects.ready.costs, finalValid, retained, reads.2⟩, ?_⟩
  have replay := SourceCurrentProjectionNumericReplay.forest_replay bounded.2
    (SourceCurrentConstrainedCapSeededForecast.projectionFuel (natural.map Int.ofNat) values.length profile)
    (SourceCurrentConstrainedCapSeededForecast.projectionFuel (natural.map Int.ofNat) values.length profile)
    (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  simp only [SourceCurrentAllocatedSeededWorker.operand, replay]

end MicroCFTA.SourceCurrentConstrainedCapSeededProjection
