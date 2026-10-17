import MicroCFTA.SourceRecursiveIntersectionWorkMass
import MicroCFTA.SourceMergedSelectionNumeric
import MicroCFTA.SourceCurrentMemoMergeMass

/-!
# Current heap control for literal Merge operations

Available inputs bound the exact stored winners of literal constructors.
A separate list-width limit bounds their complete ordered input mass.
Actual selection histories bound all unfolding effects from initial heap
resources. These local transfers do not bound a complete recursive Merge.
-/
namespace MicroCFTA.SourceCurrentMemoMergeResourceControl
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedReaderControl (g)
open SourceMergedComparisonNumeric (comparisonFuel)
open InternedFreshOrdinaryResultMass (inflate)
variable {Symbol Guard : Type}

/-- One scalar bounds both complete payload maps and both issued counters. -/
abbrev Fits (bound : Nat) (heap : State Symbol Guard) : Prop :=
  SourceCurrentAllocatedUnfoldHistory.Fits bound heap

/-- Larger scalar resources retain the same complete heap. -/
theorem Fits.mono {first last : Nat} {heap : State Symbol Guard}
    (fits : Fits first heap) (increase : first ≤ last) : Fits last heap := fits.mono increase

/-- Original issued counters and causal payload mass bound the initial heap. -/
def initialBound (nodes edges mass : Nat) : Nat := max (max nodes edges) mass

/-- Initial causal stored mass needs no future execution to establish scalar control. -/
theorem initial (heap : State Symbol Guard) (mass : Nat) (stored : InternedValueMassHeap.Stored mass heap) :
    Fits (initialBound heap.nodes.next heap.edges.next mass) heap := by
  refine ⟨stored.mono (by unfold initialBound; omega), ?_, ?_, Nat.zero_le _⟩
  · change heap.nodes.next ≤ initialBound heap.nodes.next heap.edges.next mass
    unfold initialBound; omega
  · change heap.edges.next ≤ initialBound heap.nodes.next heap.edges.next mass
    unfold initialBound; omega

/-- One primitive pays one identity and the complete list of bounded payloads. -/
def primitiveGrowth (width bound : Nat) : Nat := max (bound + 1) (inflate width bound)

/-- Every primitive envelope retains the original scalar resources. -/
theorem primitiveGrowth_ge (width bound : Nat) : bound ≤ primitiveGrowth width bound := by
  unfold primitiveGrowth
  omega

/-- Larger literal width and current resources retain the next primitive envelope. -/
theorem primitiveGrowth_mono {firstWidth lastWidth firstBound lastBound : Nat}
    (widths : firstWidth ≤ lastWidth) (bounds : firstBound ≤ lastBound) :
    primitiveGrowth firstWidth firstBound ≤ primitiveGrowth lastWidth lastBound :=
  Nat.max_le_max (Nat.add_le_add_right bounds 1)
    (Nat.le_trans (SourceRecursiveIntersectionWorkMass.inflate_width widths firstBound)
      (InternedFreshOrdinaryResultMass.inflate_mono lastWidth bounds))

/-- Literal available input occurrences bound the complete ordered value-list mass. -/
theorem values_mass {bound width : Nat} {heap : State Symbol Guard} (fits : Fits bound heap)
    (values : List (Value Symbol Guard)) (available : Values heap values) (length : values.length ≤ width) :
    InternedValueMass.values values ≤ width * (1 + bound) :=
  Nat.le_trans (SourceRecursiveIntersectionWorkMass.values_le values bound
    (fun value member => InternedValueMassHeap.available heap fits.stored value (available value member)))
    (Nat.mul_le_mul_right (1 + bound) length)

/-- Literal resident rows bound the complete ordered row-list mass. -/
theorem rows_mass {bound width : Nat} {heap : State Symbol Guard} (fits : Fits bound heap)
    (rows : List (EdgeValue Symbol Guard)) (resident : Edges heap rows) (length : rows.length ≤ width) :
    InternedValueMass.edges rows ≤ width * (1 + bound) :=
  Nat.le_trans (SourceRecursiveIntersectionWorkMass.edges_le rows bound
    (fun row member => InternedValueMassHeap.resident heap fits.stored row (resident row member)))
    (Nat.mul_le_mul_right (1 + bound) length)

private theorem copied_rows (values : List (Value Symbol Guard)) :
    InternedValueMass.edges (values.flatMap nodeEdges) ≤ InternedValueMass.values values := by
  induction values with
  | nil => exact Nat.le_refl _
  | cons value rest ih =>
      have own : InternedValueMass.edges (nodeEdges value) ≤ 1 + InternedValueMass.value value := by
        cases value <;> simp only [nodeEdges, InternedValueMass.edges, InternedValueMass.value] <;> omega
      simp only [List.flatMap_cons, InternedValueMass.edges_append, InternedValueMass.values]
      omega

section Primitives
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Actual edge work bounds its full returned heap and exact keep-first payload. -/
theorem edge (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard))
    (heap : State Symbol Guard) (bound width : Nat) (fits : Fits bound heap)
    (available : Values heap values) (length : values.length ≤ width) :
    Fits (primitiveGrowth width bound) (run (makeEdge symbol guard values) heap).2 ∧
      InternedValueMass.edge (run (makeEdge symbol guard values) heap).1 ≤ primitiveGrowth width bound ∧
      (run (makeEdge symbol guard values) heap).2.nodes.next = heap.nodes.next ∧
      (run (makeEdge symbol guard values) heap).2.edges.next ≤ heap.edges.next + 1 := by
  have actual := SourceRecursiveIntersectionWorkMass.edge symbol guard values heap fits.stored
    (fun value member => InternedValueMassHeap.available heap fits.stored value (available value member))
  have larger : inflate values.length bound ≤ primitiveGrowth width bound :=
    Nat.le_trans (SourceRecursiveIntersectionWorkMass.inflate_width length bound) (Nat.le_max_right _ _)
  refine ⟨⟨actual.1.mono larger, ?_, ?_, Nat.zero_le _⟩, Nat.le_trans actual.2.1 larger, actual.2.2⟩
  · change (run (makeEdge symbol guard values) heap).2.nodes.next ≤ primitiveGrowth width bound
    have old := fits.nodes
    change heap.nodes.next ≤ bound at old
    have retained := primitiveGrowth_ge width bound
    omega
  · change (run (makeEdge symbol guard values) heap).2.edges.next ≤ primitiveGrowth width bound
    have old := fits.edges
    change heap.edges.next ≤ bound at old
    have paid : bound + 1 ≤ primitiveGrowth width bound := Nat.le_max_left _ _
    omega

/-- Actual node work bounds surviving rows, stored winners, and its literal node charge. -/
theorem node (rows : List (EdgeValue Symbol Guard)) (heap : State Symbol Guard) (bound width : Nat)
    (fits : Fits bound heap) (resident : Edges heap rows) (length : rows.length ≤ width) :
    Fits (primitiveGrowth width bound) (run (makeNode rows) heap).2 ∧
      InternedValueMass.value (run (makeNode rows) heap).1 ≤ primitiveGrowth width bound ∧
      (run (makeNode rows) heap).2.nodes.next ≤ heap.nodes.next + 1 ∧
      (run (makeNode rows) heap).2.edges.next = heap.edges.next := by
  have actual := SourceRecursiveIntersectionWorkMass.node rows heap fits.stored
    (fun row member => InternedValueMassHeap.resident heap fits.stored row (resident row member))
  have larger : inflate rows.length bound ≤ primitiveGrowth width bound :=
    Nat.le_trans (SourceRecursiveIntersectionWorkMass.inflate_width length bound) (Nat.le_max_right _ _)
  refine ⟨⟨actual.1.mono larger, ?_, ?_, Nat.zero_le _⟩, Nat.le_trans actual.2.1 larger, actual.2.2⟩
  · change (run (makeNode rows) heap).2.nodes.next ≤ primitiveGrowth width bound
    have old := fits.nodes
    change heap.nodes.next ≤ bound at old
    have paid : bound + 1 ≤ primitiveGrowth width bound := Nat.le_max_left _ _
    omega
  · change (run (makeNode rows) heap).2.edges.next ≤ primitiveGrowth width bound
    have old := fits.edges
    change heap.edges.next ≤ bound at old
    have retained := primitiveGrowth_ge width bound
    omega

/-- Full union work includes normalized members and either literal final constructor path. -/
theorem union (values : List (Value Symbol Guard)) (heap : State Symbol Guard) (bound width : Nat)
    (fits : Fits bound heap) (available : Values heap values) (length : values.length ≤ width) :
    Fits (primitiveGrowth width bound) (run (makeUnion values) heap).2 ∧
      InternedValueMass.value (run (makeUnion values) heap).1 ≤ primitiveGrowth width bound ∧
      (run (makeUnion values) heap).2.nodes.next ≤ heap.nodes.next + 1 ∧
      (run (makeUnion values) heap).2.edges.next = heap.edges.next := by
  have actual := SourceRecursiveIntersectionWorkMass.union values heap fits.stored
    (fun value member => InternedValueMassHeap.available heap fits.stored value (available value member))
  have larger : inflate values.length bound ≤ primitiveGrowth width bound :=
    Nat.le_trans (SourceRecursiveIntersectionWorkMass.inflate_width length bound) (Nat.le_max_right _ _)
  refine ⟨⟨actual.1.mono larger, ?_, ?_, Nat.zero_le _⟩, Nat.le_trans actual.2.1 larger, actual.2.2⟩
  · change (run (makeUnion values) heap).2.nodes.next ≤ primitiveGrowth width bound
    have old := fits.nodes
    change heap.nodes.next ≤ bound at old
    have paid : bound + 1 ≤ primitiveGrowth width bound := Nat.le_max_left _ _
    omega
  · change (run (makeUnion values) heap).2.edges.next ≤ primitiveGrowth width bound
    have old := fits.edges
    change heap.edges.next ≤ bound at old
    have retained := primitiveGrowth_ge width bound
    omega

/-- The literal ordinary-union fast path copies only input rows, at any input shape. -/
theorem ordinaryUnion (values : List (Value Symbol Guard)) (heap : State Symbol Guard) (bound width : Nat)
    (fits : Fits bound heap) (available : Values heap values) (length : values.length ≤ width) :
    Fits (primitiveGrowth width bound) (run (MergedOrdinaryHeight.ordinaryUnion values) heap).2 ∧
      InternedValueMass.value (run (MergedOrdinaryHeight.ordinaryUnion values) heap).1 ≤ primitiveGrowth width bound ∧
      (run (MergedOrdinaryHeight.ordinaryUnion values) heap).2.nodes.next ≤ heap.nodes.next + 1 ∧
      (run (MergedOrdinaryHeight.ordinaryUnion values) heap).2.edges.next = heap.edges.next := by
  have mass := Nat.le_trans (copied_rows values) (values_mass fits values available length)
  have actual := InternedValueMassConstructors.node (values.flatMap nodeEdges) heap fits.stored
  have larger : max bound (1 + InternedValueMass.edges (values.flatMap nodeEdges)) ≤ primitiveGrowth width bound := by
    unfold primitiveGrowth inflate
    omega
  have counters := SourceCurrentAllocatedFiniteOrdinaryReservations.makeNode_next (values.flatMap nodeEdges) heap
  refine ⟨⟨actual.1.mono larger, ?_, ?_, Nat.zero_le _⟩, Nat.le_trans actual.2 larger, counters⟩
  · change (run (makeNode (values.flatMap nodeEdges)) heap).2.nodes.next ≤ primitiveGrowth width bound
    have old := fits.nodes
    change heap.nodes.next ≤ bound at old
    have paid : bound + 1 ≤ primitiveGrowth width bound := Nat.le_max_left _ _
    omega
  · change (run (makeNode (values.flatMap nodeEdges)) heap).2.edges.next ≤ primitiveGrowth width bound
    have old := fits.edges
    change heap.edges.next ≤ bound at old
    have retained := primitiveGrowth_ge width bound
    omega

end Primitives

private theorem iterate_ge (next : Nat → Nat) (grows : ∀ value, value ≤ next value) (count value : Nat) :
    value ≤ HeightOrderControlled.iterate next count value := by
  induction count generalizing value with
  | zero => exact Nat.le_refl _
  | succ count ih => exact Nat.le_trans (grows value) (ih (next value))

private theorem majorant_succ_ge (dimension bound : Nat) :
    HeightOrderControlled.majorant g dimension bound ≤ HeightOrderControlled.majorant g (dimension + 1) bound := by
  rw [HeightOrderControlled.majorant_succ, HeightOrderControlled.iterate]
  exact Nat.le_trans (Nat.le_of_lt (SourceCurrentAllocatedReaderControl.g_strict _))
    (iterate_ge _ (fun value => Nat.le_trans
      (HeightOrderControlled.majorant_ge g SourceCurrentAllocatedReaderControl.g_strict dimension value)
      (Nat.le_of_lt (SourceCurrentAllocatedReaderControl.g_strict _))) bound _)

private theorem majorant_dimension_mono {first last : Nat} (enough : first ≤ last) (bound : Nat) :
    HeightOrderControlled.majorant g first bound ≤ HeightOrderControlled.majorant g last bound := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le enough
  induction extra with
  | zero => exact Nat.le_refl _
  | succ extra ih => exact Nat.le_trans ih (majorant_succ_ge _ _)

private theorem heapBound_counters_mono (mass : Nat) {firstNodes lastNodes firstEdges lastEdges : Nat}
    (nodes : firstNodes ≤ lastNodes) (edges : firstEdges ≤ lastEdges) :
    SourceCurrentAllocatedUnfoldHistory.heapBound firstNodes firstEdges mass ≤
      SourceCurrentAllocatedUnfoldHistory.heapBound lastNodes lastEdges mass := by
  unfold SourceCurrentAllocatedUnfoldHistory.heapBound
  apply HeightOrderControlled.majorant_mono g SourceCurrentAllocatedReaderControl.g_mono
    SourceCurrentAllocatedReaderControl.g_strict
  unfold SourceCurrentAllocatedUnfoldHistory.initialBound
  omega

private theorem readFuel_mono {firstNodes lastNodes firstEdges lastEdges firstMass lastMass : Nat}
    (nodes : firstNodes ≤ lastNodes) (edges : firstEdges ≤ lastEdges) (masses : firstMass ≤ lastMass) :
    SourceCurrentAllocatedRowReadNumeric.readFuel firstNodes firstEdges firstMass ≤
      SourceCurrentAllocatedRowReadNumeric.readFuel lastNodes lastEdges lastMass := by
  unfold SourceCurrentAllocatedRowReadNumeric.readFuel SourceCurrentAllocatedReaderNumeric.fuel
  apply Nat.le_trans (HeightOrderControlled.majorant_mono g SourceCurrentAllocatedReaderControl.g_mono
    SourceCurrentAllocatedReaderControl.g_strict (firstMass + 1) ?_)
    (majorant_dimension_mono (Nat.add_le_add_right masses 1) _)
  apply SourceCurrentAllocatedReaderControl.g_mono
  unfold SourceCurrentAllocatedReaderNumeric.initialControl
  simp only [Nat.one_mul]
  omega

private theorem comparisonFuel_counters_mono (mass : Nat) {firstNodes lastNodes firstEdges lastEdges : Nat}
    (nodes : firstNodes ≤ lastNodes) (edges : firstEdges ≤ lastEdges) :
    comparisonFuel firstNodes firstEdges mass ≤ comparisonFuel lastNodes lastEdges mass := by
  have bounds := heapBound_counters_mono mass nodes edges
  have readers := readFuel_mono bounds bounds bounds
  have pairs := Nat.mul_le_mul bounds bounds
  unfold SourceMergedComparisonNumeric.comparisonFuel SourceMergedComparisonNumeric.readerFuel
  omega

/-- Initial scalar resources bound all actual selection unfolds. -/
def selectionGrowth (bound : Nat) : Nat := SourceCurrentAllocatedUnfoldHistory.heapBound bound bound bound

/-- The selection envelope retains its original scalar resources. -/
theorem selectionGrowth_ge (bound : Nat) : bound ≤ selectionGrowth bound := by
  simpa only [selectionGrowth, SourceCurrentAllocatedUnfoldHistory.heapBound,
    SourceCurrentAllocatedUnfoldHistory.initialBound, Nat.max_self] using
    HeightOrderControlled.majorant_ge g SourceCurrentAllocatedReaderControl.g_strict bound bound

/-- Larger initial scalar resources retain the selection envelope. -/
theorem selectionGrowth_mono {first last : Nat} (enough : first ≤ last) : selectionGrowth first ≤ selectionGrowth last := by
  simp only [selectionGrowth, SourceCurrentAllocatedUnfoldHistory.heapBound,
    SourceCurrentAllocatedUnfoldHistory.initialBound, Nat.max_self]
  exact Nat.le_trans (HeightOrderControlled.majorant_mono g SourceCurrentAllocatedReaderControl.g_mono
    SourceCurrentAllocatedReaderControl.g_strict first enough) (majorant_dimension_mono enough last)

section Selection
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- An actual successful selection retains its exact return at initial scalar fuel. -/
theorem selection_replay (clear : Guard → Bool) (oldFuel : Nat) (inputs : List (Value Symbol Guard))
    (heap : State Symbol Guard) (bound : Nat) (semantic : SemanticReady heap) (fits : Fits bound heap)
    (available : Values heap inputs) (closed : ClosedValues inputs)
    (result : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : SourceMergedSelection.select clear oldFuel inputs heap = .done result after) :
    SourceMergedComparisonEffects.Effect heap after ∧ Fits (selectionGrowth bound) after ∧
      SourceMergedSelection.select clear (comparisonFuel bound bound bound) inputs heap = .done result after ∧
      ∀ extra, SourceMergedSelection.select clear (comparisonFuel bound bound bound + extra) inputs heap = .done result after := by
  have recorded := SourceMergedSelectionNumeric.select_recorded bound clear oldFuel inputs heap semantic
    (InternedValueMassBinderDepth.stored_bounded heap bound fits.stored) available closed result after done
  have current := recorded.history.complete semantic.ready.semantic semantic.ready.covered semantic.ready.depth fits.stored
  have enough := comparisonFuel_counters_mono bound fits.nodes fits.edges
  have replay := SourceMergedSelectionNumeric.select_replay heap bound semantic fits.stored oldFuel
    (comparisonFuel bound bound bound) clear enough inputs heap semantic available closed (.refl heap) result after done
  refine ⟨recorded.effect, current.2.mono (heapBound_counters_mono bound fits.nodes fits.edges), replay, ?_⟩
  intro extra
  exact SourceMergedSelectionNumeric.select_replay heap bound semantic fits.stored oldFuel
    (comparisonFuel bound bound bound + extra) clear (Nat.le_trans enough (Nat.le_add_right _ _))
    inputs heap semantic available closed (.refl heap) result after done

/-- Initial facts construct selection and its full current-heap envelope without a completed call input. -/
theorem selection_complete (clear : Guard → Bool) (inputs : List (Value Symbol Guard))
    (heap : State Symbol Guard) (bound : Nat) (semantic : SemanticReady heap) (fits : Fits bound heap)
    (available : Values heap inputs) (closed : ClosedValues inputs) :
    ∃ result after,
      SourceMergedSelection.select clear (comparisonFuel bound bound bound) inputs heap = .done result after ∧
      SourceMergedComparisonEffects.Effect heap after ∧ Fits (selectionGrowth bound) after ∧
      ∀ extra, SourceMergedSelection.select clear (comparisonFuel bound bound bound + extra) inputs heap = .done result after := by
  obtain ⟨result, after, done, _effects, _fits, _resources, _stable⟩ :=
    SourceMergedSelectionNumeric.select_complete clear inputs heap bound semantic fits.stored available closed
  have checked := selection_replay clear _ inputs heap bound semantic fits available closed result after done
  exact ⟨result, after, checked.2.2.1, checked.1, checked.2.1, checked.2.2.2⟩

end Selection

/-- A current physical memo bounds the exact retained winner, including an earlier completed entry. -/
theorem winner_bound {bound : Nat} {heap : State Symbol Guard} {memo : SourceCurrentMemoMergeGraph.Memo Symbol Guard}
    (physical : SourceCurrentMemoMergeEffects.Stored heap memo) (fits : Fits bound heap)
    (input candidate : Value Symbol Guard) (available : Available heap candidate) :
    Available heap (SourceCurrentMemoMergeGraph.winner memo input candidate).result ∧
      InternedValueMass.value (SourceCurrentMemoMergeGraph.winner memo input candidate).result ≤ bound :=
  SourceCurrentMemoMergeMass.winner_bound physical fits.stored input candidate available

end MicroCFTA.SourceCurrentMemoMergeResourceControl
