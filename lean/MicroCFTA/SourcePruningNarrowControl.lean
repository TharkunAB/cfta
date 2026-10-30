import MicroCFTA.SourcePruningNativeView
import MicroCFTA.EqualityOrdinaryReadback
import MicroCFTA.SourcePruningEnumerationAction

/-!
# Control of actual pruning row filters

The filter keeps complete existing edges. Its result is a physical ordinary
normal form. The same filter then returns the same value and heap at any fuel.
Different keys can remove further rows. These laws do not bound intersections,
selected Mu unfolding, all handle changes, or recursive worker depth.

-/
namespace MicroCFTA.SourcePruningNativeView
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedRecordCoherence
local notation "Symbol" => SourcePruningTemplates.Symbol
attribute [local instance] FormulaExecutable.formulaDecidableEq
variable {Guard Key : Type}

/-- An ordinary physical normal form with all rows retained needs no further work. -/
theorem narrowAt_of_normal [DecidableEq (EdgeKey Symbol Guard)]
    (fits : Key → Symbol → Bool) (admits : Key → Value Symbol Guard → Bool)
    (fuel : Nat) (key : Key) (value : Value Symbol Guard) (before : State Symbol Guard)
    (ordinary : SourceEqualityRequiredCache.Ordinary value)
    (normal : EqualityOrdinaryReadback.Normal before value)
    (kept : ∀ edge ∈ nodeEdges value, keeps fits admits key edge = true) :
    narrowAt fits admits fuel key value before = .done value before := by
  have filtered : (nodeEdges value).filter (keeps fits admits key) = nodeEdges value :=
    List.filter_eq_self.mpr kept
  have exposed : MergedFreshOrdinaryExposure.nodeEdges fuel value before =
      .done (nodeEdges value) before := by
    cases value with
    | empty | node => rfl
    | reference | union | mu => cases ordinary
  change run (makeNode (nodeEdges value)) before = (value, before) at normal
  simp only [narrowAt, exposed, filtered, normal]

/-- The actual closed-input filter derives a physical normal result and exact replay. -/
theorem narrowAt_complete_control [DecidableEq (EdgeKey Symbol Guard)]
    (fits : Key → Symbol → Bool) (admits : Key → Value Symbol Guard → Bool)
    (key : Key) (value : Value Symbol Guard) (before : State Symbol Guard)
    (ready : SourceEqualityRequiredCache.Ready before)
    (available : Available before value) (closed : value.free = []) :
    ∃ fuel rows middle result after,
      MergedFreshOrdinaryExposure.nodeEdges fuel value before = .done rows middle ∧
      run (makeNode (rows.filter (keeps fits admits key))) middle = (result, after) ∧
      narrowAt fits admits fuel key value before = .done result after ∧
      SourceEqualityRequiredCache.Keeps before after ∧
      Available after result ∧ result.free = [] ∧
      SourceEqualityRequiredCache.Ordinary result ∧
      EqualityOrdinaryReadback.Normal after result ∧
      (∀ edge ∈ nodeEdges result, edge ∈ rows ∧ keeps fits admits key edge = true) ∧
      (∀ extra, narrowAt fits admits (fuel + extra) key value before = .done result after) ∧
      (∀ repeatFuel, narrowAt fits admits repeatFuel key result after = .done result after) := by
  obtain ⟨fuel, rows, middle, exposed, semantic, covered, depth, growth, history,
      resident, closedRows, stable⟩ :=
    MergedFreshOrdinaryColdTermination.read_closed value before ready.semantic ready.covered ready.depth available closed
  let selected := rows.filter (keeps fits admits key)
  let constructed := run (makeNode selected) middle
  have middleReady : SourceEqualityRequiredCache.Ready middle := ⟨semantic, covered, depth⟩
  have readKeeps : SourceEqualityRequiredCache.Keeps before middle := ⟨middleReady, growth, history⟩
  have selectedResident : InternedNestedProvenance.Edges middle selected :=
    fun edge member => resident edge (List.mem_filter.mp member).1
  have selectedClosed : MergedColdReaderClosedInputs.ClosedEdges selected :=
    fun edge member => closedRows edge (List.mem_filter.mp member).1
  obtain ⟨builtKeeps, builtAvailable, builtClosed, builtOrdinary⟩ :=
    SourceEqualityRequiredCache.node selected middle middleReady selectedResident selectedClosed
  have builtNormal : EqualityOrdinaryReadback.Normal constructed.2 constructed.1 :=
    EqualityOrdinaryReadback.makeNode_normal selected middle constructed.2
      middleReady.semantic.1.normal.facts.coherent middleReady.semantic.1.normal.facts.linked
      builtKeeps.ready.semantic.1.normal.facts.coherent selectedResident (grows_refl _)
  have constructedRows : nodeEdges constructed.1 = canonicalEdges (surviving selected) :=
    EqualityLeafProjectionPhysical.makeNode_edges selected middle middleReady.semantic.1.normal.facts.coherent
      middleReady.semantic.1.normal.facts.linked selectedResident
  have resultRows : ∀ edge ∈ nodeEdges constructed.1, edge ∈ rows ∧ keeps fits admits key edge = true := by
    intro edge member
    rw [constructedRows] at member
    have survivingMember := canonicalEdges_member (surviving selected) edge member
    exact List.mem_filter.mp (List.mem_filter.mp survivingMember).1
  refine ⟨fuel, rows, middle, constructed.1, constructed.2, exposed, rfl, ?_, readKeeps.trans builtKeeps,
    builtAvailable, builtClosed, builtOrdinary, builtNormal, resultRows, ?_, ?_⟩
  · simp only [narrowAt, exposed, constructed, selected]
  · intro extra
    simp only [narrowAt, stable extra, constructed, selected]
  · intro repeatFuel
    exact narrowAt_of_normal fits admits repeatFuel key constructed.1 constructed.2
      builtOrdinary builtNormal (fun edge member => (resultRows edge member).2)

/-- Any successful ordinary-input filter keeps only complete original root rows. -/
theorem narrowAt_ordinary_rows [DecidableEq (EdgeKey Symbol Guard)]
    (fits : Key → Symbol → Bool) (admits : Key → Value Symbol Guard → Bool)
    (fuel : Nat) (key : Key) (value result : Value Symbol Guard) (before after : State Symbol Guard)
    (ready : SourceEqualityRequiredCache.Ready before)
    (available : Available before value) (ordinary : SourceEqualityRequiredCache.Ordinary value)
    (returned : narrowAt fits admits fuel key value before = .done result after) :
    ∀ edge ∈ nodeEdges result, edge ∈ nodeEdges value ∧ keeps fits admits key edge = true := by
  have exposed : MergedFreshOrdinaryExposure.nodeEdges fuel value before =
      .done (nodeEdges value) before := by
    cases value with
    | empty | node => rfl
    | reference | union | mu => cases ordinary
  have rowsResident := resident_edges before ready.semantic.1.normal.facts.linked value available.resident
  have selectedResident : ∀ edge ∈ (nodeEdges value).filter (keeps fits admits key), EdgeResident before edge :=
    fun edge member => rowsResident edge (List.mem_filter.mp member).1
  simp only [narrowAt, exposed] at returned
  have same := MergedSourceComparison.Result.done.inj returned
  have resultSame : (run (makeNode ((nodeEdges value).filter (keeps fits admits key))) before).1 = result := same.1
  have resultRows := EqualityLeafProjectionPhysical.makeNode_edges
    ((nodeEdges value).filter (keeps fits admits key)) before ready.semantic.1.normal.facts.coherent
    ready.semantic.1.normal.facts.linked selectedResident
  rw [resultSame] at resultRows
  intro edge member
  rw [resultRows] at member
  have survivingMember := canonicalEdges_member _ edge member
  exact List.mem_filter.mp (List.mem_filter.mp survivingMember).1

end MicroCFTA.SourcePruningNativeView

namespace MicroCFTA.SourcePruningEnumerationAction
open InternedConstructorTemplates InternedEdgeResidency
open SourcePruningNativeView
open SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
attribute [local instance] FormulaExecutable.formulaDecidableEq
variable {Guard EnumGuard Typing Key : Type}

local instance narrowControlMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- Actual preparation retains rejection for Empty and the handle for a retained normal node. -/
theorem prepare_of_normal [DecidableEq (EdgeKey Symbol Guard)]
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → Value Symbol Guard → Bool) (metadata : SourcePruningRecordTypes.Metadata Typing)
    (nativeFuel representativeFuel uv handle : Nat) (scs : List EnumerationState.Suspended)
    (value : Value Symbol Guard) (before : State Symbol Guard)
    (ordinary : SourceEqualityRequiredCache.Ordinary value)
    (normal : EqualityOrdinaryReadback.Normal before value)
    (kept : ∀ edge ∈ nodeEdges value, keeps fits admits (holeKey metadata.typing uv) edge = true)
    (encoded : encodeNode value = some handle) :
    prepare (EnumGuard := EnumGuard) holeKey fits admits metadata nativeFuel representativeFuel uv handle scs value before =
      .done (value, some (match value with | .empty => EnumerationState.reject | _ => pure ())) before := by
  have repeated := narrowAt_of_normal fits admits nativeFuel (holeKey metadata.typing uv) value before
    ordinary normal kept
  cases value with
  | empty =>
      have narrowed : SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv .empty before =
          .done .empty before := by
        simp only [SourcePruningOuterNarrow.narrow]
        split
        · rfl
        · exact repeated
      simp only [prepare, narrowed]
  | reference | union | mu => cases ordinary
  | node entry edges depth free =>
      have narrowed : SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv
          (.node entry edges depth free) before = .done (.node entry edges depth free) before := by
        simp only [SourcePruningOuterNarrow.narrow]
        split
        · rfl
        · exact repeated
      simp only [prepare, narrowed, encoded, ite_true]

end MicroCFTA.SourcePruningEnumerationAction
