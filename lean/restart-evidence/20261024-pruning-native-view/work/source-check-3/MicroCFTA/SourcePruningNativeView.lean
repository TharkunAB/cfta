import MicroCFTA.SourcePruningTemplates
import MicroCFTA.SourceEqualityRequiredCache
import MicroCFTA.MergedFreshOrdinaryExposureLive
import MicroCFTA.EqualityLeafProjectionPhysical
import MicroCFTA.InternedEmptyNormalization

/-!
# Actual interned-node narrowing for pruning

The source filter retains complete edges. Both reads use the repaired reader.
The Mu exemption is separate from union closure. Native memo2 implementation,
enumeration-ID realization and semantic pruning remain separate obligations.
-/
namespace MicroCFTA.SourcePruningNativeView
open InternedConstructorTemplates InternedProbeProvenance
local notation "Symbol" => SourcePruningTemplates.Symbol
attribute [local instance] FormulaExecutable.formulaDecidableEq
variable {Guard Key : Type}

/-- Select original edges with the source's full-label and annotation tests. -/
def keeps (fits : Key → Symbol → Bool)
    (admits : Key → Value Symbol Guard → Bool)
    (key : Key) (edge : EdgeValue Symbol Guard) : Bool :=
  match edge.children with
  | [annotation, _, _, _] =>
      if edge.entry.key.symbol = ("app", FullSyntax.Formula.top) then admits key annotation else true
  | [annotation, _] =>
      if edge.entry.key.symbol = ("filter", FullSyntax.Formula.top) then admits key annotation else true
  | [annotation] => admits key annotation && fits key edge.entry.key.symbol
  | _ => true

/-- Read actual rows and construct their selected node in the returned cache. -/
def narrowAt [DecidableEq (EdgeKey Symbol Guard)]
    (fits : Key → Symbol → Bool) (admits : Key → Value Symbol Guard → Bool)
    (fuel : Nat) (key : Key) (value : Value Symbol Guard)
    (before : State Symbol Guard) : MergedSourceComparison.Result Symbol Guard (Value Symbol Guard) :=
  match MergedFreshOrdinaryExposure.nodeEdges fuel value before with
  | .done rows middle =>
      let constructed := run (makeNode (rows.filter (keeps fits admits key))) middle
      .done constructed.1 constructed.2
  | .unresolved name after => .failed (.unresolved name) after
  | .pending pendingKey after => .failed (.pending pendingKey) after
  | .exhausted after => .failed .exhausted after

/-- Exempt Mu alone, then test the actual second read of the narrowed node. -/
def emptyAt [DecidableEq (EdgeKey Symbol Guard)]
    (fits : Key → Symbol → Bool) (admits : Key → Value Symbol Guard → Bool)
    (fuel : Nat) (key : Key) (value : Value Symbol Guard)
    (before : State Symbol Guard) : MergedSourceComparison.Result Symbol Guard Bool :=
  match value with
  | .mu .. => .done false before
  | _ => (narrowAt fits admits fuel key value before).bind fun narrowed middle =>
      match MergedFreshOrdinaryExposure.nodeEdges fuel narrowed middle with
      | .done rows after => .done rows.isEmpty after
      | .unresolved name after => .failed (.unresolved name) after
      | .pending pendingKey after => .failed (.pending pendingKey) after
      | .exhausted after => .failed .exhausted after

/-- Closed source values derive finite narrowing, exact cache effects and literal emptiness. -/
theorem narrowAt_complete [DecidableEq (EdgeKey Symbol Guard)]
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
      InternedEdgeResidency.nodeEdges result =
        canonicalEdges (surviving (rows.filter (keeps fits admits key))) ∧
      (∀ readFuel, MergedFreshOrdinaryExposure.nodeEdges readFuel result after =
        .done (InternedEdgeResidency.nodeEdges result) after) ∧
      (result = .empty ↔ ∀ edge ∈ rows, keeps fits admits key edge = false) ∧
      ((InternedEdgeResidency.nodeEdges result).isEmpty = true ↔
        ∀ edge ∈ rows, keeps fits admits key edge = false) ∧
      (∀ extra, narrowAt fits admits (fuel + extra) key value before = .done result after) := by
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
  change SourceEqualityRequiredCache.Ordinary constructed.1 at builtOrdinary
  have liveRows : ∀ edge ∈ rows, edge.children.any (fun child => child.referenceOf == .empty) = false := by
    have observed := MergedFreshOrdinaryExposureLive.nodeEdges_live fuel value before
      ready.semantic ready.covered available closed
    simpa only [exposed, MergedFreshOrdinaryExposureLive.Live] using observed
  have constructedRows : InternedEdgeResidency.nodeEdges constructed.1 = canonicalEdges (surviving selected) :=
    EqualityLeafProjectionPhysical.makeNode_edges selected middle middleReady.semantic.1.normal.facts.coherent
      middleReady.semantic.1.normal.facts.linked selectedResident
  have referenceEmpty : constructed.1.referenceOf = .empty ↔
      ∀ edge ∈ rows, keeps fits admits key edge = false := by
    rw [InternedEmptyNormalization.makeNode_empty_iff selected middle middleReady.semantic.1.normal.facts.coherent
      middleReady.semantic.1.normal.facts.linked selectedResident]
    constructor
    · intro allDead edge member
      cases kept : keeps fits admits key edge with
      | false => rfl
      | true =>
          have impossible := allDead edge (List.mem_filter.mpr ⟨member, kept⟩)
          rw [liveRows edge member] at impossible
          cases impossible
    · intro noneKept edge member
      obtain ⟨original, kept⟩ := List.mem_filter.mp member
      have impossible : false = true := (noneKept edge original).symm.trans kept
      cases impossible
  have emptyValue : constructed.1 = .empty ↔ ∀ edge ∈ rows, keeps fits admits key edge = false :=
    (InternedEmptyNormalization.reference_empty constructed.1).symm.trans referenceEmpty
  have ordinaryEmpty : (InternedEdgeResidency.nodeEdges constructed.1).isEmpty = true ↔ constructed.1 = .empty := by
    have shape := InternedNonemptyRecords.resident_nonempty constructed.2 builtKeeps.ready.semantic.1.normal.proper
      constructed.1 builtAvailable.resident
    cases same : constructed.1 with
    | empty => simp [InternedEdgeResidency.nodeEdges]
    | node entry edges depth free =>
        have nonempty : edges ≠ [] := by
          simpa only [same, InternedNonemptyRecords.StoredNonempty] using shape
        cases edges with
        | nil => exact False.elim (nonempty rfl)
        | cons edge rest => simp [InternedEdgeResidency.nodeEdges]
    | reference | union | mu =>
        simp only [same, SourceEqualityRequiredCache.Ordinary] at builtOrdinary
  have secondRead : ∀ readFuel, MergedFreshOrdinaryExposure.nodeEdges readFuel constructed.1 constructed.2 =
      .done (InternedEdgeResidency.nodeEdges constructed.1) constructed.2 := by
    intro readFuel
    cases same : constructed.1 with
    | empty | node => rfl
    | reference | union | mu =>
        simp only [same, SourceEqualityRequiredCache.Ordinary] at builtOrdinary
  refine ⟨fuel, rows, middle, constructed.1, constructed.2, exposed, rfl, ?_, readKeeps.trans builtKeeps,
    builtAvailable, builtClosed, builtOrdinary, constructedRows, secondRead, emptyValue,
    ordinaryEmpty.trans emptyValue, ?_⟩
  · simp only [narrowAt, exposed, constructed, selected]
  · intro extra
    simp only [narrowAt, stable extra, constructed, selected]

/-- The Mu-only exemption performs no read and retains the complete cache. -/
theorem emptyAt_mu [DecidableEq (EdgeKey Symbol Guard)]
    (fits : Key → Symbol → Bool) (admits : Key → Value Symbol Guard → Bool)
    (fuel : Nat) (key : Key)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (body depthShape ordinaryShape : Value Symbol Guard) (before : State Symbol Guard) :
    emptyAt fits admits fuel key (.mu entry body depthShape ordinaryShape) before = .done false before := rfl

end MicroCFTA.SourcePruningNativeView
