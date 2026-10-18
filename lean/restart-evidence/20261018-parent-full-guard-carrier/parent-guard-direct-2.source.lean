import MicroCFTA.SourceCurrentLocalGuardAlphabet
import MicroCFTA.SourceCurrentParentNumeric

/-!
# Complete Parent returns with finite raw guard carriers

Raw rejection adds only Top. A live Parent retains the local carrier and
then constructs either its exact original guard or Top. Initial facts
construct the full old receipt and the same nine-fuel worker return.
-/
namespace MicroCFTA.SourceCurrentParentGuardAlphabet
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedGuardedLanguage (meaning edgeMeaning)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedPartialInvariant (Context Post)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Request" => SourceCurrentAllocatedPartialState.EdgeRequest
local notation "Resident" => InternedEdgeResidency.EdgeResident
local notation "contradictory" => SourceEqualityMkEdgeAllocation.contradictory
local notation "raw" => SourceEqualityConjoinAllocation.readback
local notation "advance" => SourceCurrentAllocatedPartialState.advance
local notation "fuel" => SourceCurrentParentForecast.fuel
local notation "Carrier" => SourceEqualityAnnotationHeap.Heap
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "LiveInputs" => SourceCurrentParentNumeric.LiveInputs
namespace Graph
export SourceCurrentAllocatedParentEdge (Edge Receipt RawMeaning)
export SourceCurrentAllocatedParentEdgeActual (Reads)
end Graph
variable {width bits : Nat}

/-- Raw rejection retains Top and the initial alphabet without inspecting the loaded field. -/
noncomputable def forecast (alphabet : List Guard) (budget count : Nat) (original : Guard)
    (loaded : Allocated) (inherited : EqValue) (before : Checked width) (profile : Profile) : List Guard :=
  if contradictory original then top :: alphabet
  else top :: original :: SourceCurrentLocalGuardAlphabet.forecast alphabet budget count loaded inherited before profile

/-- A resident initial request supplies its exact loaded forecast or the unused missing-field fallback. -/
noncomputable def residentForecast (alphabet : List Guard) (budget : Nat) (request : Request)
    (before : Checked width) (profile : Profile) : List Guard :=
  if contradictory request.value.entry.key.constraint then top :: alphabet
  else match SourceEqualityConstraintFieldLookup.load request.value.entry.key.constraint before.operations.constraints with
    | .ok (some loaded) => forecast alphabet budget request.value.children.length request.value.entry.key.constraint
        loaded request.inherited before profile
    | _ => alphabet

variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem constructor_carrier (annotation : Guard → Prop)
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {symbol : Symbol} {constraint : Allocated} {children : List (Value Symbol Guard)}
    {before after : Checked width} {result : EdgeValue Symbol Guard}
    (actual : SourceCurrentAllocatedMkEdge.Receipt formulas solver inventory symbol constraint children before result after)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before.operations)
    (ready : SourceEqualityConstraintAllocation.Ready before.operations.constraints constraint.stored)
    (known : Carrier annotation before.native.machine.heap) (original : annotation (raw constraint)) (unit : annotation top) :
    Carrier annotation after.native.machine.heap := by
  have built := SourceEqualityMkEdgeAllocation.build_receipt symbol constraint.stored constraint.guard children
    before.operations before.native.machine.heap valid ready
  have heap := congrArg (fun output => output.2.native.machine.heap) actual.actual
  simp only [SourceCurrentAllocatedMkEdge.build] at heap
  rw [built.1] at heap
  change (run (SourceEqualityMkEdgeAllocation.work symbol (raw constraint) children
    (SourceEqualityMkEdgeAllocation.accepted (raw constraint) children.length)) before.native.machine.heap).2 =
      after.native.machine.heap at heap
  rw [← heap]
  cases keep : SourceEqualityMkEdgeAllocation.accepted (raw constraint) children.length with
  | true =>
      simpa only [SourceEqualityMkEdgeAllocation.work,keep,ite_true] using
        SourceEqualityAnnotationHeap.run annotation _
          (SourceEqualityAnnotationHeap.makeEdge annotation symbol (raw constraint) children original)
          before.native.machine.heap known
  | false =>
      simpa only [SourceEqualityMkEdgeAllocation.work,keep,Bool.false_eq_true,ite_false] using
        SourceEqualityAnnotationHeap.run annotation _
          (SourceEqualityAnnotationHeap.makeEdge annotation symbol top [.empty] unit) before.native.machine.heap known

variable [DecidableEq Symbol] [DecidableEq (Value Symbol Guard)]

/-- Raw rejection constructs its Top sentinel without field, inherited, child or Room premises. -/
theorem rejected (alphabet : List Guard)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (symbol : Symbol) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Caller width) (memos : Memos)
    (initial : Context formulas solver inventory before memos) (frame : Frame formulas solver inventory before.checked)
    (profile : Profile) (fits : Fits profile before.checked) (test : contradictory original = true)
    (known : Carrier (fun guard => guard ∈ alphabet) before.checked.native.machine.heap) :
    SourceCurrentParentNumeric.Receipt formulas solver inventory profile budget symbol original loaded inherited values before memos
      (SourceCurrentAllocatedMkEdge.reject symbol before.checked).1 (SourceCurrentAllocatedMkEdge.reject symbol before.checked).2
      before.fourth before.merge memos ∧
    Carrier (fun guard => guard ∈ forecast alphabet budget values.length original loaded inherited before.checked profile)
      (SourceCurrentAllocatedMkEdge.reject symbol before.checked).2.native.machine.heap := by
  have receipt := SourceCurrentParentNumeric.rejected formulas solver inventory budget symbol original loaded inherited values
    before memos initial frame profile fits test
  have fields : Carrier (fun guard => guard ∈ top :: alphabet) before.checked.native.machine.heap :=
    fun key edge found => List.mem_cons_of_mem _ (known key edge found)
  have returned := SourceEqualityAnnotationHeap.run (fun guard => guard ∈ top :: alphabet)
    (makeEdge symbol top [.empty]) (SourceEqualityAnnotationHeap.makeEdge _ symbol top [.empty] List.mem_cons_self)
    before.checked.native.machine.heap fields
  refine ⟨receipt,?_⟩
  change Carrier (fun guard => guard ∈ forecast alphabet budget values.length original loaded inherited before.checked profile)
    (run (makeEdge symbol top [.empty]) before.checked.native.machine.heap).2
  simpa only [forecast,test,ite_true] using returned

/-- Initial live facts construct the literal local and parent workers at computed fuels. -/
theorem complete (alphabet : List Guard) (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (symbol : Symbol) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Caller (bits + 2)) (memos : Memos)
    (initial : Context formulas solver inventory before memos) (frame : Frame formulas solver inventory before.checked)
    (profile : Profile) (fits : Fits profile before.checked) (live : LiveInputs original loaded inherited values before)
    (reserved : SourceCurrentParentForecast.Reserved bits budget values.length original loaded inherited before.checked profile)
    (known : Carrier (fun guard => guard ∈ alphabet) before.checked.native.machine.heap) :
    ∃ result after savedFourth saved next final,
      SourceCurrentParentNumeric.Receipt formulas solver next profile budget symbol original loaded inherited values before memos result after savedFourth saved final ∧
      Carrier (fun guard => guard ∈ forecast alphabet budget values.length original loaded inherited before.checked profile) after.native.machine.heap := by
  cases test : contradictory original with
  | true =>
      exact ⟨_, _, before.fourth, before.merge, inventory, memos,
        rejected alphabet formulas solver inventory budget symbol original loaded inherited values before memos initial frame profile fits test known⟩
  | false =>
      obtain ⟨cached, found, inheritedReady, available⟩ := live test
      have loadedReady := SourceEqualityConstraintFieldLookup.load_ready original before.checked.operations.constraints
        initial.ready.good.operations.constraints cached loaded found
      have localRoom : SourceCurrentLocalForecast.Reserved bits budget values.length loaded inherited before.checked profile := by
        simpa only [SourceCurrentParentForecast.Reserved, test, Bool.false_eq_true, ite_false] using reserved
      obtain ⟨children, middle, savedFourth, saved, next, final, lowerReceipt, lowerCarrier⟩ := SourceCurrentLocalGuardAlphabet.complete alphabet formulas solver inventory
        budget original loaded inherited values before memos initial frame profile fits cached found inheritedReady available localRoom known
      have lower := lowerReceipt.semantic
      have storedReady := loadedReady.1.grows lower.effects.grows.constraint_growth
      have field : SourceCurrentConjunctionEquality.FieldAvailable middle.operations (raw loaded) := by
        rw [loadedReady.2]
        exact (show SourceCurrentConjunctionEquality.FieldAvailable before.checked.operations original from ⟨cached, loaded, found⟩).grows
          lower.effects.grows
      obtain ⟨result, after, constructor, finalFrame, numeric, _nodes, _edges⟩ := SourceCurrentMkEdgeNumeric.complete
        formulas solver next symbol loaded children middle lowerReceipt.frame
        (SourceCurrentLocalForecast.finalProfile budget values.length loaded inherited before.checked profile) lowerReceipt.fits
        storedReady field lower.available
      let actual : Graph.Edge budget symbol original loaded inherited values before.checked before.fourth before.merge
          result after savedFourth saved := .live test lowerReceipt.actual constructor.actual
      have reads : Graph.Reads formulas solver actual memos final := .live (test := test) (built := constructor.actual) lowerReceipt.reads
      have semantic : Graph.Receipt formulas solver next symbol original loaded inherited values before.checked result after
          before.fourth savedFourth before.merge saved final := by
        refine ⟨constructor.ready, constructor.admitted, lower.effects.trans constructor.effects, constructor.resident,
          lower.stored.grows constructor.effects.keeps, lower.covered, lower.retained,
          SourceQueryUnfoldMemo.valid_grows _ _ lower.ready.semantic constructor.effects.keeps final lower.globals,
          SourceCurrentEmptinessMemo.grows formulas solver constructor.effects.keeps savedFourth lower.correct,
          lower.fourthRetained, Or.inr ⟨children, middle, lower.length, constructor⟩, ?_⟩
        intro ambient term
        have edgeLaw := constructor.language storedReady ambient term
        rw [loadedReady.2] at edgeLaw
        have narrows : edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term →
            Graph.RawMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient symbol original values term := by
          intro accepted
          obtain ⟨terms, shape, forest, guard⟩ := edgeLaw.mp accepted
          exact ⟨terms, shape, (lower.language ambient symbol terms).1 forest, guard⟩
        refine ⟨narrows, fun inheritedSat => ⟨narrows, ?_⟩⟩
        rintro ⟨terms, shape, forest, guard⟩
        apply edgeLaw.mpr
        refine ⟨terms, shape, ?_, guard⟩
        have guards : SourceEqualityPCSGuard.holds formulas solver original (.node symbol terms) = true := by
          simpa only [shape] using guard
        have inheritedSat : SourceEqualityPrecheck.Sat (.node symbol terms) inherited.payload := by
          simpa only [shape] using inheritedSat
        exact ((lower.language ambient symbol terms).2 guards inheritedSat).mpr forest
      have probes : InternedFreshOrdinaryProbeHeap.Heap after.native.machine.heap := by
        have produced := SourceCurrentAllocatedProbeParent.mkEdge_heap symbol loaded children middle lowerReceipt.post.context.probes
        rw [constructor.actual] at produced
        exact produced
      have post : Post formulas solver next before (advance before after savedFourth saved) final :=
        ⟨⟨semantic.ready, semantic.admitted,
          initial.sound.advance formulas solver after savedFourth saved semantic.effects,
          semantic.stored, semantic.covered, semantic.correct, semantic.globals, probes⟩,
          semantic.effects, semantic.retained, semantic.fourthRetained⟩
      refine ⟨result, after, savedFourth, saved, next, final, ⟨(fun _ => found), actual, reads, semantic, finalFrame, ?_, post, ?_⟩, ?_⟩
      · simpa only [SourceCurrentParentForecast.finalProfile, test, Bool.false_eq_true, ite_false, lower.length] using numeric
      · intro g s r e p h m c n hg hs hr he hp hh hm hc hn
        have done := lowerReceipt.run g s r e p h m c n
          (by simpa only [SourceCurrentParentForecast.fuel, test, Bool.false_eq_true, ite_false] using hg)
          (by simpa only [SourceCurrentParentForecast.fuel, test, Bool.false_eq_true, ite_false] using hs)
          (by simpa only [SourceCurrentParentForecast.fuel, test, Bool.false_eq_true, ite_false] using hr)
          (by simpa only [SourceCurrentParentForecast.fuel, test, Bool.false_eq_true, ite_false] using he)
          (by simpa only [SourceCurrentParentForecast.fuel, test, Bool.false_eq_true, ite_false] using hp)
          (by simpa only [SourceCurrentParentForecast.fuel, test, Bool.false_eq_true, ite_false] using hh)
          (by simpa only [SourceCurrentParentForecast.fuel, test, Bool.false_eq_true, ite_false] using hm)
          (by simpa only [SourceCurrentParentForecast.fuel, test, Bool.false_eq_true, ite_false] using hc)
          (by simpa only [SourceCurrentParentForecast.fuel, test, Bool.false_eq_true, ite_false] using hn)
        simp only [SourceCurrentAllocatedParentWorker.edge, test, Bool.false_eq_true, ite_false, found,
          SourceCurrentAllocatedParentWorker.reduceChildren, done, SourceCurrentAllocatedParentWorker.Outcome.bind,
          SourceCurrentAllocatedParentWorker.build, constructor.actual]
      · refine constructor_carrier
          (fun guard => guard ∈ forecast alphabet budget values.length original loaded inherited before.checked profile)
          constructor lowerReceipt.frame.ready.good.operations storedReady ?_ ?_ ?_
        · intro key edge present
          simp only [forecast,test,Bool.false_eq_true,ite_false]
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (lowerCarrier key edge present))
        · rw [loadedReady.2]
          simp only [forecast,test,Bool.false_eq_true,ite_false,List.mem_cons]
          exact Or.inr (Or.inl rfl)
        · simp only [forecast,test,Bool.false_eq_true,ite_false,List.mem_cons]
          exact Or.inl rfl

/-- Resident live inputs derive their own initial field and children; raw rejection skips these facts. -/
theorem resident_complete (alphabet : List Guard) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory) (budget : Nat) (request : Request)
    (before : Caller (bits + 2)) (memos : Memos) (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (resident : contradictory request.value.entry.key.constraint = false → Resident before.checked.native.machine.heap request.value)
    (inheritedReady : contradictory request.value.entry.key.constraint = false →
      SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (reserved : SourceCurrentParentForecast.residentReserved bits budget request before.checked profile)
    (known : Carrier (fun guard => guard ∈ alphabet) before.checked.native.machine.heap) :
    ∃ loaded result after savedFourth saved next final,
      SourceCurrentParentNumeric.Receipt formulas solver next profile budget request.value.entry.key.symbol request.value.entry.key.constraint loaded
        request.inherited request.value.children before memos result after savedFourth saved final ∧
      Fits (SourceCurrentParentForecast.residentProfile budget request before.checked profile) after ∧
      Carrier (fun guard => guard ∈ residentForecast alphabet budget request before.checked profile) after.native.machine.heap ∧
      ∀ g s r e p h m c n,
        SourceCurrentParentForecast.residentFuel budget request before.checked profile ≤ g →
        SourceCurrentParentForecast.residentFuel budget request before.checked profile ≤ s →
        SourceCurrentParentForecast.residentFuel budget request before.checked profile ≤ r →
        SourceCurrentParentForecast.residentFuel budget request before.checked profile ≤ e →
        SourceCurrentParentForecast.residentFuel budget request before.checked profile ≤ p →
        SourceCurrentParentForecast.residentFuel budget request before.checked profile ≤ h →
        SourceCurrentParentForecast.residentFuel budget request before.checked profile ≤ m →
        SourceCurrentParentForecast.residentFuel budget request before.checked profile ≤ c →
        SourceCurrentParentForecast.residentFuel budget request before.checked profile ≤ n →
        SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget request.value.entry.key.symbol
          request.value.entry.key.constraint request.inherited request.value.children before.checked before.fourth before.merge =
          .done result after savedFourth saved := by
  cases test : contradictory request.value.entry.key.constraint with
  | true =>
      let loaded : Allocated := ⟨.contradiction, request.value.entry.key.constraint.guard⟩
      obtain ⟨receipt,carrier⟩ := rejected alphabet formulas solver inventory budget request.value.entry.key.symbol request.value.entry.key.constraint
        loaded request.inherited request.value.children before memos initial frame profile fits test known
      refine ⟨loaded, _, _, before.fourth, before.merge, inventory, memos, receipt, ?_, ?_, ?_⟩
      · simpa only [SourceCurrentParentForecast.residentProfile, SourceCurrentParentForecast.finalProfile, test, ite_true] using receipt.fits
      · simpa only [residentForecast,forecast,test,ite_true] using carrier
      · intro g s r e p h m c n _hg _hs _hr _he _hp _hh _hm _hc _hn
        apply receipt.run g s r e p h m c n <;>
          simp only [SourceCurrentParentForecast.fuel, test, ite_true, Nat.zero_le]
  | false =>
      obtain ⟨cached, loaded, found⟩ := initial.ready.good.fields request.value.entry.key request.value (resident test)
      have available := initial.ready.semantic.ready.semantic.1.normal.facts.cached.edges _ request.value (resident test)
      have live : LiveInputs request.value.entry.key.constraint loaded request.inherited request.value.children before :=
        fun _ => ⟨cached, found, inheritedReady test, available⟩
      have reserve : SourceCurrentParentForecast.Reserved bits budget request.value.children.length request.value.entry.key.constraint
          loaded request.inherited before.checked profile := by
        simpa only [SourceCurrentParentForecast.residentReserved, test, Bool.false_eq_true, ite_false, found] using reserved
      obtain ⟨result, after, savedFourth, saved, next, final, receipt, carrier⟩ := complete alphabet formulas solver inventory budget
        request.value.entry.key.symbol request.value.entry.key.constraint loaded request.inherited request.value.children
        before memos initial frame profile fits live reserve known
      refine ⟨loaded, result, after, savedFourth, saved, next, final, receipt, ?_, ?_, ?_⟩
      · simpa only [SourceCurrentParentForecast.residentProfile, test, Bool.false_eq_true, ite_false, found] using receipt.fits
      · simpa only [residentForecast,test,Bool.false_eq_true,ite_false,found] using carrier
      · intro g s r e p h m c n hg hs hr he hp hh hm hc hn
        exact receipt.run g s r e p h m c n
          (by simpa only [SourceCurrentParentForecast.residentFuel, test, Bool.false_eq_true, ite_false, found] using hg)
          (by simpa only [SourceCurrentParentForecast.residentFuel, test, Bool.false_eq_true, ite_false, found] using hs)
          (by simpa only [SourceCurrentParentForecast.residentFuel, test, Bool.false_eq_true, ite_false, found] using hr)
          (by simpa only [SourceCurrentParentForecast.residentFuel, test, Bool.false_eq_true, ite_false, found] using he)
          (by simpa only [SourceCurrentParentForecast.residentFuel, test, Bool.false_eq_true, ite_false, found] using hp)
          (by simpa only [SourceCurrentParentForecast.residentFuel, test, Bool.false_eq_true, ite_false, found] using hh)
          (by simpa only [SourceCurrentParentForecast.residentFuel, test, Bool.false_eq_true, ite_false, found] using hm)
          (by simpa only [SourceCurrentParentForecast.residentFuel, test, Bool.false_eq_true, ite_false, found] using hc)
          (by simpa only [SourceCurrentParentForecast.residentFuel, test, Bool.false_eq_true, ite_false, found] using hn)

end MicroCFTA.SourceCurrentParentGuardAlphabet
