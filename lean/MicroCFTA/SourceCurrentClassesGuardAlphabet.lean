import MicroCFTA.SourceCurrentClassesNumeric
import MicroCFTA.SourceCurrentPreparationGuardAlphabet
import MicroCFTA.SourceCurrentClassGuardAlphabet

/-!
# Initial finite guard carriers through complete local classes

Preparation and the actual selected class pass retain one complete worker
return. Finite initial guard words and positional record selections bound
every class continuation. Initial resource reservations remain explicit.
No future result, guard range or capacity callback is supplied.
-/
namespace MicroCFTA.SourceCurrentClassesGuardAlphabet
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceEqualityClassOrder (Record Coherent)
open SourceEqualityProjectionPathDomain (ForestClosed)
namespace Preparation
export SourceCurrentPreparationGuardAlphabet (complete)
end Preparation
namespace Graph
export SourceCurrentConjunctionScanClassPass (Reduction Receipt)
export SourceCurrentConjunctionScanClassPassActual (Reads)
end Graph
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "advance" => SourceCurrentAllocatedPartialState.advance
local notation "guards" => SourceCurrentConjunctionGuardUniverse.guards
local notation "fuel" => SourceCurrentClassesForecast.fuel
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "wordsThrough" => SourceCurrentParentAlphabetReservation.wordsThrough
local notation "preparationForecast" => SourceCurrentPreparationGuardAlphabet.forecast
local notation "advanceAlphabet" => SourceCurrentNativeGuardAlphabet.advance
variable {bits : Nat}


/-- Exact initial words and positional class selections determine the returned carrier. -/
noncomputable def forecast (budget count : Nat) (records : List Record)
    (alphabet : List Guard) (profile : Profile) : List Guard :=
  let prepared := preparationForecast budget count records alphabet profile
  alphabet ++ prepared ++ (wordsThrough alphabet profile.edges).flatMap fun ambient =>
    (SourceCurrentInitialSelectionForecast.selections records).flatMap fun kept =>
      advanceAlphabet prepared (SourceCurrentClassGuardAlphabet.foldCount kept count
        (SourceCurrentScanRequiredForecast.finalProfile budget count records ambient profile))

private theorem ambient_member {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    {before : Checked (bits+2)} (frame : Frame formulas solver inventory before)
    {profile : Profile} (fits : Fits profile before) {alphabet : List Guard}
    (known : Heap (fun guard => guard ∈ alphabet) before.native.machine.heap) :
    guards before.native.machine.heap ∈ wordsThrough alphabet profile.edges := by
  apply SourceCurrentParentAlphabetReservation.wordsThrough_member
  · have length := List.length_filterMap_le
      (SourceRecursiveIntersectionSourceProfile.edgeRead before.native.machine.heap)
      (List.range before.native.machine.heap.edges.next)
    simp only [SourceCurrentConjunctionGuardUniverse.guards,SourceRecursiveIntersectionSourceProfile.edgePayloads,
      List.length_map,List.length_range] at length ⊢
    exact Nat.le_trans length fits.edges
  · intro guard member
    obtain ⟨edge,present,rfl⟩ := List.mem_map.mp member
    have facts := frame.ready.semantic.ready.semantic.1.normal.facts
    obtain ⟨index,_range,read⟩ := List.mem_filterMap.mp present
    unfold SourceRecursiveIntersectionSourceProfile.edgeRead at read
    cases found : before.native.machine.heap.edges.issued index with
    | none => simp only [found,Option.bind_none] at read; cases read
    | some key =>
        have stored : before.native.machine.heap.edgeRecords key = some edge := by
          simpa only [found,Option.bind_some] using read
        have same := (facts.coherent.edges key edge stored).2.1
        exact known _ _ (by simpa only [same] using stored)


variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem class_pass (alphabet : List Guard)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (records : List SourceEqualityClassOrder.Record)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (values : List (Value Symbol Guard)) (before : Caller (bits + 2)) (memos : Memos) (profile : Profile)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (fits : Fits profile before.checked)
    (available : Values before.checked.native.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (reserved : SourceCurrentConstrainedCapClassForecast.Reserved bits records values.length profile)
    (known : Heap (fun guard => guard ∈ alphabet) before.checked.native.machine.heap) :
    ∃ results after saved next final,
      ∃ actual : SourceCurrentAllocatedClassPass.Pass records values before.checked before.merge results after saved,
      SourceCurrentAllocatedClassPass.PassReads formulas solver actual memos final ∧
      SourceCurrentAllocatedClassPass.Receipt formulas solver next records values before.checked before.merge results after saved memos final ∧
      Post formulas solver next before (advance before after before.fourth saved) final ∧
      Frame formulas solver next after ∧ Fits (SourceCurrentConstrainedCapClassForecast.foldProfile records values.length profile) after ∧
      Heap (fun guard => guard ∈ advanceAlphabet alphabet (SourceCurrentClassGuardAlphabet.foldCount records values.length profile)) after.native.machine.heap ∧
      results.length = values.length ∧
      (advance before after before.fourth saved).nodeResults = before.nodeResults ∧
      (advance before after before.fourth saved).edgeResults = before.edgeResults ∧
      (advance before after before.fourth saved).fourth = before.fourth ∧
      SourceCurrentAllocatedClassWorker.pass
        (SourceCurrentConstrainedCapClassForecast.foldFuel records values.length profile) (SourceCurrentConstrainedCapClassForecast.foldFuel records values.length profile)
        (SourceCurrentConstrainedCapClassForecast.foldFuel records values.length profile) (SourceCurrentConstrainedCapClassForecast.foldFuel records values.length profile)
        (SourceCurrentConstrainedCapClassForecast.foldFuel records values.length profile) (SourceCurrentConstrainedCapClassForecast.foldFuel records values.length profile)
        records values before.checked before.merge = .done results after saved ∧
      ∀ e p h m s n,
        SourceCurrentConstrainedCapClassForecast.foldFuel records values.length profile ≤ e → SourceCurrentConstrainedCapClassForecast.foldFuel records values.length profile ≤ p →
        SourceCurrentConstrainedCapClassForecast.foldFuel records values.length profile ≤ h → SourceCurrentConstrainedCapClassForecast.foldFuel records values.length profile ≤ m →
        SourceCurrentConstrainedCapClassForecast.foldFuel records values.length profile ≤ s → SourceCurrentConstrainedCapClassForecast.foldFuel records values.length profile ≤ n →
        SourceCurrentAllocatedClassWorker.pass e p h m s n records values before.checked before.merge =
          .done results after saved := by
  obtain ⟨results, after, saved, next, final, actual, reads, receipt, returned, numeric,
      carrier, length, done, stable⟩ :=
    SourceCurrentClassGuardAlphabet.pass alphabet formulas solver inventory records coherent active values
      before.checked before.merge profile frame fits available domains initial.stored initial.covered memos
      initial.globals reserved known
  have probes := SourceCurrentAllocatedProbeClassPass.pass_heap formulas solver inventory reads coherent active
    initial.ready initial.admitted available domains initial.stored initial.covered initial.globals initial.probes
  have post : Post formulas solver next before (advance before after before.fourth saved) final :=
    ⟨⟨receipt.ready, receipt.admitted,
      initial.sound.advance formulas solver _ before.fourth saved receipt.effects, receipt.stored, receipt.covered,
      SourceCurrentEmptinessMemo.grows formulas solver receipt.effects.keeps before.fourth initial.correct,
      receipt.globals.valid, probes⟩, receipt.effects, receipt.retained, fun _ _ found => found⟩
  refine ⟨results, after, saved, next, final, actual, reads, receipt, post, returned, numeric,
    carrier, length, rfl, rfl, rfl, done, stable⟩


variable [DecidableEq (Value Symbol Guard)]

/-- Initial support constructs the full local class receipt and its finite raw guard carrier. -/
theorem complete (alphabet : List Guard)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (values : List (Value Symbol Guard)) (records : List Record)
    (before : Caller (bits + 2)) (memos : Memos) (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (available : Values before.checked.native.machine.heap values)
    (proper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [])
    (coherent : ∀ record ∈ records, Coherent record) (active : ∀ record ∈ records, Nontrivial record.paths)
    (reserved : SourceCurrentClassesForecast.Reserved bits budget values.length records
      (guards before.checked.native.machine.heap) profile)
    (known : Heap (fun guard => guard ∈ alphabet) before.checked.native.machine.heap) :
    ∃ outcome results after savedFourth saved next final,
      SourceCurrentClassesNumeric.Receipt formulas solver next profile budget records values before memos
        outcome results after savedFourth saved final ∧
      Heap (fun guard => guard ∈ forecast budget values.length records alphabet profile) after.native.machine.heap := by
  obtain ⟨outcome, kept, prepared, middle, savedFourth, next, current, preparedReceipt, preparedCarrier⟩ :=
    Preparation.complete alphabet formulas solver inventory budget values records before memos initial frame profile fits
      available proper coherent active reserved.1 known
  have prefixEnough := SourceCurrentClassesForecast.preparation_fuel budget values.length records
    (guards before.checked.native.machine.heap) profile
  cases outcome with
  | some paths =>
      obtain ⟨actual, reads⟩ := SourceCurrentScanRequiredClassGraph.stopped (memo := before.merge)
        (formulas := formulas) (solver := solver) preparedReceipt.reads
      have semantic : Graph.Receipt formulas solver next records values prepared before.checked middle
          before.fourth savedFourth before.merge before.merge (some paths) current :=
        ⟨preparedReceipt.post.context.ready, preparedReceipt.frame.admitted, preparedReceipt.post.effects, preparedReceipt.originals,
          preparedReceipt.available, preparedReceipt.length, preparedReceipt.post.context.stored, preparedReceipt.post.context.covered,
          preparedReceipt.post.retained, preparedReceipt.post.context.globals, preparedReceipt.post.context.correct,
          preparedReceipt.post.fourthRetained, preparedReceipt.rejected, preparedReceipt.language⟩
      refine ⟨some paths, prepared, middle, savedFourth, before.merge, next, current,
        ⟨actual, reads, semantic, preparedReceipt.frame,
        preparedReceipt.fits.mono (SourceCurrentClassesForecast.preparation_le _ _ _ _ _), preparedReceipt.post, ?_⟩, ?_⟩
      · intro g s r e p h m c n hg hs hr _he hp hh _hm _hc hn
        have done := preparedReceipt.run g s r p h n (Nat.le_trans prefixEnough hg) (Nat.le_trans prefixEnough hs)
          (Nat.le_trans prefixEnough hr) (Nat.le_trans prefixEnough hp) (Nat.le_trans prefixEnough hh) (Nat.le_trans prefixEnough hn)
        rw [SourceCurrentScanRequiredWorker.classes, done]
        rfl
      · intro key edge present
        exact List.mem_append_left _ (List.mem_append_right _ (preparedCarrier key edge present))
  | none =>
      have keptCoherent := fun record member => coherent record (preparedReceipt.selected.subset member)
      have keptActive := fun record member => active record (preparedReceipt.selected.subset member)
      have room := SourceCurrentClassesForecast.class_reserved preparedReceipt.selected bits budget values.length
        (guards before.checked.native.machine.heap) profile reserved
      have reservedPass : SourceCurrentConstrainedCapClassForecast.Reserved bits kept prepared.length
          (SourceCurrentScanRequiredForecast.finalProfile budget values.length records
            (guards before.checked.native.machine.heap) profile) := by
        simpa only [preparedReceipt.length] using room
      obtain ⟨results, after, saved, lastInventory, final, pass, passReads, checked, passPost, returned,
          passFits, passCarrier, length, _nodes, _edges, _fourth, _done, stable⟩ :=
        class_pass (preparationForecast budget values.length records alphabet profile) formulas solver next kept keptCoherent keptActive prepared
          (advance before middle savedFourth before.merge) current
          (SourceCurrentScanRequiredForecast.finalProfile budget values.length records
            (guards before.checked.native.machine.heap) profile)
          preparedReceipt.post.context preparedReceipt.frame preparedReceipt.fits preparedReceipt.available (preparedReceipt.domains rfl) reservedPass preparedCarrier
      obtain ⟨actual, reads⟩ := SourceCurrentScanRequiredClassGraph.completed preparedReceipt.reads pass passReads
      have post : Post formulas solver lastInventory before (advance before after savedFourth saved) final :=
        preparedReceipt.post.trans passPost
      have language : ∀ ambient symbol terms,
          (All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) results terms →
            All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms) ∧
          ((∀ record ∈ records, ClassSat (.node symbol terms) record.paths) →
            (All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) results terms ↔
              All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms)) := by
        intro ambient symbol terms
        have first := preparedReceipt.language ambient symbol terms
        have last := checked.language ambient symbol terms
        refine ⟨fun accepted => first.1 (last.1 accepted), ?_⟩
        intro satisfied
        exact (last.2 (fun record member => satisfied record (preparedReceipt.selected.subset member))).trans (first.2 satisfied)
      have semantic : Graph.Receipt formulas solver lastInventory records values results before.checked after
          before.fourth savedFourth before.merge saved none final :=
        ⟨post.context.ready, returned.admitted, post.effects,
          (fun value member => checked.effects.keeps.available value (preparedReceipt.originals value member)),
          checked.available, length.trans preparedReceipt.length, post.context.stored, post.context.covered,
          post.retained, post.context.globals, post.context.correct, post.fourthRetained, preparedReceipt.rejected, language⟩
      rw [preparedReceipt.length] at passFits
      have finalFits := passFits.mono
        (SourceCurrentClassesForecast.class_profile preparedReceipt.selected budget values.length
          (guards before.checked.native.machine.heap) profile)
      have classEnough := SourceCurrentClassesForecast.class_fuel preparedReceipt.selected budget values.length
        (guards before.checked.native.machine.heap) profile
      refine ⟨none, results, after, savedFourth, saved, lastInventory, final,
        ⟨actual, reads, semantic, returned, ?_, post, ?_⟩, ?_⟩
      · exact finalFits
      · intro g s r e p h m c n hg hs hr he hp hh hm hc hn
        have done := preparedReceipt.run g s r p h n (Nat.le_trans prefixEnough hg) (Nat.le_trans prefixEnough hs)
          (Nat.le_trans prefixEnough hr) (Nat.le_trans prefixEnough hp) (Nat.le_trans prefixEnough hh) (Nat.le_trans prefixEnough hn)
        have passDone := stable e p h m c n
          (by simpa only [preparedReceipt.length] using Nat.le_trans classEnough he)
          (by simpa only [preparedReceipt.length] using Nat.le_trans classEnough hp)
          (by simpa only [preparedReceipt.length] using Nat.le_trans classEnough hh)
          (by simpa only [preparedReceipt.length] using Nat.le_trans classEnough hm)
          (by simpa only [preparedReceipt.length] using Nat.le_trans classEnough hc)
          (by simpa only [preparedReceipt.length] using Nat.le_trans classEnough hn)
        change SourceCurrentAllocatedClassWorker.pass e p h m c n kept prepared middle before.merge =
          .done results after saved at passDone
        rw [SourceCurrentScanRequiredWorker.classes, done]
        simp only [SourceCurrentAllocatedLocalWorker.Outcome.bind, SourceCurrentAllocatedLocalWorker.pass, passDone]

      · intro key edge present
        apply List.mem_append_right
        apply List.mem_flatMap.mpr
        refine ⟨guards before.checked.native.machine.heap, ambient_member frame fits known, ?_⟩
        apply List.mem_flatMap.mpr
        refine ⟨kept, SourceCurrentInitialSelectionForecast.sublist_selection preparedReceipt.selected, ?_⟩
        simpa only [preparedReceipt.length] using passCarrier key edge present

end MicroCFTA.SourceCurrentClassesGuardAlphabet
