import MicroCFTA.SourceCurrentClassesForecast
import MicroCFTA.SourceCurrentScanRequiredClassGraph
import MicroCFTA.SourceCurrentClassCallerNumeric

/-!
# Complete local classes from initial resources

The original record list reserves preparation and every possible selected
class continuation. The actual Scan and Required return supplies the
selected domains. The class pass starts at that exact returned caller.
No future execution, finite input Cap, or closed forest is required.
-/
namespace MicroCFTA.SourceCurrentClassesNumeric
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceEqualityClassOrder (Record Coherent)
namespace Preparation
export SourceCurrentScanRequiredNumeric (complete)
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
variable {width bits : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- One complete source return retains the original graph, language, caller, and numeric replay. -/
structure Receipt (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (profile : Profile) (budget : Nat) (records : List Record) (values : List (Value Symbol Guard))
    (before : Caller width) (memos : Memos) (outcome : Option Class) (results : List (Value Symbol Guard))
    (after : Checked width) (savedFourth : Fourth) (saved : Memo) (final : Memos) : Prop where
  /-- The existing graph records the actual reached Scan, Required, and class pass. -/
  actual : Graph.Reduction budget records values before.checked before.fourth before.merge outcome results after savedFourth saved
  /-- Strict source reads retain the same returned global memo bundle. -/
  reads : Graph.Reads formulas solver actual memos final
  /-- The complete existing receipt retains physical effects, language, arity, and memo laws. -/
  semantic : Graph.Receipt formulas solver inventory records values results before.checked after
    before.fourth savedFourth before.merge saved outcome final
  /-- The full query Frame uses the same returned inventory as the caller Post. -/
  frame : Frame formulas solver inventory after
  /-- The original record schedule bounds the complete class return. -/
  fits : Fits (SourceCurrentClassesForecast.finalProfile budget values.length records
    (guards before.checked.native.machine.heap) profile) after
  /-- The caller retains its actual context and both outer result tables. -/
  post : Post formulas solver inventory before (advance before after savedFourth saved) final
  /-- All nine local class fuels can increase independently with the same complete return. -/
  run : ∀ g s r e p h m c n,
    fuel budget values.length records (guards before.checked.native.machine.heap) profile ≤ g →
    fuel budget values.length records (guards before.checked.native.machine.heap) profile ≤ s →
    fuel budget values.length records (guards before.checked.native.machine.heap) profile ≤ r →
    fuel budget values.length records (guards before.checked.native.machine.heap) profile ≤ e →
    fuel budget values.length records (guards before.checked.native.machine.heap) profile ≤ p →
    fuel budget values.length records (guards before.checked.native.machine.heap) profile ≤ h →
    fuel budget values.length records (guards before.checked.native.machine.heap) profile ≤ m →
    fuel budget values.length records (guards before.checked.native.machine.heap) profile ≤ c →
    fuel budget values.length records (guards before.checked.native.machine.heap) profile ≤ n →
    SourceCurrentAllocatedLocalWorker.classes g s r e p h m c n budget records values
      before.checked before.fourth before.merge = .done results after savedFourth saved

/-- Initial caller facts construct the full original class worker without finite Cap premises. -/
theorem complete (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (values : List (Value Symbol Guard)) (records : List Record)
    (before : Caller (bits + 2)) (memos : Memos) (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (available : Values before.checked.native.machine.heap values)
    (proper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [])
    (coherent : ∀ record ∈ records, Coherent record) (active : ∀ record ∈ records, Nontrivial record.paths)
    (reserved : SourceCurrentClassesForecast.Reserved bits budget values.length records
      (guards before.checked.native.machine.heap) profile) :
    ∃ outcome results after savedFourth saved next final,
      Receipt formulas solver next profile budget records values before memos outcome results after savedFourth saved final := by
  obtain ⟨outcome, kept, prepared, middle, savedFourth, next, current, prefix⟩ :=
    Preparation.complete formulas solver inventory budget values records before memos initial frame profile fits
      available proper coherent active reserved.1
  have prefixEnough := SourceCurrentClassesForecast.preparation_fuel budget values.length records
    (guards before.checked.native.machine.heap) profile
  cases outcome with
  | some paths =>
      obtain ⟨actual, reads⟩ := SourceCurrentScanRequiredClassGraph.stopped (memo := before.merge)
        (formulas := formulas) (solver := solver) prefix.reads
      have semantic : Graph.Receipt formulas solver next records values prepared before.checked middle
          before.fourth savedFourth before.merge before.merge (some paths) current :=
        ⟨prefix.post.context.ready, prefix.frame.admitted, prefix.post.effects, prefix.originals,
          prefix.available, prefix.length, prefix.post.context.stored, prefix.post.context.covered,
          prefix.post.retained, prefix.post.context.globals, prefix.post.context.correct,
          prefix.post.fourthRetained, prefix.rejected, prefix.language⟩
      refine ⟨some paths, prepared, middle, savedFourth, before.merge, next, current,
        actual, reads, semantic, prefix.frame,
        prefix.fits.mono (SourceCurrentClassesForecast.preparation_le _ _ _ _ _), prefix.post, ?_⟩
      intro g s r e p h m c n hg hs hr _he hp hh _hm _hc hn
      have done := prefix.run g s r p h n (Nat.le_trans prefixEnough hg) (Nat.le_trans prefixEnough hs)
        (Nat.le_trans prefixEnough hr) (Nat.le_trans prefixEnough hp) (Nat.le_trans prefixEnough hh) (Nat.le_trans prefixEnough hn)
      rw [SourceCurrentScanRequiredWorker.classes, done]
      rfl
  | none =>
      have keptCoherent := fun record member => coherent record (prefix.selected.subset member)
      have keptActive := fun record member => active record (prefix.selected.subset member)
      have room := SourceCurrentClassesForecast.class_reserved prefix.selected bits budget values.length
        (guards before.checked.native.machine.heap) profile reserved
      have reservedPass : SourceCurrentConstrainedCapClassForecast.Reserved bits kept prepared.length
          (SourceCurrentScanRequiredForecast.finalProfile budget values.length records
            (guards before.checked.native.machine.heap) profile) := by
        simpa only [prefix.length] using room
      obtain ⟨results, after, saved, lastInventory, final, pass, passReads, checked, passPost, returned,
          passFits, length, _nodes, _edges, _fourth, _done, stable⟩ :=
        SourceCurrentClassCallerNumeric.complete formulas solver next kept keptCoherent keptActive prepared
          (advance before middle savedFourth before.merge) current
          (SourceCurrentScanRequiredForecast.finalProfile budget values.length records
            (guards before.checked.native.machine.heap) profile)
          prefix.post.context prefix.frame prefix.fits prefix.available (prefix.domains rfl) reservedPass
      obtain ⟨actual, reads⟩ := SourceCurrentScanRequiredClassGraph.completed prefix.reads pass passReads
      have post : Post formulas solver lastInventory before (advance before after savedFourth saved) final :=
        prefix.post.trans passPost
      have language : ∀ ambient symbol terms,
          (All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) results terms →
            All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms) ∧
          ((∀ record ∈ records, ClassSat (.node symbol terms) record.paths) →
            (All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) results terms ↔
              All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms)) := by
        intro ambient symbol terms
        have first := prefix.language ambient symbol terms
        have last := checked.language ambient symbol terms
        refine ⟨fun accepted => first.1 (last.1 accepted), ?_⟩
        intro satisfied
        exact (last.2 (fun record member => satisfied record (prefix.selected.subset member))).trans (first.2 satisfied)
      have semantic : Graph.Receipt formulas solver lastInventory records values results before.checked after
          before.fourth savedFourth before.merge saved none final :=
        ⟨post.context.ready, returned.admitted, post.effects,
          (fun value member => checked.effects.keeps.available value (prefix.originals value member)),
          checked.available, length.trans prefix.length, post.context.stored, post.context.covered,
          post.retained, post.context.globals, post.context.correct, post.fourthRetained, prefix.rejected, language⟩
      rw [prefix.length] at passFits
      have finalFits := passFits.mono
        (SourceCurrentClassesForecast.class_profile prefix.selected budget values.length
          (guards before.checked.native.machine.heap) profile)
      have classEnough := SourceCurrentClassesForecast.class_fuel prefix.selected budget values.length
        (guards before.checked.native.machine.heap) profile
      refine ⟨none, results, after, savedFourth, saved, lastInventory, final,
        actual, reads, semantic, returned, ?_, post, ?_⟩
      · exact finalFits
      · intro g s r e p h m c n hg hs hr he hp hh hm hc hn
        have done := prefix.run g s r p h n (Nat.le_trans prefixEnough hg) (Nat.le_trans prefixEnough hs)
          (Nat.le_trans prefixEnough hr) (Nat.le_trans prefixEnough hp) (Nat.le_trans prefixEnough hh) (Nat.le_trans prefixEnough hn)
        have passDone := stable e p h m c n
          (by simpa only [prefix.length] using Nat.le_trans classEnough he)
          (by simpa only [prefix.length] using Nat.le_trans classEnough hp)
          (by simpa only [prefix.length] using Nat.le_trans classEnough hh)
          (by simpa only [prefix.length] using Nat.le_trans classEnough hm)
          (by simpa only [prefix.length] using Nat.le_trans classEnough hc)
          (by simpa only [prefix.length] using Nat.le_trans classEnough hn)
        rw [SourceCurrentScanRequiredWorker.classes, done]
        simpa only [SourceCurrentAllocatedLocalWorker.Outcome.bind, SourceCurrentAllocatedLocalWorker.pass, passDone]

end MicroCFTA.SourceCurrentClassesNumeric
