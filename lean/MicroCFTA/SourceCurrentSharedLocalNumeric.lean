import MicroCFTA.SourceCurrentSharedLocalForecast
import MicroCFTA.SourceCurrentSharedClassesNumeric
import MicroCFTA.SourceCurrentAllocatedSharedLocalWorker

/-!
# Initial completion of the shared local reduction

The current stored field and inherited equality value construct the actual
precheck. Its original branch selects unchanged children, erased children,
or complete class reduction. Initial numeric reservations determine every
worker bound. New execution and read receipts retain the shared classes
continuation. The reused semantic receipt contains no Scan graph. No future
range, branch, or successful call is assumed.
-/
namespace MicroCFTA.SourceCurrentSharedLocalNumeric
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedGuardedLanguage (meaning)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedPartialInvariant (Context Post)
namespace Graph
export SourceCurrentAllocatedLocalReduction (Receipt)
end Graph
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "advance" => SourceCurrentAllocatedPartialState.advance
local notation "prefixState" => SourceCurrentAllocatedPrecheck.state
local notation "runPrefix" => SourceEqualityPartialPrecheckAllocation.run
local notation "fuel" => SourceCurrentSharedLocalForecast.fuel
variable {width bits : Nat}
section
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- The actual precheck selects exactly one local continuation. -/
inductive Execution (budget : Nat) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo) :
    List (Value Symbol Guard) → Checked width → Fourth → Memo → Prop where
  | unchanged (actual : (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .ok .unchanged) :
      Execution budget loaded inherited values before fourth memo values (prefixState before loaded inherited) fourth memo
  | emptyChildren (actual : (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .ok .emptyChildren) :
      Execution budget loaded inherited values before fourth memo (EqualityLeafProjectionRuntimeEmpty.erase values)
        (prefixState before loaded inherited) fourth memo
  | classes {records outcome results after savedFourth saved}
      (actual : (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .ok (.classes records))
      (continuation : SourceCurrentSharedClassesNumeric.Execution budget records values
        (prefixState before loaded inherited) fourth memo outcome results after savedFourth saved) :
      Execution budget loaded inherited values before fourth memo results after savedFourth saved

/-- Early returns make no global query; live returns retain the actual stage reads. -/
inductive Reads (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    {budget : Nat} → {loaded : Allocated} → {inherited : EqValue} →
    {values results : List (Value Symbol Guard)} → {before after : Checked width} →
    {fourth savedFourth : Fourth} → {memo saved : Memo} →
    Execution budget loaded inherited values before fourth memo results after savedFourth saved → Memos → Memos → Prop where
  | unchanged {budget loaded inherited values before fourth memo actual memos} :
      Reads formulas solver (Execution.unchanged (budget := budget) (loaded := loaded) (inherited := inherited)
        (values := values) (before := before) (fourth := fourth) (memo := memo) actual) memos memos
  | emptyChildren {budget loaded inherited values before fourth memo actual memos} :
      Reads formulas solver (Execution.emptyChildren (budget := budget) (loaded := loaded) (inherited := inherited)
        (values := values) (before := before) (fourth := fourth) (memo := memo) actual) memos memos
  | classes {budget loaded inherited values before fourth memo records outcome results after savedFourth saved actual}
      {continuation : SourceCurrentSharedClassesNumeric.Execution budget records values
        (prefixState before loaded inherited) fourth memo outcome results after savedFourth saved} {memos final}
      (reads : SourceCurrentSharedClassesNumeric.Reads formulas solver continuation memos final) :
      Reads formulas solver (Execution.classes actual continuation) memos final

/-- One constructed shared return retains its actual branches, language, caller and replay. -/
structure Receipt (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (profile : Profile) (budget : Nat) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Caller width) (memos : Memos) (results : List (Value Symbol Guard))
    (after : Checked width) (savedFourth : Fourth) (saved : Memo) (final : Memos) : Prop where
  /-- The new execution retains the actual precheck and shared class continuation. -/
  actual : Execution budget loaded inherited values before.checked before.fourth before.merge results after savedFourth saved
  /-- Strict source reads retain the exact returned global memo bundle. -/
  reads : Reads formulas solver actual memos final
  /-- The pure semantic receipt retains guarded language and every physical memo law. -/
  semantic : Graph.Receipt formulas solver inventory original loaded inherited values results before.checked after
    before.fourth savedFourth before.merge saved final
  /-- The full query Frame uses the same returned inventory as the caller Post. -/
  frame : Frame formulas solver inventory after
  /-- Initial fields and operations bound the complete local return. -/
  fits : Fits (SourceCurrentSharedLocalForecast.finalProfile budget values.length loaded inherited before.checked profile) after
  /-- The caller retains its actual context and both outer result tables. -/
  post : Post formulas solver inventory before (advance before after savedFourth saved) final
  /-- All nine local fuels can increase independently with the same complete return. -/
  run : ∀ g s r e p h m c n,
    fuel budget values.length loaded inherited before.checked profile ≤ g →
    fuel budget values.length loaded inherited before.checked profile ≤ s →
    fuel budget values.length loaded inherited before.checked profile ≤ r →
    fuel budget values.length loaded inherited before.checked profile ≤ e →
    fuel budget values.length loaded inherited before.checked profile ≤ p →
    fuel budget values.length loaded inherited before.checked profile ≤ h →
    fuel budget values.length loaded inherited before.checked profile ≤ m →
    fuel budget values.length loaded inherited before.checked profile ≤ c →
    fuel budget values.length loaded inherited before.checked profile ≤ n →
    SourceCurrentAllocatedSharedLocalWorker.reduce g s r e p h m c n budget loaded inherited values
      before.checked before.fourth before.merge = .done results after savedFourth saved

end

private theorem erased_narrows (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (values : List (Value Symbol Guard)) (terms : List (Term Symbol)) :
    All₂ (meaning holds ambient) (EqualityLeafProjectionRuntimeEmpty.erase values) terms → All₂ (meaning holds ambient) values terms := by
  cases values with
  | nil => exact id
  | cons value values =>
      intro accepted
      cases accepted with
      | cons impossible _ => simp only [meaning] at impossible

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- Initial stored-field facts construct every local branch without finite Cap or future range premises. -/
theorem complete (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Caller (bits + 2)) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.checked.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints inherited)
    (available : Values before.checked.native.machine.heap values)
    (reserved : SourceCurrentSharedLocalForecast.Reserved bits budget values.length loaded inherited before.checked profile) :
    ∃ results after savedFourth saved next final,
      Receipt formulas solver next profile budget original loaded inherited values before memos results after savedFourth saved final := by
  obtain ⟨own, branch, checked⟩ := SourceCurrentAllocatedPrecheck.loaded_complete formulas solver inventory
    before.checked initial.ready initial.admitted original cached loaded found inherited inheritedReady
  have prefixFrame : Frame formulas solver inventory (prefixState before.checked loaded inherited) :=
    ⟨checked.ready, checked.admitted, frame.context, frame.joint, frame.origins⟩
  have prefixFits : Fits profile (prefixState before.checked loaded inherited) :=
    ⟨fits.nodes, fits.edges, fits.domains, fits.stored⟩
  have enteredHeap : (advance before (prefixState before.checked loaded inherited) before.fourth before.merge).checked.native.machine.heap =
      before.checked.native.machine.heap := rfl
  have prefixPost : Post formulas solver inventory before
      (advance before (prefixState before.checked loaded inherited) before.fourth before.merge) memos :=
    ⟨⟨checked.ready, checked.admitted,
      initial.sound.advance formulas solver _ before.fourth before.merge checked.effects,
      initial.stored, initial.covered, initial.correct, initial.globals, initial.probes⟩,
      checked.effects, extends_refl _, fun _ _ present => present⟩
  cases branch with
  | unchanged =>
      let actual : Execution budget loaded inherited values before.checked before.fourth before.merge values
          (prefixState before.checked loaded inherited) before.fourth before.merge := .unchanged checked.actual
      have reads : Reads formulas solver actual memos memos := .unchanged (actual := checked.actual)
      have semantic : Graph.Receipt formulas solver inventory original loaded inherited values values before.checked
          (prefixState before.checked loaded inherited) before.fourth before.fourth before.merge before.merge memos :=
        ⟨⟨inventory, own, .unchanged, checked⟩, checked.ready, checked.admitted, checked.effects,
          available, available, rfl, initial.stored, initial.covered, extends_refl _, initial.globals,
          initial.correct, (fun _ _ present => present), fun _ _ _ => ⟨id, fun _ _ => Iff.rfl⟩⟩
      refine ⟨values, prefixState before.checked loaded inherited, before.fourth, before.merge, inventory, memos,
        actual, reads, semantic, prefixFrame, ?_, prefixPost, ?_⟩
      · simpa only [SourceCurrentSharedLocalForecast.finalProfile, checked.actual] using prefixFits
      · intro g s r e p h m c n _hg _hs _hr _he _hp _hh _hm _hc _hn
        exact SourceCurrentAllocatedSharedLocalWorker.reduce_unchanged g s r e p h m c n budget loaded inherited
          values before.checked before.fourth before.merge checked.actual
  | emptyChildren =>
      let actual : Execution budget loaded inherited values before.checked before.fourth before.merge
          (EqualityLeafProjectionRuntimeEmpty.erase values) (prefixState before.checked loaded inherited)
          before.fourth before.merge := .emptyChildren checked.actual
      have reads : Reads formulas solver actual memos memos := .emptyChildren (actual := checked.actual)
      have semantic : Graph.Receipt formulas solver inventory original loaded inherited values
          (EqualityLeafProjectionRuntimeEmpty.erase values) before.checked (prefixState before.checked loaded inherited)
          before.fourth before.fourth before.merge before.merge memos := by
        refine ⟨⟨inventory, own, .emptyChildren, checked⟩, checked.ready, checked.admitted, checked.effects,
          available, (SourceEqualityEmptyPropagation.erased_scope before.checked.native.machine.heap values).1,
          List.length_map _, initial.stored, initial.covered, extends_refl _, initial.globals,
          initial.correct, (fun _ _ present => present), ?_⟩
        intro ambient symbol terms
        exact ⟨erased_narrows _ ambient values terms,
          fun guard inheritedSat => False.elim (checked.empty_guard rfl _ guard inheritedSat)⟩
      refine ⟨EqualityLeafProjectionRuntimeEmpty.erase values, prefixState before.checked loaded inherited,
        before.fourth, before.merge, inventory, memos, actual, reads, semantic, prefixFrame, ?_, prefixPost, ?_⟩
      · simpa only [SourceCurrentSharedLocalForecast.finalProfile, checked.actual] using prefixFits
      · intro g s r e p h m c n _hg _hs _hr _he _hp _hh _hm _hc _hn
        exact SourceCurrentAllocatedSharedLocalWorker.reduce_emptyChildren g s r e p h m c n budget loaded inherited
          values before.checked before.fourth before.merge checked.actual
  | classes records =>
      obtain ⟨proper, _, _, _, _, fields⟩ := checked.classes records rfl
      have recordsProper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [] := by
        intro record member
        exact proper record.paths (List.mem_map.mpr ⟨record, member, rfl⟩)
      have classRoom : SourceCurrentSharedClassesForecast.Reserved bits budget values.length records
          (SourceCurrentConjunctionGuardUniverse.guards before.checked.native.machine.heap) profile := by
        simpa only [SourceCurrentSharedLocalForecast.Reserved, checked.actual] using reserved
      obtain ⟨outcome, results, after, savedFourth, saved, next, final, classes⟩ :=
        SourceCurrentSharedClassesNumeric.complete formulas solver inventory budget values records
          (advance before (prefixState before.checked loaded inherited) before.fourth before.merge) memos
          prefixPost.context prefixFrame profile prefixFits available recordsProper
          (fun record member => (fields record member).1) (fun record member => (fields record member).2.2) classRoom
      let actual : Execution budget loaded inherited values before.checked before.fourth before.merge
          results after savedFourth saved := .classes checked.actual classes.actual
      have reads : Reads formulas solver actual memos final := .classes (actual := checked.actual) classes.reads
      have semantic : Graph.Receipt formulas solver next original loaded inherited values results
          before.checked after before.fourth savedFourth before.merge saved final := by
        have receipt := classes.semantic
        refine ⟨⟨inventory, own, .classes records, checked⟩, receipt.ready, receipt.admitted,
          checked.effects.trans receipt.effects, receipt.originals, receipt.available, receipt.length,
          receipt.stored, receipt.covered, receipt.retained, receipt.globals, receipt.correct, receipt.fourthRetained, ?_⟩
        intro ambient symbol terms
        have language := receipt.language ambient symbol terms
        refine ⟨language.1, fun guard _ => language.2 ?_⟩
        have satisfied := (checked.classes_exact records rfl (.node symbol terms)).mpr
          (SourceEqualityPCSGuard.own_sat formulas solver original (.node symbol terms) guard)
        intro record member
        exact satisfied record.paths (List.mem_map.mpr ⟨record, member, rfl⟩)
      refine ⟨results, after, savedFourth, saved, next, final,
        actual, reads, semantic, classes.frame, ?_, prefixPost.trans classes.post, ?_⟩
      · simpa only [SourceCurrentSharedLocalForecast.finalProfile, checked.actual, enteredHeap] using classes.fits
      · intro g s r e p h m c n hg hs hr he hp hh hm hc hn
        have done := classes.run g s r e p h m c n
          (by simpa only [SourceCurrentSharedLocalForecast.fuel, checked.actual, enteredHeap] using hg)
          (by simpa only [SourceCurrentSharedLocalForecast.fuel, checked.actual, enteredHeap] using hs)
          (by simpa only [SourceCurrentSharedLocalForecast.fuel, checked.actual, enteredHeap] using hr)
          (by simpa only [SourceCurrentSharedLocalForecast.fuel, checked.actual, enteredHeap] using he)
          (by simpa only [SourceCurrentSharedLocalForecast.fuel, checked.actual, enteredHeap] using hp)
          (by simpa only [SourceCurrentSharedLocalForecast.fuel, checked.actual, enteredHeap] using hh)
          (by simpa only [SourceCurrentSharedLocalForecast.fuel, checked.actual, enteredHeap] using hm)
          (by simpa only [SourceCurrentSharedLocalForecast.fuel, checked.actual, enteredHeap] using hc)
          (by simpa only [SourceCurrentSharedLocalForecast.fuel, checked.actual, enteredHeap] using hn)
        change SourceCurrentAllocatedSharedLocalWorker.classes g s r e p h m c n budget records values
          (prefixState before.checked loaded inherited) before.fourth before.merge = .done results after savedFourth saved at done
        simpa only [SourceCurrentAllocatedSharedLocalWorker.reduce, checked.actual, SourceCurrentAllocatedPrecheck.state] using done

end MicroCFTA.SourceCurrentSharedLocalNumeric
