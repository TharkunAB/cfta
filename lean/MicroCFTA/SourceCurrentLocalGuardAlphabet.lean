import MicroCFTA.SourceCurrentClassesGuardAlphabet
import MicroCFTA.SourceCurrentLocalNumeric

/-!
# Complete local reduction with an initial finite guard carrier

The initial allocated precheck determines the exact branch. Early branches
retain raw guards. The live class producer constructs its own complete
return and carrier. The original semantic receipt and replay remain exact.
-/
namespace MicroCFTA.SourceCurrentLocalGuardAlphabet
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedGuardedLanguage (meaning)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedPartialInvariant (Context Post)
namespace Graph
export SourceCurrentAllocatedLocalReduction (Reduction Receipt)
export SourceCurrentAllocatedLocalReductionActual (Reads)
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
local notation "fuel" => SourceCurrentLocalForecast.fuel
local notation "Carrier" => SourceEqualityAnnotationHeap.Heap
variable {width bits : Nat}

/-- The exact initial precheck selects a finite class carrier or retains the entry alphabet. -/
noncomputable def forecast (alphabet : List Guard) (budget count : Nat) (loaded : Allocated) (inherited : EqValue)
    (before : Checked width) (profile : Profile) : List Guard :=
  match (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited before.operations).1 with
  | .ok (.classes records) => SourceCurrentClassesGuardAlphabet.forecast budget count records alphabet profile
  | _ => alphabet

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
theorem complete (alphabet : List Guard) (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Caller (bits + 2)) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.checked.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints inherited)
    (available : Values before.checked.native.machine.heap values)
    (reserved : SourceCurrentLocalForecast.Reserved bits budget values.length loaded inherited before.checked profile)
    (known : Carrier (fun guard => guard ∈ alphabet) before.checked.native.machine.heap) :
    ∃ results after savedFourth saved next final,
      SourceCurrentLocalNumeric.Receipt formulas solver next profile budget original loaded inherited values before memos results after savedFourth saved final ∧
      Carrier (fun guard => guard ∈ forecast alphabet budget values.length loaded inherited before.checked profile) after.native.machine.heap := by
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
      let actual : Graph.Reduction budget loaded inherited values before.checked before.fourth before.merge values
          (prefixState before.checked loaded inherited) before.fourth before.merge := .unchanged checked.actual
      have reads : Graph.Reads formulas solver actual memos memos := .unchanged (actual := checked.actual)
      have semantic : Graph.Receipt formulas solver inventory original loaded inherited values values before.checked
          (prefixState before.checked loaded inherited) before.fourth before.fourth before.merge before.merge memos :=
        ⟨⟨inventory, own, .unchanged, checked⟩, checked.ready, checked.admitted, checked.effects,
          available, available, rfl, initial.stored, initial.covered, extends_refl _, initial.globals,
          initial.correct, (fun _ _ present => present), fun _ _ _ => ⟨id, fun _ _ => Iff.rfl⟩⟩
      refine ⟨values, prefixState before.checked loaded inherited, before.fourth, before.merge, inventory, memos,
        ⟨actual, reads, semantic, prefixFrame, ?_, prefixPost, ?_⟩, ?_⟩
      · simpa only [SourceCurrentLocalForecast.finalProfile, checked.actual] using prefixFits
      · intro g s r e p h m c n _hg _hs _hr _he _hp _hh _hm _hc _hn
        exact SourceCurrentAllocatedLocalWorker.reduce_unchanged g s r e p h m c n budget loaded inherited
          values before.checked before.fourth before.merge checked.actual
      · simpa only [forecast, checked.actual, SourceCurrentAllocatedPrecheck.state_native] using known
  | emptyChildren =>
      let actual : Graph.Reduction budget loaded inherited values before.checked before.fourth before.merge
          (EqualityLeafProjectionRuntimeEmpty.erase values) (prefixState before.checked loaded inherited)
          before.fourth before.merge := .emptyChildren checked.actual
      have reads : Graph.Reads formulas solver actual memos memos := .emptyChildren (actual := checked.actual)
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
        before.fourth, before.merge, inventory, memos, ⟨actual, reads, semantic, prefixFrame, ?_, prefixPost, ?_⟩, ?_⟩
      · simpa only [SourceCurrentLocalForecast.finalProfile, checked.actual] using prefixFits
      · intro g s r e p h m c n _hg _hs _hr _he _hp _hh _hm _hc _hn
        exact SourceCurrentAllocatedLocalWorker.reduce_emptyChildren g s r e p h m c n budget loaded inherited
          values before.checked before.fourth before.merge checked.actual
      · simpa only [forecast, checked.actual, SourceCurrentAllocatedPrecheck.state_native] using known
  | classes records =>
      obtain ⟨proper, _, _, _, _, fields⟩ := checked.classes records rfl
      have recordsProper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [] := by
        intro record member
        exact proper record.paths (List.mem_map.mpr ⟨record, member, rfl⟩)
      have classRoom : SourceCurrentClassesForecast.Reserved bits budget values.length records
          (SourceCurrentConjunctionGuardUniverse.guards before.checked.native.machine.heap) profile := by
        simpa only [SourceCurrentLocalForecast.Reserved, checked.actual] using reserved
      obtain ⟨outcome, results, after, savedFourth, saved, next, final, classes, classCarrier⟩ :=
        SourceCurrentClassesGuardAlphabet.complete alphabet formulas solver inventory budget values records
          (advance before (prefixState before.checked loaded inherited) before.fourth before.merge) memos
          prefixPost.context prefixFrame profile prefixFits available recordsProper
          (fun record member => (fields record member).1) (fun record member => (fields record member).2.2) classRoom known
      let actual : Graph.Reduction budget loaded inherited values before.checked before.fourth before.merge
          results after savedFourth saved := .classes checked.actual classes.actual
      have reads : Graph.Reads formulas solver actual memos final := .classes (actual := checked.actual) classes.reads
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
        ⟨actual, reads, semantic, classes.frame, ?_, prefixPost.trans classes.post, ?_⟩, ?_⟩
      · simpa only [SourceCurrentLocalForecast.finalProfile, checked.actual, enteredHeap] using classes.fits
      · intro g s r e p h m c n hg hs hr he hp hh hm hc hn
        have done := classes.run g s r e p h m c n
          (by simpa only [SourceCurrentLocalForecast.fuel, checked.actual, enteredHeap] using hg)
          (by simpa only [SourceCurrentLocalForecast.fuel, checked.actual, enteredHeap] using hs)
          (by simpa only [SourceCurrentLocalForecast.fuel, checked.actual, enteredHeap] using hr)
          (by simpa only [SourceCurrentLocalForecast.fuel, checked.actual, enteredHeap] using he)
          (by simpa only [SourceCurrentLocalForecast.fuel, checked.actual, enteredHeap] using hp)
          (by simpa only [SourceCurrentLocalForecast.fuel, checked.actual, enteredHeap] using hh)
          (by simpa only [SourceCurrentLocalForecast.fuel, checked.actual, enteredHeap] using hm)
          (by simpa only [SourceCurrentLocalForecast.fuel, checked.actual, enteredHeap] using hc)
          (by simpa only [SourceCurrentLocalForecast.fuel, checked.actual, enteredHeap] using hn)
        change SourceCurrentAllocatedLocalWorker.classes g s r e p h m c n budget records values
          (prefixState before.checked loaded inherited) before.fourth before.merge = .done results after savedFourth saved at done
        simpa only [SourceCurrentAllocatedLocalWorker.reduce, checked.actual, SourceCurrentAllocatedPrecheck.state] using done

      · simpa only [forecast, checked.actual] using classCarrier

end MicroCFTA.SourceCurrentLocalGuardAlphabet
