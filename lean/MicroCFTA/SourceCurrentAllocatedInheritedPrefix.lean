import MicroCFTA.SourceCurrentAllocatedPrecheck

/-!
# Actual inherited-first prefix on a returned edge

Inherited contradiction returns before the own accessor. A live inherited
value demands the returned raw field, then combines inherited first and own
second. The prefix retains the literal equality-operation result at the
same full native state. Missing fields and accessor errors remain distinct.
This finite prefix makes no recursive child request. Runtime forcing and
the later indexed child walk remain separate.
-/
namespace MicroCFTA.SourceCurrentAllocatedInheritedPrefix
open Language InternedConstructorTemplates InternedEdgeResidency
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Operations" => SourceEqualityConstraintMemoAllocation.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
local notation "FieldAvailable" => SourceCurrentConjunctionEquality.FieldAvailable
variable {width : Nat}

/-- Contradiction skips the accessor; live inputs combine at its actual return. -/
noncomputable def run (original : Guard) (inherited : EqValue) (before : Operations) :
    Except String (Option EqValue) × Operations :=
  match inherited with
  | .contradiction => (.ok (some .contradiction), before)
  | .live _ _ =>
      let own := SourceCurrentConjunctionEquality.accessor original before
      match own.1 with
      | .error message => (.error message, own.2)
      | .ok none => (.ok none, own.2)
      | .ok (some value) =>
          let combined := SourceEqualityConstraintMemoAllocation.combine inherited value own.2
          (combined.1.map some, combined.2)

/-- Inherited contradiction has no accessor or allocation effect. -/
theorem run_contradiction (original : Guard) (before : Operations) :
    run original .contradiction before = (.ok (some .contradiction), before) := rfl

/-- A reached accessor error retains its literal returned operation state. -/
theorem run_error (original : Guard) (identity : Nat) (records : List SourceEqualityClassOrder.Record)
    (before : Operations) (message : String)
    (failed : (SourceCurrentConjunctionEquality.accessor original before).1 = .error message) :
    run original (.live identity records) before =
      (.error message, (SourceCurrentConjunctionEquality.accessor original before).2) := by
  simp only [run, failed]

/-- A reached missing field stays missing without a combination. -/
theorem run_missing (original : Guard) (identity : Nat) (records : List SourceEqualityClassOrder.Record)
    (before : Operations)
    (missing : (SourceCurrentConjunctionEquality.accessor original before).1 = .ok none) :
    run original (.live identity records) before =
      (.ok none, (SourceCurrentConjunctionEquality.accessor original before).2) := by
  simp only [run, missing]

/-- A reached own value enters the source combination in inherited-first order. -/
theorem run_combine (original : Guard) (identity : Nat) (records : List SourceEqualityClassOrder.Record)
    (before : Operations) (own : EqValue)
    (loaded : (SourceCurrentConjunctionEquality.accessor original before).1 = .ok (some own)) :
    run original (.live identity records) before =
      ((SourceEqualityConstraintMemoAllocation.combine (.live identity records) own
        (SourceCurrentConjunctionEquality.accessor original before).2).1.map some,
       (SourceEqualityConstraintMemoAllocation.combine (.live identity records) own
        (SourceCurrentConjunctionEquality.accessor original before).2).2) := by
  simp only [run, loaded]

/-- The prefix installs only its literal operation state at the unchanged heap. -/
noncomputable def state (before : Checked width) (original : Guard) (inherited : EqValue) : Checked width :=
  advancePhysical before ⟨before.native.machine.heap, (run original inherited before.operations).2⟩

/-- Both native memo tables, the domain cache, and the constructor heap stay exact. -/
theorem state_native (before : Checked width) (original : Guard) (inherited : EqValue) :
    (state before original inherited).native = before.native := rfl

/-- The checked state retains the literal prefix operation result. -/
theorem state_operations (before : Checked width) (original : Guard) (inherited : EqValue) :
    (state before original inherited).operations = (run original inherited before.operations).2 := rfl

/-- Inherited contradiction retains the whole checked state. -/
theorem state_contradiction (before : Checked width) (original : Guard) :
    state before original .contradiction = before := by
  cases before
  rfl

/-- Actual finite allocation derives the current physical state and exact equality meaning. -/
structure Receipt (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (original : Guard) (inherited : EqValue) (before : Checked width) (combined : EqValue) : Prop where
  actual : (run original inherited before.operations).1 = .ok (some combined)
  native : (state before original inherited).native = before.native
  operations : (state before original inherited).operations = (run original inherited before.operations).2
  valid : SourceEqualityConstraintMemoAllocation.Valid (state before original inherited).operations
  grows : SourceEqualityConstraintMemoAllocation.Grows before.operations (state before original inherited).operations
  combinedReady : EqReady (state before original inherited).operations.constraints combined
  ready : Ready (state before original inherited)
  admitted : At formulas solver inventory (state before original inherited)
  effects : Effects (physical before) (physical (state before original inherited))
  extension : SourceRecursiveIntersectionKernel.Extension before.native.machine
    (state before original inherited).native.machine
  exact : ∀ term : Term Symbol, SourceEqualityPrecheck.Sat term combined.payload ↔
    SourceEqualityPrecheck.Sat term inherited.payload ∧
      SourceEqualityGuardReadback.Sat term (SourceCompactGuards.sourceEqualities original)

/-- The contradiction prefix needs no field, load, or child premise. -/
theorem contradiction (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (original : Guard) (before : Checked width) (ready : Ready before)
    (admitted : At formulas solver inventory before) :
    Receipt formulas solver inventory original .contradiction before .contradiction := by
  have physicalReady := SourceCurrentAllocatedConjunctionMemo.ready before ready.good ready.semantic ready.costs
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [state_contradiction] using ready.good.operations
  · simpa only [state_contradiction] using SourceEqualityConstraintMemoAllocation.grows_refl before.operations
  · change EqReady before.operations.constraints .contradiction
    exact ⟨trivial, by intro records impossible; cases impossible⟩
  · simpa only [state_contradiction] using ready
  · simpa only [state_contradiction] using admitted
  · simpa only [state_contradiction] using SourceCurrentConjunctionRowsAllocation.Effects.refl (physical before) physicalReady
  · simpa only [state_contradiction] using SourceRecursiveIntersectionKernel.Extension.refl before.native.machine
  · intro term
    simp only [SourceEqualityConstraintAllocation.Value.payload, SourceEqualityPrecheck.Sat, false_and]

/-- Initial available fields construct the exact finite inherited-first prefix. -/
theorem finite (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (original : Guard) (inherited : EqValue) (before : Checked width)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (field : FieldAvailable before.operations original)
    (inheritedReady : EqReady before.operations.constraints inherited) :
    ∃ combined, Receipt formulas solver inventory original inherited before combined := by
  cases inherited with
  | contradiction => exact ⟨.contradiction, contradiction formulas solver inventory original before ready admitted⟩
  | live identity records =>
      obtain ⟨own, accessorDone, accessorValid, ownReady, classes, _, accessorGrows⟩ :=
        SourceCurrentConjunctionEquality.accessor_correct original before.operations ready.good.operations field
      obtain ⟨combined, combinedDone, combinedValid, combinedReady, payload, combinedGrows⟩ :=
        SourceEqualityConstraintMemoAllocation.combine_correct (.live identity records) own
          (SourceCurrentConjunctionEquality.accessor original before.operations).2 accessorValid
          (inheritedReady.grows accessorGrows.constraint_growth) ownReady
      have actual : run original (.live identity records) before.operations =
          (.ok (some combined), (SourceEqualityConstraintMemoAllocation.combine (.live identity records) own
            (SourceCurrentConjunctionEquality.accessor original before.operations).2).2) := by
        simp only [run_combine original identity records before.operations own accessorDone, combinedDone, Except.map]
      have growth := SourceCurrentConjunctionEquality.grows_trans accessorGrows combinedGrows
      have nextValid : SourceEqualityConstraintMemoAllocation.Valid
          (state before original (.live identity records)).operations := by
        simpa only [state_operations, actual] using combinedValid
      have nextGrowth : SourceEqualityConstraintMemoAllocation.Grows before.operations
          (state before original (.live identity records)).operations := by
        simpa only [state_operations, actual] using growth
      have nextReady : Ready (state before original (.live identity records)) :=
        SourceCurrentConjunctionAllocatedClassEntry.operations_ready before _ ready nextValid nextGrowth
      have effects : Effects (physical before) (physical (state before original (.live identity records))) :=
        ⟨SourceEqualityRequiredCache.pure_keeps _ ready.semantic.ready,
          ⟨ready.semantic, ready.costs, nextValid, ready.good.fields.grows nextGrowth⟩, nextGrowth⟩
      have extension := SourceCurrentAllocatedQueryMemo.advance_extension before
        ⟨before.native.machine.heap, (run original (.live identity records) before.operations).2⟩ effects
      refine ⟨combined, congrArg Prod.fst actual, rfl, rfl, nextValid, nextGrowth, ?_, nextReady,
        admitted.advance _ extension, effects, extension, ?_⟩
      · simpa only [state_operations, actual] using combinedReady
      · intro term
        have ownExact : SourceEqualityPrecheck.Sat term own.payload ↔
            SourceEqualityGuardReadback.Sat term (SourceCompactGuards.sourceEqualities original) := by
          rw [← classes]
          exact (SourceEqualityInheritedPayload.classes_sat own.payload term).symm
        exact ((SourceEqualityInheritedPayload.combine_exact payload).2 term).trans (and_congr Iff.rfl ownExact)

/-- The returned resident edge supplies its own actual current field load. -/
theorem resident_finite (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (edge : EdgeValue Symbol Guard) (inherited : EqValue) (before : Checked width)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (resident : EdgeResident before.native.machine.heap edge)
    (inheritedReady : EqReady before.operations.constraints inherited) :
    ∃ combined, Receipt formulas solver inventory edge.entry.key.constraint inherited before combined :=
  finite formulas solver inventory edge.entry.key.constraint inherited before ready admitted
    (ready.good.fields edge.entry.key edge resident) inheritedReady

/-- Full returned-guard acceptance and inherited satisfaction imply the actual combined payload. -/
theorem Receipt.guard_satisfied
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {original : Guard} {inherited combined : EqValue} {before : Checked width}
    (receipt : Receipt formulas solver inventory original inherited before combined) (term : Term Symbol)
    (accepted : SourceEqualityPCSGuard.holds formulas solver original term = true)
    (inheritedSat : SourceEqualityPrecheck.Sat term inherited.payload) :
    SourceEqualityPrecheck.Sat term combined.payload :=
  (receipt.exact term).mpr ⟨inheritedSat, SourceEqualityPCSGuard.own_sat formulas solver original term accepted⟩

end MicroCFTA.SourceCurrentAllocatedInheritedPrefix
