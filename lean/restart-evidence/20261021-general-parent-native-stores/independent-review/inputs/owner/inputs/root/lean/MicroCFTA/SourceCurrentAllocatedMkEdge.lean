import MicroCFTA.SourceCurrentAllocatedTargetQuery
import MicroCFTA.SourceCurrentConjunctionFieldAllocation
import MicroCFTA.SourceEqualityMkEdgeArity
import MicroCFTA.SourceEqualityNativeDemandMismatchProvenance

/-!
# Checked parent-edge construction with actual equality allocation

The constructor first checks the raw stored field. A live check can demand
the full equality accessor. Rejection allocates the sentinel's Top field.
The returned state retains both native tables and the domain cache.
The separate contradiction endpoint has no child-list argument. These
receipts describe completed resident construction. They do not establish
the GHC demand schedule or machine identity representation.
-/
namespace MicroCFTA.SourceCurrentAllocatedMkEdge
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical advance_extension)
open SourceCurrentConjunctionClassScan (Ready)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionEquality (FieldAvailable)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "OpState" => SourceEqualityConstraintMemoAllocation.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "raw" => SourceEqualityConjoinAllocation.readback
local notation "accepted" => SourceEqualityMkEdgeAllocation.accepted
variable [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- Execute the actual checked constructor and retain its returned operations. -/
noncomputable def build (symbol : Symbol) (constraint : Allocated)
    (children : List (Value Symbol Guard)) (before : Checked width) :
    Except String (EdgeValue Symbol Guard) × Checked width :=
  let built := SourceEqualityMkEdgeAllocation.build symbol constraint.stored constraint.guard children
    before.operations before.native.machine.heap
  (built.1, advancePhysical before ⟨built.2.2, built.2.1⟩)

/-- Construct the source rejection sentinel without a child computation. -/
def reject (symbol : Symbol) (before : Checked width) : EdgeValue Symbol Guard × Checked width :=
  let built := run (makeEdge symbol top [.empty]) before.native.machine.heap
  (built.1, advancePhysical before ⟨built.2, SourceEqualityMkEdgeAllocation.emptyField before.operations⟩)

/-- Physical construction retains the complete checked state and input inventory. -/
structure PhysicalReceipt (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (before : Checked width) (result : EdgeValue Symbol Guard) (after : Checked width) : Prop where
  ready : Ready after
  admitted : At formulas solver inventory after
  effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before) (physical after)
  extension : SourceRecursiveIntersectionKernel.Extension before.native.machine after.native.machine
  resident : InternedEdgeResidency.EdgeResident after.native.machine.heap result
  nodes : after.native.nodes = before.native.nodes
  edges : after.native.edges = before.native.edges
  domains : after.native.machine.domains = before.native.machine.domains

/-- The exact source check chooses the original fields or the sentinel fields. -/
structure Receipt (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (symbol : Symbol) (constraint : Allocated) (children : List (Value Symbol Guard))
    (before : Checked width) (result : EdgeValue Symbol Guard) (after : Checked width) : Prop
    extends PhysicalReceipt formulas solver inventory before result after where
  actual : build symbol constraint children before = (.ok result, after)
  symbol : result.entry.key.symbol = symbol
  guard : result.entry.key.constraint = if accepted (raw constraint) children.length then raw constraint else top
  children : result.children = if accepted (raw constraint) children.length then children else [.empty]

/-- A rejection receipt has no premise about available or evaluated children. -/
structure RejectReceipt (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (symbol : Symbol) (before : Checked width) (result : EdgeValue Symbol Guard) (after : Checked width) : Prop
    extends PhysicalReceipt formulas solver inventory before result after where
  actual : reject symbol before = (result, after)
  symbol : result.entry.key.symbol = symbol
  guard : result.entry.key.constraint = top
  children : result.children = [.empty]

private theorem raw_physical (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (before : Checked width) (ready : Ready before) (admitted : At formulas solver inventory before)
    (operations : OpState) (valid : SourceEqualityConstraintMemoAllocation.Valid operations)
    (growth : SourceEqualityConstraintMemoAllocation.Grows before.operations operations)
    (symbol : Symbol) (guard : Guard) (children : List (Value Symbol Guard))
    (field : FieldAvailable operations guard) (available : Values before.native.machine.heap children) :
    let built := run (makeEdge symbol guard children) before.native.machine.heap
    PhysicalReceipt formulas solver inventory before built.1 (advancePhysical before ⟨built.2, operations⟩) ∧
      built.1.entry.key.symbol = symbol ∧ built.1.entry.key.constraint = guard ∧ built.1.children = children := by
  have actual := SourceEqualityRequiredCache.edge symbol guard children before.native.machine.heap
    ready.semantic.ready available
  have semantic := SourceEqualityRequiredSemanticCache.edge symbol guard children before.native.machine.heap
    ready.semantic available
  have fields := SourceEqualityAnnotationHeap.run (FieldAvailable operations) _
    (SourceEqualityAnnotationHeap.makeEdge (FieldAvailable operations) symbol guard children field)
    before.native.machine.heap (ready.good.fields.grows growth)
  have effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before)
      ⟨(run (makeEdge symbol guard children) before.native.machine.heap).2, operations⟩ :=
    ⟨actual.1, ⟨semantic, ready.costs, valid, fields⟩, growth⟩
  have extension := advance_extension before _ effects
  exact ⟨⟨SourceCurrentConjunctionClassScan.advance_ready before _ ready effects,
    admitted.advance _ extension, effects, extension, actual.2.1, rfl, rfl, rfl⟩,
    MergedPhysicalGroupEdges.makeEdge_fields before.native.machine.heap
      ready.semantic.ready.semantic.1.normal.facts symbol guard children available⟩

/-- Completed source checks and available children derive the same actual return. -/
theorem finite (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (symbol : Symbol) (constraint : Allocated) (children : List (Value Symbol Guard)) (before : Checked width)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (storedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints constraint.stored)
    (field : FieldAvailable before.operations (raw constraint))
    (available : Values before.native.machine.heap children) :
    ∃ result after, Receipt formulas solver inventory symbol constraint children before result after := by
  have checked := SourceEqualityMkEdgeAllocation.check_correct constraint.stored constraint.guard children.length
    before.operations ready.good.operations storedReady
  have built := SourceEqualityMkEdgeAllocation.build_receipt symbol constraint.stored constraint.guard children
    before.operations before.native.machine.heap ready.good.operations storedReady
  cases keep : accepted (raw constraint) children.length with
  | true =>
      have selected : accepted (SourceEqualityAccessorAllocation.constraint constraint.stored constraint.guard)
          children.length = true := keep
      have currentField := field.grows checked.2.2
      obtain ⟨receipt, symbolEq, guardEq, childrenEq⟩ := raw_physical formulas solver inventory before ready admitted
        _ checked.2.1 checked.2.2 symbol (raw constraint) children currentField available
      refine ⟨_, _, ⟨receipt, ?_, symbolEq, ?_, ?_⟩⟩
      · simp only [build, built.1, SourceEqualityMkEdgeAllocation.work,
          SourceEqualityMkEdgeAllocation.outputState, selected, ↓reduceIte]
        rfl
      · simpa only [keep, ↓reduceIte] using guardEq
      · simpa only [keep, ↓reduceIte] using childrenEq
  | false =>
      have selected : accepted (SourceEqualityAccessorAllocation.constraint constraint.stored constraint.guard)
          children.length = false := keep
      obtain ⟨valid, growth, topField⟩ := SourceCurrentConjunctionFieldAllocation.empty_field _ checked.2.1
      have totalGrowth := SourceCurrentConjunctionEquality.grows_trans checked.2.2 growth
      have emptyAvailable : Values before.native.machine.heap ([.empty] : List (Value Symbol Guard)) := by
        intro child member
        have same : child = .empty := List.mem_singleton.mp member
        subst child
        exact InternedProbeProvenance.empty_available _
      obtain ⟨receipt, symbolEq, guardEq, childrenEq⟩ := raw_physical formulas solver inventory before ready admitted
        _ valid totalGrowth symbol top [.empty] topField emptyAvailable
      refine ⟨_, _, ⟨receipt, ?_, symbolEq, ?_, ?_⟩⟩
      · simp only [build, built.1, SourceEqualityMkEdgeAllocation.work,
          SourceEqualityMkEdgeAllocation.outputState, selected, Bool.false_eq_true, ↓reduceIte]
      · simpa only [keep, Bool.false_eq_true, ↓reduceIte] using guardEq
      · simpa only [keep, Bool.false_eq_true, ↓reduceIte] using childrenEq

/-- Raw contradiction bypasses the accessor and all child-list availability checks. -/
theorem build_contradictory (symbol : Symbol) (constraint : Allocated)
    (children : List (Value Symbol Guard)) (before : Checked width)
    (rejected : SourceEqualityMkEdgeAllocation.contradictory (raw constraint) = true) :
    build symbol constraint children before = (.ok (reject symbol before).1, (reject symbol before).2) := by
  have checked := SourceEqualityMkEdgeAllocation.check_contradictory constraint.stored constraint.guard
    children.length before.operations rejected
  simp only [build, SourceEqualityMkEdgeAllocation.build, checked, SourceEqualityMkEdgeAllocation.work,
    SourceEqualityMkEdgeAllocation.outputState, Bool.false_eq_true, ↓reduceIte, reject]

/-- Sentinel construction derives its own Top allocation and all full-state effects. -/
theorem reject_correct (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (symbol : Symbol) (before : Checked width) (ready : Ready before)
    (admitted : At formulas solver inventory before) :
    RejectReceipt formulas solver inventory symbol before (reject symbol before).1 (reject symbol before).2 := by
  obtain ⟨valid, growth, field⟩ := SourceCurrentConjunctionFieldAllocation.empty_field before.operations ready.good.operations
  have available : Values before.native.machine.heap ([.empty] : List (Value Symbol Guard)) := by
    intro child member
    have same : child = .empty := List.mem_singleton.mp member
    subst child
    exact InternedProbeProvenance.empty_available _
  obtain ⟨receipt, symbolEq, guardEq, childrenEq⟩ := raw_physical formulas solver inventory before ready admitted
    _ valid growth symbol top [.empty] field available
  exact ⟨receipt, rfl, symbolEq, guardEq, childrenEq⟩

/-- Every rejected constructor sentinel has empty independent edge language. -/
theorem RejectReceipt.empty {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    {symbol : Symbol} {before after : Checked width} {result : EdgeValue Symbol Guard}
    (receipt : RejectReceipt formulas solver inventory symbol before result after)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol) :
    ¬ InternedGuardedLanguage.edgeMeaning holds ambient result term :=
  SourceEqualityNativeDemandMismatchProvenance.empty_child_rejects result receipt.children holds ambient term

/-- Constructor rejection preserves exactly the raw edge language at this child arity. -/
theorem Receipt.language {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    {symbol : Symbol} {constraint : Allocated} {children : List (Value Symbol Guard)}
    {before after : Checked width} {result : EdgeValue Symbol Guard}
    (receipt : Receipt formulas solver inventory symbol constraint children before result after)
    (storedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints constraint.stored)
    (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol) :
    InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔
      ∃ terms, term = .node symbol terms ∧
        All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) children terms ∧
        SourceEqualityPCSGuard.holds formulas solver (raw constraint) term = true := by
  cases keep : accepted (raw constraint) children.length with
  | true =>
      rw [InternedGuardedLanguage.edgeMeaning_all]
      simp only [MergedColdInterpretation.EdgeMeaning, receipt.symbol, receipt.guard, receipt.children, keep, ↓reduceIte]
  | false =>
      have sentinel : result.children = [.empty] := by
        simpa only [keep, Bool.false_eq_true, ↓reduceIte] using receipt.children
      constructor
      · intro acceptedTerm
        exact False.elim (SourceEqualityNativeDemandMismatchProvenance.empty_child_rejects result sentinel _ ambient term acceptedTerm)
      · rintro ⟨terms, rfl, forest, constraintTrue⟩
        have active := SourceEqualityMkEdgeArity.ready_active constraint.stored constraint.guard storedReady
        have source := constraintTrue
        rw [SourceEqualityPCSGuard.public_eq formulas solver (raw constraint) active] at source
        have acceptedTerm := SourceEqualityMkEdgeArity.accepted_of_source formulas solver (raw constraint) active symbol terms source
        rw [← forest.length_eq, keep] at acceptedTerm
        cases acceptedTerm

end MicroCFTA.SourceCurrentAllocatedMkEdge
