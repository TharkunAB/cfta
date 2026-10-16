import MicroCFTA.SourceCurrentAllocatedMkEdge
import MicroCFTA.SourceEqualityPartialNodeRebuild
import MicroCFTA.EqualityLeafProjectionSetChildren
import MicroCFTA.SourceCurrentRequiredHeapEffects

/-!
# Raw same-arity reconstruction in the current checked state

Same-arity setChildren directly interns the original full raw field.
It does not repeat mkEdge checks or demand its equality accessor. The
ordinary modifyNode branch compares ordered physical edge identities.
Equal lists retain the original node; changed lists use makeNode. These
proofs permit open available children and rows. They reuse pure constructor
definitions, not the historical native execution theorem.
-/
namespace MicroCFTA.SourceCurrentAllocatedRawRebuild
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical advance_extension)
open SourceCurrentConjunctionClassScan (Ready)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "FieldAvailable" => SourceCurrentConjunctionEquality.FieldAvailable
variable [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- Directly intern an equal-arity replacement with the original complete raw field. -/
def edge (original : EdgeValue Symbol Guard) (children : List (Value Symbol Guard)) (before : Checked width) :
    EdgeValue Symbol Guard × Checked width :=
  let built := run (makeEdge original.entry.key.symbol original.entry.key.constraint children) before.native.machine.heap
  (built.1, advancePhysical before ⟨built.2, before.operations⟩)

/-- Every checked fallback selects this exact raw branch when child arity is unchanged. -/
theorem edge_same_arity
    (checked : Symbol → List (Value Symbol Guard) → Guard → Work Symbol Guard (EdgeValue Symbol Guard))
    (original : EdgeValue Symbol Guard) (children : List (Value Symbol Guard)) (before : Checked width)
    (same : children.length = original.children.length) :
    edge original children before =
      let built := run (EqualityLeafProjectionSetChildren.setChildren checked original children) before.native.machine.heap
      (built.1, advancePhysical before ⟨built.2, before.operations⟩) := by
  rw [EqualityLeafProjectionSetChildren.same_arity checked original children same]
  rfl

/-- Execute the literal ordered-identity modifyNode definition and retain equality operations. -/
def modify (original : Value Symbol Guard) (oldRows newRows : List (EdgeValue Symbol Guard)) (before : Checked width) :
    Value Symbol Guard × Checked width :=
  let built := SourceEqualityPartialNodeRebuild.modify original oldRows newRows before.native
  (built.1, ⟨built.2, before.operations⟩)

/-- Constructor-only reconstruction retains the same native tables and equality operations. -/
structure Receipt (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (before after : Checked width) : Prop where
  ready : Ready after
  admitted : At formulas solver inventory after
  effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before) (physical after)
  extension : SourceRecursiveIntersectionKernel.Extension before.native.machine after.native.machine
  operations : after.operations = before.operations
  nodes : after.native.nodes = before.native.nodes
  edges : after.native.edges = before.native.edges
  domains : after.native.machine.domains = before.native.machine.domains

/-- A raw edge reconstruction retains its symbol, full field, and ordered children. -/
structure EdgeReceipt (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (original : EdgeValue Symbol Guard) (children : List (Value Symbol Guard))
    (before : Checked width) (result : EdgeValue Symbol Guard) (after : Checked width) : Prop
    extends Receipt formulas solver inventory before after where
  actual : edge original children before = (result, after)
  resident : EdgeResident after.native.machine.heap result
  symbol : result.entry.key.symbol = original.entry.key.symbol
  guard : result.entry.key.constraint = original.entry.key.constraint
  children : result.children = children
  arity : result.children.length = original.children.length

/-- An ordinary node reconstruction retains availability and the actual completed row list. -/
structure NodeReceipt (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (original : Value Symbol Guard) (oldRows newRows : List (EdgeValue Symbol Guard))
    (before : Checked width) (result : Value Symbol Guard) (after : Checked width) : Prop
    extends Receipt formulas solver inventory before after where
  actual : modify original oldRows newRows before = (result, after)
  available : Available after.native.machine.heap result
  language : ∀ holds ambient term,
    InternedGuardedLanguage.meaning holds ambient result term ↔
      ∃ row ∈ newRows, InternedGuardedLanguage.edgeMeaning holds ambient row term

omit [DecidableEq (EdgeKey Symbol Guard)] in
private theorem advance_receipt (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (before : Checked width) (ready : Ready before) (admitted : At formulas solver inventory before)
    (heap : State Symbol Guard)
    (effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before) ⟨heap, before.operations⟩) :
    Receipt formulas solver inventory before (advancePhysical before ⟨heap, before.operations⟩) := by
  have extension := advance_extension before _ effects
  exact ⟨SourceCurrentConjunctionClassScan.advance_ready before _ ready effects,
    admitted.advance _ extension, effects, extension, rfl, rfl, rfl, rfl⟩

/-- An actual resident field and available equal-arity replacements derive every raw rebuild effect. -/
theorem edge_verified (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (original : EdgeValue Symbol Guard) (children : List (Value Symbol Guard)) (before : Checked width)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (resident : EdgeResident before.native.machine.heap original)
    (available : Values before.native.machine.heap children) (same : children.length = original.children.length) :
    EdgeReceipt formulas solver inventory original children before (edge original children before).1 (edge original children before).2 := by
  have field := ready.good.fields original.entry.key original resident
  have actual := SourceEqualityRequiredCache.edge original.entry.key.symbol original.entry.key.constraint children
    before.native.machine.heap ready.semantic.ready available
  have semantic := SourceEqualityRequiredSemanticCache.edge original.entry.key.symbol original.entry.key.constraint children
    before.native.machine.heap ready.semantic available
  have fields := SourceEqualityAnnotationHeap.run (FieldAvailable before.operations) _
    (SourceEqualityAnnotationHeap.makeEdge (FieldAvailable before.operations) original.entry.key.symbol
      original.entry.key.constraint children field) before.native.machine.heap ready.good.fields
  have effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before)
      ⟨(run (makeEdge original.entry.key.symbol original.entry.key.constraint children) before.native.machine.heap).2,
        before.operations⟩ :=
    ⟨actual.1, ⟨semantic, ready.costs, ready.good.operations, fields⟩,
      SourceEqualityConstraintMemoAllocation.grows_refl _⟩
  have complete := MergedPhysicalGroupEdges.makeEdge_fields before.native.machine.heap
    ready.semantic.ready.semantic.1.normal.facts original.entry.key.symbol original.entry.key.constraint children available
  exact ⟨advance_receipt formulas solver inventory before ready admitted _ effects,
    rfl, actual.2.1, complete.1, complete.2.1, complete.2.2,
    (congrArg List.length complete.2.2).trans same⟩

/-- Raw reconstruction has exactly the original full guard and the replacement child languages. -/
theorem EdgeReceipt.language {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    {original result : EdgeValue Symbol Guard} {children : List (Value Symbol Guard)} {before after : Checked width}
    (receipt : EdgeReceipt formulas solver inventory original children before result after)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol) :
    InternedGuardedLanguage.edgeMeaning holds ambient result term ↔
      ∃ terms, term = .node original.entry.key.symbol terms ∧
        All₂ (InternedGuardedLanguage.meaning holds ambient) children terms ∧
        holds original.entry.key.constraint term = true := by
  rw [InternedGuardedLanguage.edgeMeaning_all]
  simp only [MergedColdInterpretation.EdgeMeaning, receipt.symbol, receipt.guard, receipt.children]

/-- Equal ordered physical row identities retain the original full checked state. -/
theorem modify_unchanged (original : Value Symbol Guard) (oldRows newRows : List (EdgeValue Symbol Guard))
    (before : Checked width)
    (same : newRows.map (fun row => row.entry.identity) = oldRows.map (fun row => row.entry.identity)) :
    modify original oldRows newRows before = (original, before) := by
  simp only [modify, SourceEqualityPartialNodeRebuild.modify, same, ↓reduceIte]

/-- Both actual ordinary modifyNode branches derive readiness and complete row-union language. -/
theorem modify_verified (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (entry : Interned InternedBinderProtocol.NodeKey) (oldRows newRows : List (EdgeValue Symbol Guard))
    (depth : Nat) (free : List InternedBinderProtocol.Reference) (before : Checked width)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Available before.native.machine.heap (.node entry oldRows depth free))
    (resident : Edges before.native.machine.heap newRows) :
    NodeReceipt formulas solver inventory (.node entry oldRows depth free) oldRows newRows before
      (modify (.node entry oldRows depth free) oldRows newRows before).1
      (modify (.node entry oldRows depth free) oldRows newRows before).2 := by
  have facts := ready.semantic.ready.semantic.1.normal.facts
  by_cases same : newRows.map (fun row => row.entry.identity) = oldRows.map (fun row => row.entry.identity)
  · have oldResident := resident_edges before.native.machine.heap facts.linked _ available.resident
    have equal := edge_lists_equal before.native.machine.heap facts.coherent newRows oldRows resident oldResident same
    have unchanged := modify_unchanged (.node entry oldRows depth free) oldRows newRows before same
    rw [unchanged]
    have physicalReady := SourceCurrentAllocatedConjunctionMemo.ready before ready.good ready.semantic ready.costs
    refine ⟨⟨ready, admitted, .refl _ physicalReady, .refl _, rfl, rfl, rfl, rfl⟩,
      unchanged, available, ?_⟩
    intro holds ambient term
    rw [equal]
    exact SourceEqualityPartialNodeRebuild.node_meaning holds ambient entry oldRows depth free term
  · have constructor := SourceCurrentRequiredHeapEffects.node_constructor (FieldAvailable before.operations)
      newRows before.native.machine.heap ready.semantic ready.costs ready.good.fields resident
    have effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before)
        ⟨(run (makeNode newRows) before.native.machine.heap).2, before.operations⟩ :=
      ⟨constructor.1, ⟨constructor.2.1, constructor.2.2.1, ready.good.operations, constructor.2.2.2.1⟩,
        SourceEqualityConstraintMemoAllocation.grows_refl _⟩
    have stateReceipt := advance_receipt formulas solver inventory before ready admitted _ effects
    have built : modify (.node entry oldRows depth free) oldRows newRows before =
        ((run (makeNode newRows) before.native.machine.heap).1,
          advancePhysical before ⟨(run (makeNode newRows) before.native.machine.heap).2, before.operations⟩) := by
      simp only [modify, SourceEqualityPartialNodeRebuild.modify, same, ↓reduceIte]
      rfl
    rw [built]
    refine ⟨stateReceipt, built, constructor.2.2.2.2, ?_⟩
    intro holds ambient term
    apply (InternedGuardedLanguage.makeNode_exact before.native.machine.heap facts holds ambient newRows resident term).trans
    apply exists_congr
    intro row
    exact and_congr_right fun _ => (InternedGuardedLanguage.edgeMeaning_all holds ambient row term).symm

end MicroCFTA.SourceCurrentAllocatedRawRebuild
