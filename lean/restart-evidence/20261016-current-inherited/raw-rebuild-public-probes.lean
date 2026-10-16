import MicroCFTA.SourceCurrentAllocatedRawRebuild
import MicroCFTA.EqualityLeafProjectionNullaryEdit

namespace MicroCFTA.RawRebuildPublicProbe
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready)
open SourceCurrentAllocatedRawRebuild
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

#print axioms edge
#print axioms edge_same_arity
#print axioms SourceCurrentAllocatedRawRebuild.modify
#print axioms edge_verified
#print axioms EdgeReceipt.language
#print axioms modify_unchanged
#print axioms modify_verified
#check @edge_verified
#check @EdgeReceipt.language
#check @modify_verified
#check @NodeReceipt.language

-- The source same-arity branch is independent of every checked fallback.
example (checked : Symbol → List (Value Symbol Guard) → Guard → Work Symbol Guard (EdgeValue Symbol Guard))
    (original : EdgeValue Symbol Guard) (children : List (Value Symbol Guard)) (before : Checked width)
    (same : children.length = original.children.length) :
    edge original children before =
      let built := run (EqualityLeafProjectionSetChildren.setChildren checked original children) before.native.machine.heap
      (built.1, SourceCurrentAllocatedQueryMemo.advancePhysical before ⟨built.2, before.operations⟩) :=
  edge_same_arity checked original children before same

-- Raw rebuilding never demands or allocates an equality field.
example (original : EdgeValue Symbol Guard) (children : List (Value Symbol Guard)) (before : Checked width) :
    (edge original children before).2.operations = before.operations ∧
      (edge original children before).2.native.nodes = before.native.nodes ∧
      (edge original children before).2.native.edges = before.native.edges ∧
      (edge original children before).2.native.machine.domains = before.native.machine.domains :=
  ⟨rfl, rfl, rfl, rfl⟩

-- Reusing complete resident children gives a literal edge hit and the identical whole checked state.
example (original : EdgeValue Symbol Guard) (before : Checked width) (ready : Ready before)
    (resident : EdgeResident before.native.machine.heap original) :
    edge original original.children before = (original, before) := by
  have replay := EqualityLeafProjectionNullaryEdit.resident_edge_replay original before.native.machine.heap
    ready.semantic.ready.semantic.1.normal.facts.coherent resident
  simp only [edge, replay]
  rfl

-- Identical ordered row identities bypass the ordinary node constructor.
example (original : Value Symbol Guard) (rows : List (EdgeValue Symbol Guard)) (before : Checked width) :
    modify original rows rows before = (original, before) :=
  modify_unchanged original rows rows before rfl

-- Changed ordered identities select the actual ordinary constructor, without an equality operation.
example (original : Value Symbol Guard) (oldRows newRows : List (EdgeValue Symbol Guard)) (before : Checked width)
    (different : newRows.map (fun row => row.entry.identity) ≠ oldRows.map (fun row => row.entry.identity)) :
    modify original oldRows newRows before =
      ((run (makeNode newRows) before.native.machine.heap).1,
        SourceCurrentAllocatedQueryMemo.advancePhysical before
          ⟨(run (makeNode newRows) before.native.machine.heap).2, before.operations⟩) := by
  simp only [SourceCurrentAllocatedRawRebuild.modify, SourceEqualityPartialNodeRebuild.modify, different, ↓reduceIte]
  rfl

-- The returned raw field remains available from the actual resident cache, not an acceptance test.
example (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (original : EdgeValue Symbol Guard) (children : List (Value Symbol Guard)) (before : Checked width)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (resident : EdgeResident before.native.machine.heap original) (available : Values before.native.machine.heap children)
    (same : children.length = original.children.length) :
    SourceCurrentConjunctionEquality.FieldAvailable (edge original children before).2.operations original.entry.key.constraint := by
  have receipt := edge_verified formulas solver inventory original children before ready admitted resident available same
  have field := receipt.ready.good.fields _ _ receipt.resident
  simpa only [receipt.guard] using field

-- The generic edge law specializes directly to independent PCS guards.
example (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (original : EdgeValue Symbol Guard) (children : List (Value Symbol Guard)) (before : Checked width)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (resident : EdgeResident before.native.machine.heap original) (available : Values before.native.machine.heap children)
    (same : children.length = original.children.length) (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol) :
    InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient (edge original children before).1 term ↔
      ∃ terms, term = .node original.entry.key.symbol terms ∧
        All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) children terms ∧
        SourceEqualityPCSGuard.holds formulas solver original.entry.key.constraint term = true :=
  (edge_verified formulas solver inventory original children before ready admitted resident available same).language _ ambient term

-- All ordered resident replacement rows determine the complete node language, including open rows.
example (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (entry : Interned InternedBinderProtocol.NodeKey)
    (oldRows newRows : List (EdgeValue Symbol Guard)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (before : Checked width) (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Available before.native.machine.heap (.node entry oldRows depth free))
    (resident : Edges before.native.machine.heap newRows)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol) :
    InternedGuardedLanguage.meaning holds ambient (modify (.node entry oldRows depth free) oldRows newRows before).1 term ↔
      ∃ row ∈ newRows, InternedGuardedLanguage.edgeMeaning holds ambient row term :=
  (modify_verified formulas solver inventory entry oldRows newRows depth free before ready admitted available resident).language
    holds ambient term

-- Removing all rows produces an empty node language, with no closed-row premise.
example (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (entry : Interned InternedBinderProtocol.NodeKey)
    (oldRows : List (EdgeValue Symbol Guard)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (before : Checked width) (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Available before.native.machine.heap (.node entry oldRows depth free))
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol) :
    ¬ InternedGuardedLanguage.meaning holds ambient (modify (.node entry oldRows depth free) oldRows [] before).1 term := by
  have receipt := modify_verified formulas solver inventory entry oldRows [] depth free before ready admitted available
    (by intro row member; cases member)
  rw [receipt.language holds ambient term]
  simp

end MicroCFTA.RawRebuildPublicProbe
