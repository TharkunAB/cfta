import MicroCFTA.SourceCurrentAllocatedSharedEditLanguage
import MicroCFTA.SourceCurrentAllocatedClassEditPlan

#print axioms MicroCFTA.SourceCurrentAllocatedSharedEditLanguage.node
#print axioms MicroCFTA.SourceCurrentAllocatedSharedEditLanguage.children
#print axioms MicroCFTA.SourceCurrentAllocatedSharedEditLanguage.rows
#print axioms MicroCFTA.SourceCurrentAllocatedSharedEditLanguage.list
#check @MicroCFTA.SourceCurrentAllocatedSharedEditLanguage.node
#check @MicroCFTA.SourceCurrentAllocatedSharedEditLanguage.children
#check @MicroCFTA.SourceCurrentAllocatedSharedEditLanguage.rows
#check @MicroCFTA.SourceCurrentAllocatedSharedEditLanguage.list

namespace MicroCFTA.SourceCurrentAllocatedSharedEditLanguageProbe
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityEdits SourceEqualityEditMeaning SourceEqualitySharedEditEffects
open SourceCurrentEditDomains SourceCurrentAllocatedSharedEditGraph
open SourceCurrentAllocatedSharedEditEffects
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Inventory" => SourceCurrentAllocatedNativeInventoryState.Inventory
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "MemoValid" => EndpointMemoGateTrace.Valid
local notation "pcs" => SourceEqualityPCSGuard.holds
local notation "meaning" => InternedGuardedLanguage.meaning
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula)
variable (solver : SourceGuards.Entailment FullSyntax.Formula)
variable (base : Heap) (record : SourceEqualityClassOrder.Record)
variable (originals : List (Value Symbol Guard))
variable (ambient : InternedGuardedLanguage.Env Symbol)
variable (symbol : Symbol) (rootTerms : List (Term Symbol))
variable {inventory : Inventory} {edits : Edits EqualityNormalize.Path}
variable {values results : List (Value Symbol Guard)} {before after : SharedState width}
variable {memos final : Memos} {actual : EditList record originals edits values before results after}
variable (read : ListReads formulas solver base actual memos final)
variable (valid : SourceEqualityEdits.Valid edits) (populated : Populated edits) (allowed : Allowed record edits)
variable (ready : Ready formulas solver inventory record originals base before)
variable (available : Values before.checked.native.machine.heap values) (safe : ListSafe edits values)
variable (memoValid : MemoValid before.checked.native.machine.heap memos)

-- The narrowing theorem uses the same actual output forest and checked states.
example (terms : List (Term Symbol))
    (accepted : All₂ (meaning (pcs formulas solver) ambient) results terms) :
    All₂ (meaning (pcs formulas solver) ambient) values terms :=
  (SourceCurrentAllocatedSharedEditLanguage.list formulas solver base record originals ambient symbol rootTerms
    read valid populated allowed ready available safe memoValid terms).1 accepted

-- Original class satisfaction and the exact compiled condition retain an accepted forest.
example (terms : List (Term Symbol))
    (captured : All₂ (meaning (pcs formulas solver) ambient) originals rootTerms)
    (satisfied : EqualityNormalize.ClassSat (.node symbol rootTerms) record.paths)
    (matched : SourceEqualityEditAPI.ListCondition
      (fun path part => (Term.node symbol rootTerms).atPath path = some part) edits terms)
    (accepted : All₂ (meaning (pcs formulas solver) ambient) values terms) :
    All₂ (meaning (pcs formulas solver) ambient) results terms :=
  (SourceCurrentAllocatedSharedEditLanguage.list formulas solver base record originals ambient symbol rootTerms
    read valid populated allowed ready available safe memoValid terms).2 captured satisfied matched accepted

-- A list-root callback is ignored even when the captured class has other paths.
example (path : EqualityNormalize.Path) (terms : List (Term Symbol))
    (ready : Ready formulas solver inventory record originals base before)
    (available : Values before.checked.native.machine.heap values)
    (member : path ∈ record.paths)
    (accepted : All₂ (meaning (pcs formulas solver) ambient) values terms) :
    All₂ (meaning (pcs formulas solver) ambient) values terms := by
  have law := SourceCurrentAllocatedSharedEditLanguage.list formulas solver base record originals ambient symbol rootTerms
    (actual := .leaf (target := path) (values := values) (state := before))
    (ListReads.leaf (memos := memos)) (by simp only [SourceEqualityEdits.Valid]) (by simp only [Populated]) (by simpa only [Allowed, All] using member)
    ready available trivial memoValid terms
  exact law.1 accepted

-- Conditional exactness follows when the captured forest is the edited forest.
example {actual : EditList record values edits values before results after}
    (read : ListReads formulas solver base actual memos final)
    (ready : Ready formulas solver inventory record values base before)
    (allowed : Allowed record edits)
    (satisfied : EqualityNormalize.ClassSat (.node symbol rootTerms) record.paths)
    (matched : SourceEqualityEditAPI.ListCondition
      (fun path part => (Term.node symbol rootTerms).atPath path = some part) edits rootTerms) :
    All₂ (meaning (pcs formulas solver) ambient) results rootTerms ↔
      All₂ (meaning (pcs formulas solver) ambient) values rootTerms := by
  have law := SourceCurrentAllocatedSharedEditLanguage.list formulas solver base record values ambient symbol rootTerms
    read valid populated allowed ready available safe memoValid rootTerms
  exact ⟨law.1, fun accepted => law.2 accepted satisfied matched accepted⟩

end MicroCFTA.SourceCurrentAllocatedSharedEditLanguageProbe

namespace MicroCFTA.SourceCurrentAllocatedSharedEditLanguageCompiledProbe
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityEdits SourceCurrentEditDomains SourceCurrentAllocatedSharedEditGraph
open SourceCurrentAllocatedSharedEditEffects
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Inventory" => SourceCurrentAllocatedNativeInventoryState.Inventory
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "meaning" => InternedGuardedLanguage.meaning
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

-- Actual compiler readback discharges the condition used by retention.
example (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (base : Heap) (record : SourceEqualityClassOrder.Record)
    (values results : List (Value Symbol Guard)) (before after : SharedState width)
    (memos final : Memos) (inventory : Inventory)
    (actual : EditList record values (SourceCurrentAllocatedClassEditPlan.compiled record) values before results after)
    (read : ListReads formulas solver base actual memos final)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (ready : Ready formulas solver inventory record values base before)
    (available : Values before.checked.native.machine.heap values)
    (safe : ListSafe (SourceCurrentAllocatedClassEditPlan.compiled record) values)
    (valid : EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos)
    (ambient : InternedGuardedLanguage.Env Symbol) (symbol : Symbol) (terms : List (Term Symbol))
    (satisfied : EqualityNormalize.ClassSat (.node symbol terms) record.paths) :
    All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) results terms ↔
      All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms := by
  have bounds := SourceCurrentAllocatedSharedEditLanguage.list formulas solver base record values ambient symbol terms
    read (SourceCurrentAllocatedClassEditPlan.compiled_valid record)
    (SourceCurrentAllocatedClassEditPlan.compiled_populated record)
    (SourceCurrentAllocatedClassEditPlan.compiled_allowed record) ready available safe valid terms
  exact ⟨bounds.1, fun accepted => bounds.2 accepted satisfied
    (SourceCurrentAllocatedClassEditPlan.compiled_condition record coherent active symbol terms) accepted⟩

end MicroCFTA.SourceCurrentAllocatedSharedEditLanguageCompiledProbe
