import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEditShapes
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryPassResources

/-!
# Quantitative profiles through supplied class and pass reads

A class captures its actual entry forest and clears only its local slots.
The right fold produces its tail profile before the head captures that forest.
Every conclusion uses the same supplied actual reads and complete returned state.
No constructor headroom, range plan, or future result profile is an input.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryClassPassShapes
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedClassEdits (Class ClassReads)
open SourceCurrentAllocatedClassEditPlan
open SourceCurrentAllocatedClassPass (Fold FoldReads Pass PassReads)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow)
open SourceCurrentAllocatedFiniteOrdinaryNarrow (forest_trans forest_domain forest_propagate forest_height)
open MergedOrdinaryHeight (childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "CacheCovers" => SourceCurrentMemoMergeLanguage.CacheCovers
local notation "ClassRows" => SourceCurrentAllocatedFiniteOrdinaryClassResources.outputRows
local notation "ClassArity" => SourceCurrentAllocatedFiniteOrdinaryClassResources.outputArity
local notation "PassRows" => SourceCurrentAllocatedFiniteOrdinaryPassResources.outputRows
local notation "PassArity" => SourceCurrentAllocatedFiniteOrdinaryPassResources.outputArity
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- Supplied compiled class reads produce their fixed quantitative forest profile at the exact return. -/
theorem class_reads (inventory : Inventory) (record : SourceEqualityClassOrder.Record)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    {values results : List (Value Symbol Guard)} {before after : Checked width} {memo saved : Memo}
    {memos final : Memos} {actual : Class record values before memo results after saved}
    (reads : ClassReads formulas solver actual memos final)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (physical : PhysicalStored before.native.machine.heap memo)
    (profiles : Profiles memo) (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count) (pathsBound : ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound) :
    NativeStored after.native ∧ OutputStored after.native ∧ Profiles saved ∧
      ChildrenShape (ClassRows record rows count depth bound) (ClassArity arity) results ∧
      All₂ NodeNarrow values results ∧ results.length = values.length ∧ childrenHeight results ≤ bound := by
  have domain := ChildrenShape.domain values profile
  have domains : ∀ path ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) values :=
    fun path _ => SourceCurrentAllocatedFiniteOrdinaryTarget.forest_closed _ ready.semantic values available domain _
  cases reads with
  | edit lower =>
      have initialReady := SourceCurrentAllocatedSharedTargetState.initial_ready formulas solver inventory record values
        before.native.machine.heap before memo ready admitted
        (SourceEqualityRequiredCache.pure_keeps _ ready.semantic.ready) physical covered
      have initialStored := SourceCurrentAllocatedFiniteOrdinarySharedProfiles.initial_stored
        (rows := SourceCurrentAllocatedFiniteOrdinarySharedForceResources.targetRows record rows count depth bound)
        (arity := max arity 1) (bound := bound) before memo native output profiles
      have safe : SourceCurrentAllocatedSharedEditEffects.ListSafe (compiled record) values := by
        obtain ⟨entries, built⟩ := compiled_children record coherent active
        rw [built]
        exact compiled_safe record coherent values domains entries built
      have checked := SourceCurrentAllocatedFiniteOrdinaryEditShapes.list lower (compiled_populated record)
        (compiled_allowed record) initialReady available safe valid available coherent
        rows arity count depth bound rows arity bound profile lengthBound pathsBound heightBound initialStored profile heightBound
      exact ⟨checked.1.native, checked.1.output, checked.1.merge, checked.2⟩

/-- The actual earlier tail supplies the head class's captured forest, profile, and warm tables. -/
theorem fold (inventory : Inventory) {records values results} {before after : Checked width} {memo saved : Memo}
    {memos final : Memos} {actual : Fold records values before memo results after saved}
    (reads : FoldReads formulas solver actual memos final)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (physical : PhysicalStored before.native.machine.heap memo)
    (profiles : Profiles memo) (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count)
    (pathsBound : ∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound) :
    NativeStored after.native ∧ OutputStored after.native ∧ Profiles saved ∧
      ChildrenShape (PassRows records rows count depth bound) (PassArity records arity) results ∧
      All₂ NodeNarrow values results ∧ results.length = values.length ∧ childrenHeight results ≤ bound := by
  induction reads generalizing inventory with
  | nil => exact ⟨native, output, profiles, profile,
      SourceCurrentAllocatedFiniteOrdinaryNarrow.forest_refl (ChildrenShape.domain _ profile), rfl, heightBound⟩
  | @cons records values before memo middle step current record results after saved memos stepMemos final tail head first last ih =>
      have tailCoherent := fun own member => coherent own (List.mem_cons_of_mem record member)
      have tailActive := fun own member => active own (List.mem_cons_of_mem record member)
      have firstShapes := ih inventory tailCoherent tailActive ready admitted available physical profiles native output covered valid
        profile lengthBound (fun own member => pathsBound own (List.mem_cons_of_mem record member)) heightBound
      obtain ⟨next, firstReceipt, _, _, _⟩ := SourceCurrentAllocatedFiniteOrdinaryClassPass.fold formulas solver inventory first
        tailCoherent tailActive ready admitted available (ChildrenShape.domain values profile) physical covered native profiles.domain valid
      have headShapes := class_reads formulas solver next record (coherent _ List.mem_cons_self) (active _ List.mem_cons_self)
        last firstReceipt.ready firstReceipt.admitted firstReceipt.available firstReceipt.stored firstShapes.2.2.1 firstShapes.1 firstShapes.2.1
        firstReceipt.covered firstReceipt.globals.valid _ _ count depth bound firstShapes.2.2.2.1
        (by rw [firstShapes.2.2.2.2.2.1]; exact lengthBound) (pathsBound _ List.mem_cons_self) firstShapes.2.2.2.2.2.2
      exact ⟨headShapes.1, headShapes.2.1, headShapes.2.2.1, headShapes.2.2.2.1,
        forest_trans firstShapes.2.2.2.2.1 headShapes.2.2.2.2.1,
        headShapes.2.2.2.2.2.1.trans firstShapes.2.2.2.2.2.1, headShapes.2.2.2.2.2.2⟩

/-- Final empty propagation retains all quantitative stores and the same full-pass forest envelope. -/
theorem pass (inventory : Inventory) {records values results} {before after : Checked width} {memo saved : Memo}
    {memos final : Memos} {actual : Pass records values before memo results after saved}
    (reads : PassReads formulas solver actual memos final)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (physical : PhysicalStored before.native.machine.heap memo)
    (profiles : Profiles memo) (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count)
    (pathsBound : ∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound) :
    NativeStored after.native ∧ OutputStored after.native ∧ Profiles saved ∧
      ChildrenShape (PassRows records rows count depth bound) (PassArity records arity) results ∧
      All₂ NodeNarrow values results ∧ results.length = values.length ∧ childrenHeight results ≤ bound := by
  cases reads with
  | done remaining =>
      have checked := fold formulas solver inventory remaining coherent active ready admitted available physical profiles native output
        covered valid rows arity count depth bound profile lengthBound pathsBound heightBound
      have narrowed := forest_trans checked.2.2.2.2.1 (forest_propagate (forest_domain checked.2.2.2.2.1))
      refine ⟨checked.1, checked.2.1, checked.2.2.1, ?_, narrowed, narrowed.length_eq.symm,
        Nat.le_trans (forest_height narrowed) heightBound⟩
      unfold EqualityLeafProjectionRuntimeEmpty.propagate EqualityLeafProjectionRuntimeEmpty.erase
      split
      · exact SourceCurrentAllocatedFiniteOrdinaryOutputConstructors.children_of_members _ (fun _ member => by
          obtain ⟨_, _, rfl⟩ := List.mem_map.mp member
          trivial)
      · exact checked.2.2.2.1

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryClassPassShapes
