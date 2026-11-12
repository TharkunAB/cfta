import MicroCFTA.SourcePruningEnumerationRecursivePacket
import MicroCFTA.SourceSynthesisHereditaryProgramFields

/-!
# No pending Program slot at finished selection

Actual noStop completion makes every allocated candidate flag false.
A pending Program value has an ordinary head and an actual true candidate flag.
The complete Packet and native lookup identify the same slot and heap.
This result does not derive Program roles for all later slots.
-/
namespace MicroCFTA.SourceSynthesisNoPendingProgramSlot
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint

private theorem flags_false {EnumGuard : Type}
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (finished : EnumerationPureSelection.next (fun _ => none) before = .done) :
    ∀ slot, slot < before.core.counter → before.expandable slot = false := by
  cases seen : EnumerationIndexSelection.candidates before with
  | nil =>
      intro slot inside
      cases flag : before.expandable slot with
      | false => rfl
      | true =>
          have member : slot ∈ EnumerationIndexSelection.candidates before :=
            List.mem_filter.mpr ⟨List.mem_range.mpr inside, flag⟩
          simp only [seen, List.not_mem_nil] at member
  | cons first rest =>
      have scan : EnumerationPureSelection.find before =
          some ((first :: rest).filter fun slot => (before.waiting slot).isNone) := by
        simp only [EnumerationPureSelection.find, seen, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
      change pickNext (fun _ => none) (EnumerationPureSelection.find before) = .done at finished
      rw [scan] at finished
      cases filtered : (first :: rest).filter (fun slot => (before.waiting slot).isNone) <;>
        simp [filtered, pickNext] at finished

variable {Typing : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {caller : SourceCurrentAllocatedPartialState.State width}
    {memos : EndpointMemoGateTrace.Memos}
    {metadata : SourcePruningRecordTypes.Metadata Typing}
    {before : EnumerationExpandableIndex.Cached Symbol Constraint}
    {valid : Constraint → Prop} {literal : String → Symbol}

/-- An actual pending Program slot contradicts actual noStop finished selection. -/
theorem no_pending_program_slot
    (packet : SourcePruningEnumerationRecursive.Packet formulas solver
      inventory caller memos metadata before)
    (finished : EnumerationPureSelection.next (fun _ => none) before = .done)
    (uv handle : Nat) (scs : List EnumerationState.Suspended) (value : Node)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (decoded : SourcePruningEnumerationNodes.lookupNode
      caller.checked.native.machine.heap handle = some value)
    (fields : SourceSynthesisHereditaryProgramFields.ValueFields valid literal value) :
    False := by
  obtain ⟨_roots, _paths, _storage, _realized, _waiting, flags⟩ := packet.valid
  have allocated : uv < before.core.counter := by
    rw [packet.safe.1.aligned]
    exact (List.getElem?_eq_some_iff.mp stored).1
  have inactive := flags_false before finished uv allocated
  have candidate : SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      (.unenumerated (some handle) scs) = some false := by
    simpa only [stored, Option.getD_some, inactive] using flags uv
  have ordinary : MergedOrdinaryHeight.recursiveBoundary value = false := by
    cases fields <;> rfl
  simp [SourcePruningEnumerationNativeIndex.candidate, decoded, ordinary] at candidate

end MicroCFTA.SourceSynthesisNoPendingProgramSlot
