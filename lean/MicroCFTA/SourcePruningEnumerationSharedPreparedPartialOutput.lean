import MicroCFTA.SourcePruningEnumerationSharedPreparedHookCertificates
import MicroCFTA.SourcePruningEnumerationPartialOutput

/-!
# Partial observation of the same shared prepared output

The current output supplies its packet, native caller and complete memos.
Root allocation remains an explicit current fact. The resource packet alone
does not relate enumeration counters. The partial observation precedes every
model observer and does not assert that a satisfying assignment exists.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive
open Language Fragments EnumerationState EnumerationCorrectness InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed)
open SourcePruningEnumerationRecursive (Packet callback_frame)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {Typing : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {original : Caller width} {seed : Seed} {output : Output width Typing}

/-- Derive the exact partial root observation from the current prepared output packet. -/
theorem OutputResources.root_partial_complete
    (resources : OutputResources formulas solver original seed output)
    (inside : 0 < output.cache.core.counter) :
    ∃ (next : Inventory) (final : Memos) (metadata : Metadata Typing),
      Post formulas solver next original output.caller final ∧ final.query = output.queries ∧
      Packet formulas solver next output.caller final metadata output.cache ∧
      (output.metadata = none ∨ output.metadata = some metadata) ∧
      Fits seed.2 output.caller.checked ∧
      Heap (fun guard => guard ∈ seed.1) output.caller.checked.native.machine.heap ∧
      ∃ (level : Nat → Nat) (frontier : Nat),
        EnumerationOrder.Stratified output.cache.core level frontier ∧
        ∃ (bound : Nat) (observedTerm : Term (PartialSymbol Symbol)) (after : Core),
          (∀ extra,
            Success (SourcePruningEnumerationPartialOutput.rootPartial
              output.caller.checked.native.machine.heap (bound + extra))
              output.cache.core observedTerm after ∧
            ExceptT.run (SourcePruningEnumerationPartialOutput.rootPartial
              output.caller.checked.native.machine.heap (bound + extra) output.cache.core) =
              [.ok (observedTerm, after)]) ∧
          EnumerationDriver.RenderStable output.cache.core after ∧
          EnumerationCompressionFrame.Frame output.cache.core after ∧
          EnumerationOrder.Stratified after level frontier ∧
          Packet formulas solver next output.caller final metadata
            (EnumerationExpandableIndex.frame after output.cache) ∧
          ∀ (language : NodeLanguage Symbol) (meaning : Constraint → Term Symbol → Prop)
            (assignment : Nat → Term Symbol),
            Satisfies language meaning assignment output.cache.core →
              Satisfies language meaning assignment after ∧
              SourcePruningPartialMatch.Completes assignment observedTerm (assignment 0) := by
  obtain ⟨next, final, metadata, post, querySame, packet, metadataSame, fits, known⟩ := resources
  obtain ⟨level, frontier, ordered⟩ := packet.ordered
  obtain ⟨bound, observedTerm, after, actual, stable, frame, afterOrder, models⟩ :=
    SourcePruningEnumerationPartialOutput.rootPartial_complete
      output.caller.checked.native.machine.heap level frontier output.cache.core
      packet.safe ordered inside
  refine ⟨next, final, metadata, post, querySame, packet, metadataSame, fits, known,
    level, frontier, ordered, bound, observedTerm, after, actual, stable, frame, afterOrder,
    ?_, models⟩
  exact callback_frame packet metadata after stable.safe frame ⟨level, frontier, afterOrder⟩ (by
    intro group member entry listed
    rw [frame.counter]
    exact packet.bounded group member entry listed)

end MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive
