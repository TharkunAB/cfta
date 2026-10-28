import MicroCFTA.SourcePruningEnumerationPreparedOutcomeResources
import MicroCFTA.SourcePruningEnumerationArityOrigins

/-!
# Arity resources at the actual prepared outcome

The relation uses the prepared worker's own Failure type.
The aggregate endpoint retains arity even when no output exists.
Every emitted output retains its own arity heap and original resources.
Forgetting arity preserves all original endpoint witnesses.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedRecursive
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationRecursive (Packet Output OutputResources)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentAllocatedNativeResourceForecast (Le)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "ArityHeap" => SourcePruningEnumerationArityOrigins.Heap
variable {Typing : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]
local notation "Result" => SourcePruningEnumerationNativeContinuations.HookResult
  (Output width Typing) (Failure width Typing) width

/-- The same aggregate receipt retains arity at its endpoint and every actual output caller. -/
def OutcomeResourcesWithArity
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller width) (seed : Seed) (outcome : Result) : Prop :=
  ∃ (reached : Caller width) (next : Inventory) (final : Memos),
    Post formulas solver next original reached final ∧ Fits seed.2 reached.checked ∧
    Heap (fun guard => guard ∈ seed.1) reached.checked.native.machine.heap ∧
    ArityHeap reached.checked.native.machine.heap ∧
    match outcome with
    | .complete outputs caller queries =>
        caller = reached ∧ queries = final.query ∧
        ∀ output ∈ outputs, OutputResources formulas solver original seed output ∧
          ArityHeap output.caller.checked.native.machine.heap
    | .stopped outputs _ endpoint =>
        (endpoint = none ∨ endpoint = some (reached, final.query)) ∧
        ∀ output ∈ outputs, OutputResources formulas solver original seed output ∧
          ArityHeap output.caller.checked.native.machine.heap

/-- Forget only the new arity fields without changing the original aggregate witness. -/
theorem OutcomeResourcesWithArity.forget
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {original : Caller width} {seed : Seed} {outcome : Result}
    (resources : OutcomeResourcesWithArity formulas solver original seed outcome) :
    OutcomeResources formulas solver original seed outcome := by
  obtain ⟨reached, next, final, post, bounded, known, _arity, shape⟩ := resources
  refine ⟨reached, next, final, post, bounded, known, ?_⟩
  cases outcome with
  | complete outputs caller queries =>
      obtain ⟨callerSame, querySame, outputsValid⟩ := shape
      exact ⟨callerSame, querySame, fun output member => (outputsValid output member).1⟩
  | stopped outputs reason endpoint =>
      obtain ⟨endpointSame, outputsValid⟩ := shape
      exact ⟨endpointSame, fun output member => (outputsValid output member).1⟩

variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {original middle : Caller width} {middleInventory : Inventory} {middleMemos : Memos}
variable {seed larger : Seed}
variable {outcome : SourcePruningEnumerationNativeContinuations.HookResult
  (Output width Typing) (Failure width Typing) width}

/-- Compose the original Post while retaining every actual arity heap. -/
theorem OutcomeResourcesWithArity.post
    (post : Post formulas solver middleInventory original middle middleMemos)
    (resources : OutcomeResourcesWithArity formulas solver middle seed outcome) :
    OutcomeResourcesWithArity formulas solver original seed outcome := by
  obtain ⟨reached, next, final, reachedPost, bounded, known, arity, shape⟩ := resources
  refine ⟨reached, next, final, post.trans reachedPost, bounded, known, arity, ?_⟩
  cases outcome with
  | complete outputs caller queries =>
      obtain ⟨callerSame, querySame, outputsValid⟩ := shape
      exact ⟨callerSame, querySame, fun output member =>
        ⟨(outputsValid output member).1.post post, (outputsValid output member).2⟩⟩
  | stopped outputs reason endpoint =>
      obtain ⟨endpointSame, outputsValid⟩ := shape
      exact ⟨endpointSame, fun output member =>
        ⟨(outputsValid output member).1.post post, (outputsValid output member).2⟩⟩

/-- Pad numeric resources without changing either actual native endpoint. -/
theorem OutcomeResourcesWithArity.mono
    (numeric : Le seed.2 larger.2) (alphabet : seed.1 ⊆ larger.1)
    (resources : OutcomeResourcesWithArity formulas solver original seed outcome) :
    OutcomeResourcesWithArity formulas solver original larger outcome := by
  obtain ⟨reached, next, final, post, bounded, known, arity, shape⟩ := resources
  refine ⟨reached, next, final, post, bounded.mono numeric, ?_, arity, ?_⟩
  · intro key edge found
    exact alphabet (known key edge found)
  · cases outcome with
    | complete outputs caller queries =>
        obtain ⟨callerSame, querySame, outputsValid⟩ := shape
        exact ⟨callerSame, querySame, fun output member =>
          ⟨(outputsValid output member).1.mono numeric alphabet, (outputsValid output member).2⟩⟩
    | stopped outputs reason endpoint =>
        obtain ⟨endpointSame, outputsValid⟩ := shape
        exact ⟨endpointSame, fun output member =>
          ⟨(outputsValid output member).1.mono numeric alphabet, (outputsValid output member).2⟩⟩


end MicroCFTA.SourcePruningEnumerationPreparedRecursive
