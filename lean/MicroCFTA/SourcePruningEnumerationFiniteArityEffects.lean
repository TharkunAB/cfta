import MicroCFTA.SourcePruningEnumerationFiniteArityContract

/-!
# Transport of finite arity outcome resources

An earlier Post changes only the original caller in the certificate.
Padding changes only the numeric profile and guard alphabet.
Both operations retain the actual endpoint and each output caller.
-/
namespace MicroCFTA.SourcePruningEnumerationRecursive
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentAllocatedNativeResourceForecast (Le)
open SourcePruningEnumerationIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable {Typing : Type} {width : Nat}
variable [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)]
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

end MicroCFTA.SourcePruningEnumerationRecursive
