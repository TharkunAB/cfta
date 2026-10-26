import MicroCFTA.SourcePruningEnumerationHookCertificates

/-!
# Resources at recursive outcomes

Each output keeps its own caller, queries, metadata and enumeration cache.
A stopped result keeps an endpoint only when its execution returns one.
Post transport and resource padding do not change these observations.
-/
namespace MicroCFTA.SourcePruningEnumerationRecursive
open EnumerationState InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentAllocatedNativeResourceForecast (Le)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
open SourcePruningEnumerationNativeBranchCompletion (cost)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "reservationAdvance" => SourcePruningEnumerationIncomingReservation.advance

/-- Every ordered edge prefix costs at most the complete original edge list. -/
theorem cost_take_le (scs : List Suspended) (start : Nat)
    (edges : List (EdgeValue Symbol Constraint)) (count : Nat) :
    cost scs start (edges.take count) ≤ cost scs start edges := by
  induction edges generalizing count with
  | nil => simp only [List.take_nil, cost, Nat.le_refl]
  | cons edge rest ih =>
      cases count with
      | zero => exact Nat.zero_le _
      | succ count =>
          simp only [List.take_succ_cons, cost]
          exact Nat.add_le_add_left (ih count) _

variable {Typing : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- One emitted output retains its complete packet and resources at its own endpoint. -/
def OutputResources
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller width) (seed : Seed) (output : Output width Typing) : Prop :=
  ∃ (next : Inventory) (final : Memos) (metadata : Metadata Typing),
    Post formulas solver next original output.caller final ∧ final.query = output.queries ∧
    Packet formulas solver next output.caller final metadata output.cache ∧
    (output.metadata = none ∨ output.metadata = some metadata) ∧
    Fits seed.2 output.caller.checked ∧
    Heap (fun guard => guard ∈ seed.1) output.caller.checked.native.machine.heap

/-- A recursive outcome retains its actual endpoint and all emitted output packets. -/
def OutcomeResources
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller width) (seed : Seed)
    (outcome : SourcePruningEnumerationNativeContinuations.HookResult
      (Output width Typing) (Failure width Typing) width) : Prop :=
  ∃ (reached : Caller width) (next : Inventory) (final : Memos),
    Post formulas solver next original reached final ∧ Fits seed.2 reached.checked ∧
    Heap (fun guard => guard ∈ seed.1) reached.checked.native.machine.heap ∧
    match outcome with
    | .complete outputs caller queries =>
        caller = reached ∧ queries = final.query ∧
        ∀ output ∈ outputs, OutputResources formulas solver original seed output
    | .stopped outputs _ endpoint =>
        (endpoint = none ∨ endpoint = some (reached, final.query)) ∧
        ∀ output ∈ outputs, OutputResources formulas solver original seed output

variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {original middle : Caller width} {middleInventory : Inventory} {middleMemos : Memos}
variable {seed larger : Seed} {output : Output width Typing}
variable {outcome : SourcePruningEnumerationNativeContinuations.HookResult
  (Output width Typing) (Failure width Typing) width}

/-- An earlier Post composes without changing an output endpoint or its complete memos. -/
theorem OutputResources.post
    (post : Post formulas solver middleInventory original middle middleMemos)
    (resources : OutputResources formulas solver middle seed output) :
    OutputResources formulas solver original seed output := by
  obtain ⟨next, final, metadata, outputPost, query, packet, shape, fits, known⟩ := resources
  exact ⟨next, final, metadata, post.trans outputPost, query, packet, shape, fits, known⟩

/-- An earlier Post composes with the reached endpoint and every emitted output. -/
theorem OutcomeResources.post
    (post : Post formulas solver middleInventory original middle middleMemos)
    (resources : OutcomeResources formulas solver middle seed outcome) :
    OutcomeResources formulas solver original seed outcome := by
  obtain ⟨reached, next, final, reachedPost, fits, known, shape⟩ := resources
  refine ⟨reached, next, final, post.trans reachedPost, fits, known, ?_⟩
  cases outcome with
  | complete outputs caller queries =>
      obtain ⟨callerSame, querySame, outputsValid⟩ := shape
      exact ⟨callerSame, querySame, fun output member => (outputsValid output member).post post⟩
  | stopped outputs reason endpoint =>
      obtain ⟨endpointSame, outputsValid⟩ := shape
      exact ⟨endpointSame, fun output member => (outputsValid output member).post post⟩

/-- A larger numeric profile and alphabet retain the same actual output packet. -/
theorem OutputResources.mono (numeric : Le seed.2 larger.2)
    (alphabet : seed.1 ⊆ larger.1)
    (resources : OutputResources formulas solver original seed output) :
    OutputResources formulas solver original larger output := by
  obtain ⟨next, final, metadata, outputPost, query, packet, shape, fits, known⟩ := resources
  refine ⟨next, final, metadata, outputPost, query, packet, shape, fits.mono numeric, ?_⟩
  intro key edge found
  exact alphabet (known key edge found)

/-- Resource padding retains the reached endpoint and every output endpoint. -/
theorem OutcomeResources.mono (numeric : Le seed.2 larger.2)
    (alphabet : seed.1 ⊆ larger.1)
    (resources : OutcomeResources formulas solver original seed outcome) :
    OutcomeResources formulas solver original larger outcome := by
  obtain ⟨reached, next, final, reachedPost, fits, known, shape⟩ := resources
  refine ⟨reached, next, final, reachedPost, fits.mono numeric, ?_, ?_⟩
  · intro key edge found
    exact alphabet (known key edge found)
  · cases outcome with
    | complete outputs caller queries =>
        obtain ⟨callerSame, querySame, outputsValid⟩ := shape
        exact ⟨callerSame, querySame,
          fun output member => (outputsValid output member).mono numeric alphabet⟩
    | stopped outputs reason endpoint =>
        obtain ⟨endpointSame, outputsValid⟩ := shape
        exact ⟨endpointSame,
          fun output member => (outputsValid output member).mono numeric alphabet⟩

/-- An indexed hook output fits any supplied ceiling for the complete original edge cost. -/
theorem OutputResources.of_outputAt
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller width) (before : Cached) (seed : Seed) (scs : List Suspended)
    (edges : List (EdgeValue Symbol Constraint)) (index : Nat) (output : Output width Typing)
    (ceiling : Nat)
    (certificate : SourcePruningEnumerationNativeHookResources.OutputAt
      formulas solver original before seed scs edges index output)
    (enough : cost scs before.core.counter edges ≤ ceiling) :
    OutputResources formulas solver original (reservationAdvance seed ceiling) output := by
  let prefix := cost scs before.core.counter (edges.take (index + 1))
  have own : OutputResources formulas solver original (reservationAdvance seed prefix) output := certificate
  have counts : prefix ≤ ceiling :=
    Nat.le_trans (cost_take_le scs before.core.counter edges (index + 1)) enough
  have numeric := SourcePruningEnumerationIncomingReservation.advance_count_profile_mono seed counts
  have alphabet : (reservationAdvance seed prefix).1 ⊆ (reservationAdvance seed ceiling).1 := by
    obtain ⟨extra, same⟩ := Nat.exists_eq_add_of_le counts
    rw [same, SourcePruningEnumerationIncomingReservation.advance_add]
    exact SourcePruningEnumerationIncomingReservation.advance_alphabet_ge
      (reservationAdvance seed prefix) extra
  exact own.mono numeric alphabet

end MicroCFTA.SourcePruningEnumerationRecursive
