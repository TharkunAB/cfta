import MicroCFTA.SourcePruningEnumerationPreparedRecursive
import MicroCFTA.SourcePruningEnumerationPreparedHeadAncestryExtension
import MicroCFTA.SourcePruningEnumerationOpaqueAncestryExtension
import MicroCFTA.SourcePruningEnumerationPrefixAncestryExtension

/-!
# Recursion ancestry in concrete prepared diagnostics

The predicates cover every attached Cached value in the actual receipt and failure types.
Raw Core rows are separate from Cached values. Output caches have a separate theorem.
The observers use actual captured, opaque and selected-prefix observations.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedRecursive
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationAncestryExtension
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
local notation "Output" => SourcePruningEnumerationRecursive.Output
local notation "HookResult" => SourcePruningEnumerationNativeContinuations.HookResult
local notation "Fold" => SourcePruningEnumerationNativeContinuations.Result
variable {Typing Key : Type} {width : Nat}

/-- Every concrete receipt cache extends the original per-slot recursion histories. -/
def ReceiptAncestry (original : Core) : Receipt width → Prop
  | .complete _ _ _ after | .rejected _ _ after | .stopped _ _ (some after) =>
      Extends original after.core
  | _ => True

/-- Retain the prefix candidate and every cache in an attached ordinary scan. -/
def PrefixAncestry (original : Core) : SourcePruningEnumerationSelectedStep.Result width Typing → Prop
  | .stopped _ _ => True
  | .parked _ candidate _ =>
      match candidate with
      | none => True
      | some after => Extends original after.core
  | .narrowed _ _ _ _ _ candidate _ ordinary =>
      (match candidate with
        | none => True
        | some after => Extends original after.core) ∧
      match ordinary with
      | none | some (_, none) => True
      | some (_, some (.complete processed _ _)) =>
          ∀ receipt ∈ processed, ReceiptAncestry original receipt
      | some (_, some (.stopped processed current)) =>
          (∀ receipt ∈ processed, ReceiptAncestry original receipt) ∧
          match current with
          | none => True
          | some receipt => ReceiptAncestry original receipt

/-- Retain every Cached value in the actual recursive stop diagnostic. -/
def FailureAncestry (original : Core) : Failure width Typing → Prop
  | .exhausted _ _ before => Extends original before.core
  | .selected _ observed => PrefixAncestry original observed
  | .callback _ _ | .preparation _ _ => True
  | .alternatives _ processed current =>
      (∀ receipt ∈ processed, ReceiptAncestry original receipt) ∧
      match current with
      | .edge candidate =>
          match candidate with
          | none => True
          | some receipt => ReceiptAncestry original receipt
      | .continuation receipt reason _ =>
          ReceiptAncestry original receipt ∧ FailureAncestry original reason

/-- Complete outcomes have no diagnostic; stopped outcomes retain every attached cache. -/
def OutcomeDiagnosticAncestry (original : Core) :
    HookResult (Output width Typing) (Failure width Typing) width → Prop
  | .complete _ _ _ => True
  | .stopped _ reason _ => FailureAncestry original reason

/-- An earlier extension transports the ancestry of every attached receipt cache. -/
theorem ReceiptAncestry.mono {original middle : Core} {receipt : Receipt width}
    (extension : Extends original middle) (retained : ReceiptAncestry middle receipt) :
    ReceiptAncestry original receipt := by
  cases receipt with
  | unhandled => trivial
  | rejected caller queries after | complete fragment caller queries after =>
      exact extension.trans retained
  | stopped fragments observation candidate =>
      cases candidate with
      | none => trivial
      | some after => exact extension.trans retained

/-- An earlier extension transports all candidate and ordinary diagnostic caches. -/
theorem PrefixAncestry.mono {original middle : Core}
    {observed : SourcePruningEnumerationSelectedStep.Result width Typing}
    (extension : Extends original middle) (retained : PrefixAncestry middle observed) :
    PrefixAncestry original observed := by
  cases observed with
  | stopped read checked => trivial
  | parked checked candidate raw =>
      cases candidate with
      | none => trivial
      | some after => exact extension.trans retained
  | narrowed checked prepared caller queries action candidate right ordinary =>
      obtain ⟨candidateKept, ordinaryKept⟩ := retained
      constructor
      · cases candidate with
        | none => trivial
        | some after => exact extension.trans candidateKept
      · cases ordinary with
        | none => trivial
        | some pair =>
            rcases pair with ⟨raw, result⟩
            cases result with
            | none => trivial
            | some result =>
                cases result with
                | complete processed reached saved =>
                    exact fun receipt member => ReceiptAncestry.mono extension (ordinaryKept receipt member)
                | stopped processed current =>
                    constructor
                    · exact fun receipt member => ReceiptAncestry.mono extension (ordinaryKept.1 receipt member)
                    · cases current with
                      | none => trivial
                      | some receipt => exact ReceiptAncestry.mono extension ordinaryKept.2

/-- An earlier extension transports every cache in the recursively retained failure. -/
theorem FailureAncestry.mono {original middle : Core} {reason : Failure width Typing}
    (extension : Extends original middle) (retained : FailureAncestry middle reason) :
    FailureAncestry original reason := by
  cases reason with
  | exhausted uv metadata before => exact extension.trans retained
  | selected uv observed => exact PrefixAncestry.mono extension retained
  | callback uv raw | preparation uv raw => trivial
  | alternatives uv processed current =>
      cases current with
      | edge candidate =>
          cases candidate with
          | none =>
              constructor
              · exact fun receipt member => ReceiptAncestry.mono extension (retained.1 receipt member)
              · trivial
          | some receipt =>
              constructor
              · exact fun item member => ReceiptAncestry.mono extension (retained.1 item member)
              · exact ReceiptAncestry.mono extension retained.2
      | continuation receipt nested endpoint =>
          refine ⟨?_, ReceiptAncestry.mono extension retained.2.1,
            FailureAncestry.mono extension retained.2.2⟩
          exact fun item member => ReceiptAncestry.mono extension (retained.1 item member)
termination_by sizeOf reason

/-- An earlier extension transports the stopped diagnostic without changing the outcome. -/
theorem OutcomeDiagnosticAncestry.mono {original middle : Core}
    {outcome : HookResult (Output width Typing) (Failure width Typing) width}
    (extension : Extends original middle) (retained : OutcomeDiagnosticAncestry middle outcome) :
    OutcomeDiagnosticAncestry original outcome := by
  cases outcome with
  | complete outputs caller queries => trivial
  | stopped outputs reason endpoint => exact FailureAncestry.mono extension retained

/-- Finishing a fold keeps exactly its processed receipts and current stopped diagnostic. -/
theorem OutcomeDiagnosticAncestry.of_finished
    (original : Core) (uv : Nat)
    (result : Fold (Output width Typing) (Failure width Typing) width)
    (retained : match result with
      | .complete _ _ _ _ => True
      | .stopped processed _ current => FailureAncestry original (.alternatives uv processed current)) :
    OutcomeDiagnosticAncestry original (finish uv result) := by
  cases result <;> exact retained

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every actual captured receipt retains its own input histories at all attached caches. -/
theorem ReceiptAncestry.of_captured
    {checkEmpty : Bool} {r n p h k target : Nat} {scs : List Suspended}
    {edge : EdgeValue Symbol Constraint} {caller : Caller width} {before : Cached} {queries : Queries}
    {receipt : Receipt width}
    (observed : SourcePruningEnumerationCapturedEdge.run checkEmpty r n p h k target scs edge
      caller before queries = some receipt) : ReceiptAncestry before.core receipt := by
  have fields := SourcePruningEnumerationCapturedEdge.observed_cache_ancestry_extension observed
  cases receipt with
  | unhandled => trivial
  | rejected caller queries after | complete fragment caller queries after => exact fields.1
  | stopped fragments observation candidate =>
      cases candidate with
      | none => trivial
      | some after => exact fields.1

/-- Every actual opaque or terminal receipt retains its input histories at all attached caches. -/
theorem ReceiptAncestry.of_opaque
    {checkEmpty : Bool} {r n p h k target : Nat} {scs : List Suspended} {value : Node}
    {caller : Caller width} {before : Cached} {queries : Queries} {receipt : Receipt width}
    (observed : SourcePruningEnumerationSelectedOpaqueDispatch.run checkEmpty r n p h k target scs value
      caller before queries = some receipt) : ReceiptAncestry before.core receipt := by
  have fields := SourcePruningEnumerationSelectedOpaqueDispatch.observed_cache_ancestry_extension observed
  cases receipt with
  | unhandled => trivial
  | rejected caller queries after | complete fragment caller queries after => exact fields.1
  | stopped fragments observation candidate =>
      cases candidate with
      | none => trivial
      | some after => exact fields.1

/-- The actual valid prefix retains its candidate history and executes no ordinary scan. -/
theorem PrefixAncestry.of_prefix
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (fuel uv : Nat) (caller : Caller width) (before : Cached) (memos : Memos)
    (total : UnionFind.Total before.core.representatives)
    (valid : SourcePruningEnumerationSelectedStep.PrefixValid holeKey fits admits graph templates checkEmpty edgesOf
      stop order metadata formulas solver inventory fuel uv caller before memos
      (SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
        fuel fuel fuel fuel fuel fuel uv caller before memos.query)) :
    PrefixAncestry before.core
      (SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
        fuel fuel fuel fuel fuel fuel uv caller before memos.query) := by
  have ancestry := SourcePruningEnumerationSelectedStep.prefix_recursion_ancestry holeKey fits admits graph templates
    checkEmpty edgesOf stop order metadata formulas solver inventory fuel uv caller before memos total valid
  have ordinaryNone := SourcePruningEnumerationSelectedStep.prefix_no_ordinary holeKey fits admits graph templates
    stop order metadata fuel fuel fuel fuel fuel fuel uv caller before memos.query
  generalize actual : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
    fuel fuel fuel fuel fuel fuel uv caller before memos.query = observed at ancestry ordinaryNone ⊢
  cases observed with
  | stopped read checked => trivial
  | parked checked candidate raw =>
      cases candidate with
      | none => trivial
      | some after =>
          intro slot key member
          rw [ancestry]
          exact member
  | narrowed checked prepared reached queries action candidate right ordinary =>
      have same : ordinary = none := ordinaryNone
      subst ordinary
      constructor
      · cases candidate with
        | none => trivial
        | some after =>
            intro slot key member
            rw [ancestry]
            exact member
      · trivial

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
