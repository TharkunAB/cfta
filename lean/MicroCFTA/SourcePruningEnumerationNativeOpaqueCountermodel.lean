import MicroCFTA.InternedOpaqueUnionWitness
import MicroCFTA.SourcePruningEnumerationOpaqueBucketAssignment
import MicroCFTA.SourcePruningEnumerationOpaqueBucketCurrent
import MicroCFTA.SourcePruningEnumerationSharedOpaqueBucketBoundary

/-!
# Native construction and the actual shared opaque bucket boundary

The heap comes from the actual fresh constructor. The caller starts with
empty native and query memos. The actual shared child returns one empty
fresh bucket at every fuel. Its assignment satisfies the actual native
Top-guard language and fails the supplied valid descendant obligation.
This result does not assert a full caller Context or synthesis reachability.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeOpaqueCountermodel
open Language EnumerationState EnumerationCorrectness
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Witness" => InternedOpaqueUnionWitness.value
local notation "Bucket" => SourcePruningEnumerationOpaqueBucketAssignment.bucket
variable [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)]
variable [DecidableEq Node] [DecidableEq FullSyntax.Formula]

/-- Use the actual equality-free source Top constraint. -/
abbrev guard : Constraint := SourceEqualityConstraintConstructors.top

/-- Initialize the actual caller with the constructed heap and empty native tables. -/
def caller (width : Nat) (symbol : Symbol) : Caller width :=
  SourceCurrentAllocatedPartialState.initial
    ⟨SourceRecursiveIntersectionThunks.initial width
      ⟨InternedOpaqueUnionWitness.heap symbol guard, Cache.emptyState⟩,
      SourceEqualityConstraintMemoAllocation.empty⟩
    SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty

/-- Two independent unrestricted roots have empty waiting and expansion indexes. -/
def before : Cached := SourcePruningEnumerationOpaqueBucketCurrent.cache Constraint

omit [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)]
  [DecidableEq Node] in
/-- The current independent PCS interpretation accepts every Top-guard term. -/
theorem guard_holds
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (term : Term Symbol) :
    SourceEqualityPCSGuard.holds formulas solver guard term = true := by
  rw [SourceEqualityPCSGuard.public_eq formulas solver guard
    (SourceEqualityGuardReadback.active SourceEqualityConstraintConstructors.top_cached) term]
  exact SourceEqualityConstraintConstructors.top_true formulas solver term

/-- One actual native shared row admits a model excluded by its supplied descendant bucket. -/
theorem native_shared_countermodel
    (width : Nat) (symbol : Symbol)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (checkEmpty : Bool) (r n p h k : Nat) :
    ∃ after : Cached,
      InternedRecordCoherence.Coherent (caller width symbol).checked.native.machine.heap ∧
      InternedProbeProvenance.Available (caller width symbol).checked.native.machine.heap
        (Witness symbol guard) ∧
      (Witness symbol guard).free = [] ∧
      SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run
        checkEmpty r n p h k Bucket (Witness symbol guard) (caller width symbol) before
        SourceEndpointMemo.empty =
        ((.ok (some [.ok (.hole 2, after.core)]), caller width symbol, SourceEndpointMemo.empty,
          before.core, before.waiting), some after) ∧
      after.core = allocated (some 6) before.core ∧
      after.core.values[2]? = some (.unenumerated (some 6) []) ∧
      after.core.counter = 3 ∧
      after.expandable 2 = false ∧
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles
          (SourceEqualityPCSGuard.holds formulas solver) (fun _ _ => False)
          (caller width symbol).checked.native.machine.heap)
        (fun _ _ => True)
        (SourcePruningEnumerationOpaqueBucketAssignment.assignment
          (.node symbol []) (.node symbol []) symbol) after.core ∧
      ¬(∀ sc ∈ Bucket, Suspended.Holds
        (SourcePruningEnumerationOpaqueBucketAssignment.assignment
          (.node symbol []) (.node symbol []) symbol) (.node symbol []) sc) := by
  have accepted := InternedOpaqueUnionWitness.nullary_accepted symbol guard
    (SourceEqualityPCSGuard.holds formulas solver) (fun _ _ => False)
    (guard_holds formulas solver (.node symbol []))
  obtain ⟨handle, action, afterCore, encoded, decoded, _prepared, _raw, _success,
    shape, stored, counter, _length, _initial, satisfied, rejected, _retained⟩ :=
    SourcePruningEnumerationOpaqueBucketAssignment.countermodel
      (InternedOpaqueUnionWitness.heap symbol guard) (Witness symbol guard)
      (InternedOpaqueUnionWitness.coherent symbol guard)
      (InternedOpaqueUnionWitness.available symbol guard)
      (InternedOpaqueUnionWitness.closed symbol guard) True.intro
      (SourceEqualityPCSGuard.holds formulas solver) (fun _ _ => False) symbol accepted
      (fun (_ : Constraint) (_ : Term Symbol) => True) (.node symbol []) (.node symbol [])
  have literal : SourcePruningEnumerationNodes.encodeNode (Witness symbol guard) = some 6 := rfl
  have same : handle = 6 := Option.some.inj (encoded.symm.trans literal)
  subst handle
  subst afterCore
  refine ⟨SourcePruningEnumerationSharedOpaqueBucketBoundary.after 6 before,
    InternedOpaqueUnionWitness.coherent symbol guard,
    InternedOpaqueUnionWitness.available symbol guard,
    InternedOpaqueUnionWitness.closed symbol guard, ?_, rfl, stored, counter, rfl,
    satisfied, ?_⟩
  · exact SourcePruningEnumerationSharedOpaqueBucketBoundary.run_exact
      checkEmpty r n p h k Bucket (Witness symbol guard) 6 (caller width symbol) before
      SourceEndpointMemo.empty literal decoded rfl
      SourcePruningEnumerationOpaqueBucketAssignment.bucket_valid.2.1
  · exact SourcePruningEnumerationOpaqueBucketAssignment.bucket_rejects _ symbol

end MicroCFTA.SourcePruningEnumerationNativeOpaqueCountermodel
