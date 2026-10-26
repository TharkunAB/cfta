import MicroCFTA.SourcePruningEnumerationPrefixCompletion

namespace MicroCFTA.SourcePruningEnumerationPrefixPacket
open EnumerationState EnumerationSchedule InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourcePruningEnumerationSelectedStep
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem finish_preserves
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (r n p h k uv : Nat) (observed : Result width Typing) :
    match observed with
    | .stopped _ _ | .parked _ _ _ => finish checkEmpty edgesOf r n p h k uv observed = observed
    | .narrowed checked prepared reached queries action candidate right _ =>
        ∃ ordinary, finish checkEmpty edgesOf r n p h k uv observed =
          .narrowed checked prepared reached queries action candidate right ordinary := by
  cases observed with
  | stopped _ _ => rfl
  | parked _ _ _ => rfl
  | narrowed checked prepared reached queries action candidate right ordinary =>
      dsimp only
      unfold finish
      split <;> simp_all only [Result.narrowed.injEq] <;> subst_vars <;> exact ⟨_, rfl⟩

variable (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
variable (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
variable (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
variable (stop : Option (Metadata Typing → Nat → Bool))
variable (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
variable (formulas : SourceGuards.Formulas FullSyntax.Formula)
variable (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
variable (fuel uv : Nat) (caller : Caller width) (before : Cached) (memos : Memos)

/-- Every narrowed prefix retains its actual native Post, including Empty rejection. -/
theorem prefix_context (observed : Result width Typing)
    (valid : PrefixValid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
      formulas solver inventory fuel uv caller before memos observed) :
    match observed with
    | .stopped _ _ => False
    | .parked _ _ _ => True
    | .narrowed _ _ reached queries _ _ _ _ =>
        ∃ final, Post formulas solver inventory caller reached final ∧ final.query = queries := by
  have full := valid.2.1
  cases observed with
  | stopped read checked =>
      obtain ⟨_oldHandle, _scs, _readAfter, _reading, impossible⟩ := full
      exact impossible
  | parked _ _ _ => trivial
  | narrowed checked prepared reached queries action candidate right ordinary =>
      obtain ⟨next, finished⟩ := finish_preserves checkEmpty edgesOf 0 0 0 0 0 uv
        (.narrowed checked prepared reached queries action candidate right ordinary)
      rw [finished] at full
      obtain ⟨_oldHandle, _scs, _readAfter, _reading, _checking, _oldValue, _value, _heap,
        _selectedAction, final, _decoded, _narrowed, _prepared, _samePrepared, _reached,
        _queries, post, saved, _shape⟩ := full
      exact ⟨final, post, saved⟩

/-- Every retained parked or nonempty cache has its actual native laws and original counter and order. -/
theorem prefix_cache_valid (observed : Result width Typing)
    (valid : PrefixValid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
      formulas solver inventory fuel uv caller before memos observed) :
    match observed with
    | .parked _ (some after) _ =>
        SourcePruningEnumerationNativeBranchCompletion.CacheValid caller after ∧ Safe after.core ∧
        EnumerationReferences.PendingReferences after.core ∧ after.core.counter = before.core.counter ∧
        ∀ level frontier, EnumerationOrder.Stratified before.core level frontier →
          EnumerationOrder.Stratified after.core level frontier
    | .narrowed _ _ reached _ _ (some after) _ _ =>
        SourcePruningEnumerationNativeBranchCompletion.CacheValid reached after ∧ Safe after.core ∧
        EnumerationReferences.PendingReferences after.core ∧ after.core.counter = before.core.counter ∧
        ∀ level frontier, EnumerationOrder.Stratified before.core level frontier →
          EnumerationOrder.Stratified after.core level frontier
    | _ => True := by
  have full := valid.2.1
  cases observed with
  | stopped _ _ => trivial
  | parked checked candidate raw =>
      cases candidate with
      | none => trivial
      | some after =>
          obtain ⟨_oldHandle, _scs, _readAfter, _reading, _checking, cached, same, _core,
            cacheValid, safe, pending, _counter, _ordered, _raw⟩ := full
          have equal : after = cached := Option.some.inj same
          subst cached
          exact ⟨cacheValid, safe, pending, valid.2.2⟩
  | narrowed checked prepared reached queries action candidate right ordinary =>
      cases candidate with
      | none => trivial
      | some after =>
          obtain ⟨next, finished⟩ := finish_preserves checkEmpty edgesOf 0 0 0 0 0 uv
            (.narrowed checked prepared reached queries action (some after) right ordinary)
          rw [finished] at full
          obtain ⟨_oldHandle, _scs, _readAfter, _reading, _checking, _oldValue, _value, _heap,
            _selectedAction, _final, _decoded, _narrowed, _prepared, _samePrepared, _reached,
            _queries, _post, _saved, shape⟩ := full
          rcases shape with ⟨_empty, _action, noCache, _right, _ordinary⟩ |
            ⟨_newHandle, cached, _nonempty, _encoded, _action, same, cacheValid, safe, pending, _rest⟩
          · cases noCache
          · have equal : after = cached := Option.some.inj same
            subst cached
            exact ⟨cacheValid, safe, pending, valid.2.2⟩

end MicroCFTA.SourcePruningEnumerationPrefixPacket
