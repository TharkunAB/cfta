import MicroCFTA.SourcePruningEnumerationSharedPreparedCounterPrimitives
import MicroCFTA.SourcePruningEnumerationSharedPreparedPartialOutput

/-!
# Allocation counters at literal prepared shared outputs

The proof follows actual callbacks and ordered native alternatives.
Every emitted output retains the original allocation domain at any fuel.
Source startup therefore supplies slot zero for partial observation.
This law does not establish adequate fuel, depth or language completeness.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive
open EnumerationState EnumerationSchedule EnumerationCorrectness InternedConstructorTemplates
open SourceSynthesisOriginalFiniteDriver (startup)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result
local notation "Fold" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.Result
local notation "advance" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance
variable {Typing Key : Type} {width : Nat}
local notation "Result" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.HookResult
  (Output width Typing) (Failure width Typing) width

private def foldEmitted : Fold (Output width Typing) (Failure width Typing) width → List (Output width Typing)
  | .complete _ outputs _ _ | .stopped _ outputs _ => outputs

private theorem finish_emitted (uv : Nat) (folded : Fold (Output width Typing) (Failure width Typing) width) :
    emitted (finish uv folded) = foldEmitted folded := by
  cases folded <;> rfl

private theorem continueWith_counter
    (recur : Metadata Typing → Caller width → Queries → Cached → Option Next → Result)
    (recursiveCounters : ∀ metadata caller queries before decision output,
      output ∈ emitted (recur metadata caller queries before decision) →
        before.core.counter ≤ output.cache.core.counter)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (fuel : Nat) (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller width) (queries : Queries) (before : Cached) :
    ∀ output ∈ emitted (continueWith recur graph templates stop order fuel metadata uv fragment caller queries before),
      before.core.counter ≤ output.cache.core.counter := by
  unfold continueWith
  dsimp only
  split
  · intro output member; cases member
  · rename_i updated core recorded
    intro output member
    have same := SourcePruningEnumerationSharedPreparedCounterPrimitives.recordTypes_counter graph templates fuel
      metadata uv (.inl fragment) before.core core (false, updated)
      (by simp only [Success, recorded, List.mem_singleton])
    have lower := recursiveCounters updated caller queries (EnumerationExpandableIndex.frame core before)
      (SourcePruningEnumerationRestart.decision stop order updated (EnumerationExpandableIndex.frame core before)) output member
    change core.counter ≤ output.cache.core.counter at lower
    rw [same] at lower
    exact lower
  · intro output member; cases member

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem captured_counter
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended) (edge : EdgeValue Symbol Constraint)
    (caller reached : Caller width) (queries saved : Queries) (before after : Cached) (fragment : Fragment)
    (actual : SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge.run checkEmpty r n p h k target
      scs edge caller before queries = some (.complete fragment reached saved after)) :
    before.core.counter ≤ after.core.counter := by
  cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
  | some data =>
    obtain ⟨tries, residual⟩ := data
    have lower := SourcePruningEnumerationSharedSelectedCounterGrowth.captured checkEmpty r n p h k target
      scs edge caller before queries tries residual projected
    rw [actual] at lower
    exact lower
  | none =>
    cases allowed : arityAllows edge.children.length scs with
    | false =>
      have rejected := SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.arity_rejected
        checkEmpty r n p h k scs edge caller before queries allowed
      rw [SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge.run, rejected] at actual
      cases actual
    | true =>
      have unsupported := SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.unsupported
        checkEmpty r n p h k scs edge caller before queries allowed projected
      rw [SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge.run, unsupported] at actual
      cases actual

private theorem opaque_counter
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended) (value : Node)
    (caller reached : Caller width) (queries saved : Queries) (before after : Cached) (fragment : Fragment)
    (actual : SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty r n p h k target
      scs value caller before queries = some (.complete fragment reached saved after)) :
    before.core.counter ≤ after.core.counter := by
  have finalized :
      ((match SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run
          checkEmpty r n p h k scs value caller before queries with
      | ((.ok (some [.ok (actualFragment, _returned)]), actualCaller, actualQueries, _outer, _waiting), some middle) =>
          match SourcePruningEnumerationFinalize.run actualCaller.checked.native.machine.heap k target actualFragment middle with
          | some finished => some (.complete actualFragment actualCaller actualQueries finished)
          | none => some (.finalizeStopped actualFragment actualCaller actualQueries middle)
      | (observation, candidate) => some (.stopped [] observation candidate)) : Option (Receipt width)) =
        some (.complete fragment reached saved after) → before.core.counter ≤ after.core.counter := by
    intro observed
    split at observed
    · rename_i actualFragment returned actualCaller actualQueries outer waiting middle child
      split at observed
      · rename_i finished finishing
        have lower := SourcePruningEnumerationSharedSelectedCounterGrowth.child
          checkEmpty r n p h k scs value caller before queries middle (by rw [child])
        have same := SourcePruningEnumerationFinalize.run_scalars actualCaller.checked.native.machine.heap
          k target actualFragment middle finished finishing
        cases observed
        rw [same.1]
        exact lower
      · cases observed
    · cases observed
  cases value with
  | empty =>
    rw [SourcePruningEnumerationSharedSelectedOpaqueDispatch.empty] at actual
    cases actual
  | node entry rows depth free =>
    unfold SourcePruningEnumerationSharedSelectedOpaqueDispatch.run at actual
    simp only [reduceCtorEq, ↓reduceIte] at actual
    split at actual
    · cases actual
    · exact finalized actual
  | reference _ | mu _ _ _ _ | union _ _ _ _ =>
    unfold SourcePruningEnumerationSharedSelectedOpaqueDispatch.run at actual
    simp only [reduceCtorEq, ↓reduceIte] at actual
    exact finalized actual

private theorem scan_counter
    (hook : Fragment → Caller width → Queries → Cached → Result)
    (lower : ∀ fragment caller queries before output, output ∈ emitted (hook fragment caller queries before) →
      before.core.counter ≤ output.cache.core.counter)
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended) (before : Cached)
    (edges : List (EdgeValue Symbol Constraint)) (caller : Caller width) (queries : Queries) :
    ∀ output ∈ foldEmitted (SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.run
      hook checkEmpty r n p h k target scs before edges caller queries),
      before.core.counter ≤ output.cache.core.counter := by
  induction edges generalizing caller queries with
  | nil => intro output member; cases member
  | cons edge rest ih =>
    cases observed : SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge.run
        checkEmpty r n p h k target scs edge caller before queries with
    | none =>
      intro output member
      simp only [SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.run,
        observed, foldEmitted, List.not_mem_nil] at member
    | some receipt =>
      cases receipt with
      | unhandled | finalizeStopped _ _ _ _ =>
        intro output member
        simp only [SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.run,
          observed, SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance, foldEmitted, List.not_mem_nil] at member
      | rejected reached saved after =>
        have suffix := ih reached saved
        cases following : SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.run
            hook checkEmpty r n p h k target scs before rest reached saved <;> intro output member
        all_goals
          simp only [SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.run,
            observed, SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance, following, foldEmitted] at member
          rw [following] at suffix
          exact suffix output member
      | complete fragment reached saved after =>
        have grew := captured_counter checkEmpty r n p h k target scs edge caller reached queries saved
          before after fragment observed
        cases callback : hook fragment reached saved after with
        | stopped outputs reason endpoint =>
          intro output member
          have head : output ∈ emitted (hook fragment reached saved after) := by
            simpa only [SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.run,
              observed, callback, foldEmitted, emitted] using member
          exact Nat.le_trans grew (lower fragment reached saved after output head)
        | complete outputs middleCaller middleQueries =>
          have suffix := ih middleCaller middleQueries
          cases following : SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.run
              hook checkEmpty r n p h k target scs before rest middleCaller middleQueries <;> intro output member
          all_goals
            simp only [SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.run,
              observed, callback, following, foldEmitted] at member
            rcases List.mem_append.mp member with first | later
            · exact Nat.le_trans grew (lower fragment reached saved after output (by
                simpa only [callback, emitted] using first))
            · rw [following] at suffix
              exact suffix output later
      | stopped fragments observation candidate =>
        cases advanced : advance (.stopped fragments observation candidate) with
        | none =>
          intro output member
          simp only [SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.run,
            observed, advanced, foldEmitted, List.not_mem_nil] at member
        | some endpoint =>
          obtain ⟨middleCaller, middleQueries⟩ := endpoint
          have suffix := ih middleCaller middleQueries
          cases following : SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.run
              hook checkEmpty r n p h k target scs before rest middleCaller middleQueries <;> intro output member
          all_goals
            simp only [SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.run,
              observed, advanced, following, foldEmitted] at member
            rw [following] at suffix
            exact suffix output member

private theorem opaque_outputs_counter
    (hook : Fragment → Caller width → Queries → Cached → Result)
    (lower : ∀ fragment caller queries before output, output ∈ emitted (hook fragment caller queries before) →
      before.core.counter ≤ output.cache.core.counter)
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended) (value : Node)
    (caller : Caller width) (queries : Queries) (before : Cached) :
    ∀ output ∈ foldEmitted (SourcePruningEnumerationSharedReceiptContinuation.run hook caller queries
      (SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty r n p h k target scs value caller before queries)),
      before.core.counter ≤ output.cache.core.counter := by
  cases observed : SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty r n p h k target
      scs value caller before queries with
  | none => intro output member; cases member
  | some receipt =>
    cases receipt with
    | unhandled | rejected _ _ _ | finalizeStopped _ _ _ _ => intro output member; cases member
    | complete fragment reached saved after =>
      have grew := opaque_counter checkEmpty r n p h k target scs value caller reached queries saved before after fragment observed
      cases callback : hook fragment reached saved after <;> intro output member
      all_goals
        have head : output ∈ emitted (hook fragment reached saved after) := by
          simpa only [SourcePruningEnumerationSharedReceiptContinuation.run, callback, foldEmitted, emitted] using member
        exact Nat.le_trans grew (lower fragment reached saved after output head)
    | stopped fragments observation candidate =>
      cases advanced : advance (.stopped fragments observation candidate) with
      | none =>
        intro output member
        simp only [SourcePruningEnumerationSharedReceiptContinuation.run, advanced,
          foldEmitted, List.not_mem_nil] at member
      | some endpoint =>
        obtain ⟨reached, saved⟩ := endpoint
        intro output member
        simp only [SourcePruningEnumerationSharedReceiptContinuation.run, advanced,
          foldEmitted, List.not_mem_nil] at member

private theorem prepared_counter
    (hook : Fragment → Caller width → Queries → Cached → Result)
    (lower : ∀ fragment caller queries before output, output ∈ emitted (hook fragment caller queries before) →
      before.core.counter ≤ output.cache.core.counter)
    (checkEmpty : Bool) (entryFuel nativeFuel r n p h k uv : Nat)
    (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (caller : Caller width) (queries : Queries) (before : Cached)
    (folded : Fold (Output width Typing) (Failure width Typing) width)
    (actual : (SourcePruningEnumerationSharedPreparedContinuations.run hook checkEmpty entryFuel nativeFuel
      r n p h k uv edgesOf caller before queries).2 = some folded) :
    ∀ output ∈ foldEmitted folded, before.core.counter ≤ output.cache.core.counter := by
  cases preparation : SourcePruningEnumerationSelectedPreparation.run entryFuel nativeFuel uv caller before with
  | mk raw native =>
    simp only [SourcePruningEnumerationSharedPreparedContinuations.run, preparation] at actual
    cases native with
    | none => cases actual
    | some result =>
      cases result with
      | failed fault heap => cases actual
      | done value heap =>
        dsimp only at actual
        have singleton : ∃ target handle scs decoded entered,
            raw = [.ok ((target, handle, scs, decoded), entered)] := by
          cases raw with
          | nil => cases actual
          | cons first rest =>
            cases rest with
            | cons next tail =>
              cases first with
              | error fault => cases actual
              | ok result =>
                rcases result with ⟨⟨target, handle, scs, decoded⟩, entered⟩
                cases actual
            | nil =>
              cases first with
              | error fault => cases actual
              | ok result =>
                rcases result with ⟨⟨target, handle, scs, decoded⟩, entered⟩
                exact ⟨target, handle, scs, decoded, entered, rfl⟩
        rcases singleton with ⟨target, handle, scs, decoded, entered, reading⟩
        rw [reading] at actual
        dsimp only at actual
        have entryRaw := congrArg Prod.fst preparation
        change ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap entryFuel uv before.core) = raw at entryRaw
        rw [reading] at entryRaw
        have same := SourcePruningEnumerationSharedPreparedCounterPrimitives.entry_counter
          caller.checked.native.machine.heap entryFuel uv before.core entered (target, handle, scs, decoded)
          (by simp only [Success, entryRaw, List.mem_singleton])
        split at actual
        · have equal := Option.some.inj actual
          subst folded
          intro output member
          have bound := opaque_outputs_counter hook lower checkEmpty r n p h k target scs value
            (SourcePruningEnumerationSelectedValueCaller.advance caller heap) queries
            (EnumerationExpandableIndex.frame entered before) output member
          change entered.counter ≤ output.cache.core.counter at bound
          rw [same] at bound
          exact bound
        · cases value with
          | node entry rows depth free =>
            have equal := Option.some.inj actual
            subst folded
            intro output member
            have bound := scan_counter hook lower checkEmpty r n p h k target scs
              (EnumerationExpandableIndex.frame entered before) (edgesOf (.node entry rows depth free))
              (SourcePruningEnumerationSelectedValueCaller.advance caller heap) queries output member
            change entered.counter ≤ output.cache.core.counter at bound
            rw [same] at bound
            exact bound
          | empty | reference _ | mu _ _ _ _ | union _ _ _ _ =>
            have equal := Option.some.inj actual
            subst folded
            intro output member
            have bound := opaque_outputs_counter hook lower checkEmpty r n p h k target scs _
              (SourcePruningEnumerationSelectedValueCaller.advance caller heap) queries
              (EnumerationExpandableIndex.frame entered before) output member
            change entered.counter ≤ output.cache.core.counter at bound
            rw [same] at bound
            exact bound

/-- Every literal prepared shared output retains the input counter at every fuel and depth. -/
theorem resume_output_counter
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel depth : Nat) (metadata : Metadata Typing) (caller : Caller width) (queries : Queries)
    (before : Cached) (decision : Option Next) :
    ∀ output ∈ emitted (resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth
      metadata caller queries before decision), before.core.counter ≤ output.cache.core.counter := by
  induction depth generalizing metadata caller queries before decision with
  | zero =>
    intro output member
    have same := resume_zero_output holeKey fits admits graph templates checkEmpty edgesOf stop order
      workFuel metadata caller queries before decision output member
    rw [same.1]
    exact Nat.le_refl _
  | succ depth ih =>
    cases decision with
    | none =>
      intro output member
      obtain rfl := List.mem_singleton.mp member
      exact Nat.le_refl _
    | some next =>
      cases next with
      | done =>
        intro output member
        obtain rfl := List.mem_singleton.mp member
        exact Nat.le_refl _
      | stuck => intro output member; cases member
      | expand uv =>
        intro output member
        dsimp only [resume] at member
        split at member
        · cases member
        · rename_i checked parked updated next core observed
          have facts := SourcePruningEnumerationSharedPreparedCounterPrimitives.prefix_counter
            holeKey fits admits graph templates stop order metadata workFuel workFuel workFuel workFuel workFuel workFuel
            uv caller before queries
          rw [observed] at facts
          have same := facts updated next core rfl
          have lower := ih updated caller queries (EnumerationExpandableIndex.frame core parked) next output member
          change core.counter ≤ output.cache.core.counter at lower
          rw [same] at lower
          exact lower
        · cases member
        · cases member
        · rename_i observed
          have facts := SourcePruningEnumerationSharedPreparedCounterPrimitives.prefix_counter
            holeKey fits admits graph templates stop order metadata workFuel workFuel workFuel workFuel workFuel workFuel
            uv caller before queries
          rw [observed] at facts
          have same := facts _ rfl
          split at member
          · cases member
          · rename_i folded prepared
            rw [finish_emitted] at member
            have lower := prepared_counter
              (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth)
                graph templates stop order workFuel _ uv)
              (fun fragment actual current cache output present => continueWith_counter
                (resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth) ih
                graph templates stop order workFuel _ uv fragment actual current cache output present)
              checkEmpty workFuel workFuel workFuel workFuel workFuel workFuel workFuel uv edgesOf
              _ _ _ folded prepared output member
            rw [same] at lower
            exact lower
        · cases member
        · cases member

/-- The actual callback retains its input counter before and after smaller-depth recursion. -/
theorem continueWith_output_counter
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel depth : Nat) (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller width) (queries : Queries) (before : Cached) :
    ∀ output ∈ emitted (continueWith
      (resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth)
      graph templates stop order workFuel metadata uv fragment caller queries before),
      before.core.counter ≤ output.cache.core.counter :=
  continueWith_counter
    (resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth)
    (resume_output_counter holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth)
    graph templates stop order workFuel metadata uv fragment caller queries before

/-- Ordered native alternatives retain the captured input counter in every emitted output. -/
theorem scan_output_counter
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel depth : Nat) (metadata : Metadata Typing) (uv : Nat) (scs : List Suspended)
    (before : Cached) (edges : List (EdgeValue Symbol Constraint)) (caller : Caller width) (queries : Queries) :
    ∀ output ∈ emitted (finish uv
      (SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.run
        (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth)
          graph templates stop order workFuel metadata uv)
        checkEmpty workFuel workFuel workFuel workFuel workFuel uv scs before edges caller queries)),
      before.core.counter ≤ output.cache.core.counter := by
  intro output member
  rw [finish_emitted] at member
  exact scan_counter
    (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth)
      graph templates stop order workFuel metadata uv)
    (fun fragment actual current cache result present => continueWith_output_counter
      holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth metadata uv
      fragment actual current cache result present)
    checkEmpty workFuel workFuel workFuel workFuel workFuel uv scs before edges caller queries output member

/-- The literal prepared driver retains its original counter in every emitted output. -/
theorem run_output_counter
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel depth : Nat) (metadata : Metadata Typing) (caller : Caller width) (queries : Queries) (before : Cached) :
    ∀ output ∈ emitted (run holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth
      metadata caller queries before), before.core.counter ≤ output.cache.core.counter :=
  resume_output_counter holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth
    metadata caller queries before (SourcePruningEnumerationRestart.decision stop order metadata before)

/-- Actual source startup supplies root allocation at every emitted positive-depth output. -/
theorem run_startup_root
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel depth : Nat) (metadata : Metadata Typing) (caller : Caller width) (queries : Queries)
    (value : Node) (handle : Nat) :
    ∀ output ∈ emitted (run holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth
      metadata caller queries (startup value handle)), 0 < output.cache.core.counter := by
  intro output member
  exact Nat.lt_of_lt_of_le (startup_root value handle).2.1 (run_output_counter
    holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth metadata caller queries
    (startup value handle) output member)

open Language Fragments
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed)
open SourcePruningEnumerationRecursive (Packet)
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Heap" => SourceEqualityAnnotationHeap.Heap

/-- An actual startup output supplies its own root allocation to the full partial-observation packet. -/
theorem startup_output_partial_complete
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel depth : Nat) (metadata : Metadata Typing) (caller : Caller width) (queries : Queries)
    (value : Node) (handle : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller width) (seed : Seed) (output : Output width Typing)
    (member : output ∈ emitted (run holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth
      metadata caller queries (startup value handle)))
    (resources : OutputResources formulas solver original seed output) :
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
  exact resources.root_partial_complete
    (run_startup_root holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth metadata
      caller queries value handle output member)

end MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive
