import MicroCFTA.SourcePruningEnumerationNativeOrdinaryContinuations
import MicroCFTA.SourcePruningEnumerationEdgeChildLanguage

/-!
# Actual ordinary scan gates and inherited trie validity

An actual ordinary scan passes the runtime terminal test.
Representative entry retains the stored bucket without checking its tries.
Valid inherited and projected tries give valid descendant buckets.
-/
namespace MicroCFTA.SourcePruningEnumerationOrdinarySemanticGates
open EnumerationState EnumerationCorrectness EnumerationSemantics
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
universe u v
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- An actual ordinary scan supplies its inherited nonterminal gate. -/
theorem ordinary_nonterminal
    (checkEmpty : Bool) (r n p h k uv target handle : Nat) (scs : List Suspended)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Constraint))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries) (entered : Core)
    (result : SourcePruningEnumerationNativeBranches.Result width)
    (observed : SourcePruningEnumerationNativeOrdinary.run checkEmpty r n p h k uv
      edgesOf caller before queries =
      ([.ok ((target, handle, scs, .node entry edges depth free), entered)], some result)) :
    scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false := by
  have actualEntry := congrArg Prod.fst observed
  change ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap r uv before.core) =
    [.ok ((target, handle, scs, .node entry edges depth free), entered)] at actualEntry
  cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) with
  | false => rfl
  | true =>
      have actualScan := congrArg Prod.snd observed
      simp only [SourcePruningEnumerationNativeOrdinary.run, actualEntry, terminal,
        ↓reduceIte, reduceCtorEq] at actualScan

/-- A hook-aware ordinary scan passes the same runtime terminal test. -/
theorem ordinary_continuations_nonterminal
    {Output : Type u} {Reason : Type v}
    (hook : Fragment → Caller width → Queries → Cached →
      SourcePruningEnumerationNativeContinuations.HookResult Output Reason width)
    (checkEmpty : Bool) (r n p h k uv target handle : Nat) (scs : List Suspended)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Constraint))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries) (entered : Core)
    (result : SourcePruningEnumerationNativeContinuations.Result Output Reason width)
    (observed : SourcePruningEnumerationNativeOrdinaryContinuations.run hook checkEmpty r n p h k uv
      edgesOf caller before queries =
      ([.ok ((target, handle, scs, .node entry edges depth free), entered)], some result)) :
    scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false := by
  have actualEntry := congrArg Prod.fst observed
  change ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap r uv before.core) =
    [.ok ((target, handle, scs, .node entry edges depth free), entered)] at actualEntry
  cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) with
  | false => rfl
  | true =>
      have actualScan := congrArg Prod.snd observed
      simp only [SourcePruningEnumerationNativeOrdinaryContinuations.run, actualEntry, terminal,
        ↓reduceIte, reduceCtorEq] at actualScan

/-- Entry transports a genuine stored-bucket validity history through its exact value equality. -/
theorem stored_valid_of_values
    (before after : Core) (values : after.values = before.values)
    (valid : ∀ uv node bucket, before.values[uv]? = some (.unenumerated node bucket) →
      ValidSuspended bucket)
    (uv : Nat) (node : Option Nat) (bucket : List Suspended)
    (stored : after.values[uv]? = some (.unenumerated node bucket)) :
    ValidSuspended bucket :=
  valid uv node bucket (by simpa only [values] using stored)

/-- The actual terminal partition retains valid tries and excludes terminals from its descendant bucket. -/
theorem partition_descendants
    (bucket here descendants : List Suspended)
    (partitioned : bucket.partition (fun sc => EqualityTrie.isTerminal sc.trie) = (here, descendants)) :
    descendants.any (fun sc => EqualityTrie.isTerminal sc.trie) = false ∧
      (ValidSuspended bucket → ValidSuspended here ∧ ValidSuspended descendants) := by
  have hereSame : bucket.filter (fun sc => EqualityTrie.isTerminal sc.trie) = here := by
    simpa only [List.partition_eq_filter_filter] using congrArg Prod.fst partitioned
  have descendantsSame : bucket.filter (fun sc => !(EqualityTrie.isTerminal sc.trie)) = descendants := by
    simpa only [List.partition_eq_filter_filter, Function.comp_def] using congrArg Prod.snd partitioned
  constructor
  · apply List.any_eq_false.mpr
    intro sc member terminal
    have retained := (List.mem_filter.mp (show sc ∈ bucket.filter
      (fun sc => !(EqualityTrie.isTerminal sc.trie)) by simpa only [descendantsSame] using member)).2
    simp only [terminal, Bool.not_true, Bool.false_eq_true] at retained
  · intro valid
    constructor
    · intro sc member
      have present : sc ∈ bucket.filter (fun sc => EqualityTrie.isTerminal sc.trie) := by
        simpa only [hereSame] using member
      exact valid sc (List.mem_filter.mp present).1
    · intro sc member
      have present : sc ∈ bucket.filter (fun sc => !(EqualityTrie.isTerminal sc.trie)) := by
        simpa only [descendantsSame] using member
      exact valid sc (List.mem_filter.mp present).1

/-- Genuine inherited validity and valid projected classes give valid actual child buckets. -/
theorem children_valid
    (edge : EdgeValue Symbol Constraint) (scs : List Suspended) (start : Nat)
    (tries : List EqualityTrie.Trie) (inherited : ValidSuspended scs)
    (projected : ∀ trie ∈ tries, EqualityTrie.Valid trie) :
    ∀ incoming bucket,
      (incoming, bucket) ∈ SourcePruningEnumerationEdgeInputs.children edge scs start tries →
      ValidSuspended bucket := by
  have own : ValidSuspended (suspendedVars start tries) := by
    intro sc member
    have present : sc.trie ∈ tries := by
      rw [← suspendedVars_tries start tries]
      exact List.mem_map.mpr ⟨sc, member, rfl⟩
    exact projected sc.trie present
  intro incoming bucket member
  obtain ⟨indexed, _present, same⟩ := List.mem_map.mp member
  cases same
  intro sc retained
  rcases List.mem_append.mp retained with inheritedMember | ownMember
  · exact descend_valid scs indexed.2 inherited sc inheritedMember
  · exact descend_valid (suspendedVars start tries) indexed.2 own sc ownMember

end MicroCFTA.SourcePruningEnumerationOrdinarySemanticGates
