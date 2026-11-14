import MicroCFTA.SourcePruningEnumerationSharedChildFinalRawTargets
import MicroCFTA.EnumerationSemantics

/-!
# Terminal restrictions observed from actual shared child aliases

An assignment that satisfies the actual forest respects its raw target aliases.
Each original terminal trie therefore holds at the filled returned fragment.
The theorem derives this conditional statement from actual shared operations.
It does not construct an assignment or a finite accepted completion.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch
open EnumerationState EnumerationSchedule InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Fragment" => Fragments.Fragment Symbol

set_option autoImplicit false
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Actual shared terminal aliases derive each original empty-path restriction under the UF observer. -/
theorem terminal_singleton_terminal_observer
    (checkEmpty : Bool) (r n p h k : Nat) (bucket : List Suspended)
    (incoming : Node) (caller : Caller width) (before : Cached) (queries : Queries)
    (terminal : bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true)
    (fragment : Fragment) (afterCaller : Caller width) (savedQueries : Queries)
    (read after : Core) (moved : EnumerationWaitingIndex.Waiting) (afterCache : Option Cached)
    (roots : Nat → Nat) (paths : Roots before.core.representatives roots)
    (actual : run checkEmpty r n p h k bucket incoming caller before queries =
      ((.ok (some [.ok (fragment, after)]), afterCaller, savedQueries, read, moved), afterCache)) :
    ∃ winner, fragment = .hole winner ∧
      ∀ assignment : Nat → Language.Term Symbol,
        (UnionFind.Satisfies read.representatives assignment →
          ∀ sc ∈ bucket, [] ∈ EqualityTrie.fromPathTrie sc.trie →
            assignment winner = assignment sc.var ∧
            Suspended.Holds assignment (Fragments.fill assignment fragment) sc) ∧
        (UnionFind.Satisfies after.representatives assignment →
          ∀ sc ∈ bucket, [] ∈ EqualityTrie.fromPathTrie sc.trie →
            assignment winner = assignment sc.var ∧
            Suspended.Holds assignment (Fragments.fill assignment fragment) sc) := by
  obtain ⟨_first, _rest, _descendants, _recorded, winner, _joined, _foldCaller,
      _foldQueries, _folded, _foldOuter, _partitioned, _processed, _foldedCall,
      _foldEndpoint, _incomingCall, _recordedSame, _joinedValues, hole,
      _foldForest, _writtenForest, rawTargets⟩ :=
    terminal_singleton_final_raw_target_incidence checkEmpty r n p h k bucket incoming
      caller before queries terminal fragment afterCaller savedQueries read after moved
      afterCache roots paths actual
  have interpret (forest : UnionFind.Forest)
      (aliases : ∀ sc ∈ bucket, [] ∈ EqualityTrie.fromPathTrie sc.trie →
        UnionFind.SameClass forest winner sc.var)
      (assignment : Nat → Language.Term Symbol) (satisfied : UnionFind.Satisfies forest assignment) :
      ∀ sc ∈ bucket, [] ∈ EqualityTrie.fromPathTrie sc.trie →
        assignment winner = assignment sc.var ∧
        Suspended.Holds assignment (Fragments.fill assignment fragment) sc := by
    intro sc present atRoot
    have equal : assignment winner = assignment sc.var :=
      satisfied winner sc.var (aliases sc present atRoot)
    have terminalTrie : EqualityTrie.isTerminal sc.trie = true := by
      simp only [(EqualityTrie.nil_mem sc.trie).mp atRoot, EqualityTrie.isTerminal]
    refine ⟨equal, (EnumerationSemantics.terminal_holds assignment
      (Fragments.fill assignment fragment) sc terminalTrie).mpr ?_⟩
    simpa only [hole, Fragments.fill] using equal
  refine ⟨winner, hole, ?_⟩
  intro assignment
  exact ⟨interpret read.representatives
      (fun sc present atRoot => (rawTargets sc present atRoot).2.2.1) assignment,
    interpret after.representatives
      (fun sc present atRoot => (rawTargets sc present atRoot).2.2.2) assignment⟩

end MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch

#check @MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.terminal_singleton_terminal_observer
#print axioms MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.terminal_singleton_terminal_observer
