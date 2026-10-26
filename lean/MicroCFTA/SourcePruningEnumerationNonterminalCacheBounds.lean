import MicroCFTA.SourcePruningEnumerationChildDispatch
import MicroCFTA.SourcePruningEnumerationSuspendedMass

/-!
# Counter and suspended mass of actual cached nonterminal children

Ordinary nodes store the complete incoming bucket. Mu and Union allocate
with an empty bucket. Every successful singleton allocates one slot.
Empty rejects before allocation and retains the input cache.
-/
namespace MicroCFTA.SourcePruningEnumerationCachedPrepare
open EnumerationState
open SourcePruningEnumerationNodes
open SourcePruningEnumerationPrefixAdmission (suspendedBound)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint

/-- Allocation appends one empty bucket and retains the entire original suspended mass. -/
theorem allocated_mass (node : Option Nat) (before : Core) :
    suspendedBound (allocated node before) = suspendedBound before := by
  simp only [suspendedBound, allocated, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, List.length_nil, Nat.add_zero]

/-- An actual singleton cache has its exact shape-dependent mass and one fresh slot. -/
theorem singleton_counter_mass
    (heap : InternedConstructorTemplates.State Symbol Constraint) (fuel : Nat)
    (scs : List Suspended) (value : Node) (before after : Cached)
    (fragment : Fragments.Fragment Symbol)
    (aligned : before.core.counter = before.core.values.length)
    (cached : prepareChild heap fuel scs value before = some [(fragment, after)]) :
    after.core.counter = before.core.counter + 1 ∧
      suspendedBound after.core = suspendedBound before.core +
        (match value with | .node .. => scs.length | _ => 0) := by
  cases value with
  | empty => simp [prepareChild] at cached
  | reference name => simp [prepareChild] at cached
  | node entry edges depth free =>
      by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
      · simp [prepareChild, SourcePruningEnumerationCachedChild.prepareOrdinary, terminal] at cached
      simp only [prepareChild, Option.map_eq_some_iff] at cached
      obtain ⟨result, prepared, rowsSame⟩ := cached
      have resultSame : result = (fragment, after) := (List.cons.inj rowsSame).1
      subst result
      simp only [SourcePruningEnumerationCachedChild.prepareOrdinary, terminal, Bool.false_eq_true,
        ↓reduceIte, encodeNode, Option.bind_some, Option.bind_eq_some_iff,
        Option.map_eq_some_iff] at prepared
      obtain ⟨allocation, nativeAllocated, writtenAfter, written, pairSame⟩ := prepared
      have afterSame : writtenAfter = after := (Prod.mk.inj pairSame).2
      subst writtenAfter
      simp only [SourcePruningEnumerationCachedChild.allocate, Option.map_eq_some_iff] at nativeAllocated
      obtain ⟨flag, _classified, allocationSame⟩ := nativeAllocated
      subst allocation
      simp only [SourcePruningEnumerationCachedChild.writeSlot, Option.bind_eq_some_iff] at written
      obtain ⟨old, _stored, nativeWritten⟩ := written
      simp only [SourcePruningEnumerationNativeIndex.write, Option.bind_eq_some_iff,
        Option.some.injEq] at nativeWritten
      obtain ⟨afterFlag, _afterClassified, removed, _removedCounts, saved, _savedCounts, afterSame⟩ := nativeWritten
      subst after
      refine ⟨rfl, ?_⟩
      have mass := SourcePruningEnumerationSuspendedMass.incoming_mass
        (allocated (some (entry.identity + 1)) before.core) before.core.counter
        (some (entry.identity + 1)) (some (entry.identity + 1)) scs []
        (allocated_slot (some (entry.identity + 1)) before.core aligned)
      simpa only [List.append_nil, allocated_mass] using mass
  | union entry _ _ _ | mu entry _ _ _ =>
      by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
      · simp [prepareChild, terminal] at cached
      simp only [prepareChild, terminal, Bool.false_eq_true, ↓reduceIte, encodeNode,
        Option.bind_some, Option.map_eq_some_iff] at cached
      obtain ⟨allocation, nativeAllocated, rowsSame⟩ := cached
      simp only [SourcePruningEnumerationCachedChild.allocate, Option.map_eq_some_iff] at nativeAllocated
      obtain ⟨flag, _classified, allocationSame⟩ := nativeAllocated
      subst allocation
      have afterSame := (Prod.mk.inj (List.cons.inj rowsSame).1).2
      subst after
      exact ⟨rfl, by simpa only [Nat.add_zero] using allocated_mass (some (entry.identity + 1)) before.core⟩

/-- Every actual successful singleton adds at most the complete incoming bucket length. -/
theorem singleton_counter_mass_le
    (heap : InternedConstructorTemplates.State Symbol Constraint) (fuel : Nat)
    (scs : List Suspended) (value : Node) (before after : Cached)
    (fragment : Fragments.Fragment Symbol)
    (aligned : before.core.counter = before.core.values.length)
    (cached : prepareChild heap fuel scs value before = some [(fragment, after)]) :
    after.core.counter = before.core.counter + 1 ∧
      suspendedBound after.core ≤ suspendedBound before.core + scs.length := by
  obtain ⟨counter, mass⟩ := singleton_counter_mass heap fuel scs value before after fragment aligned cached
  refine ⟨counter, ?_⟩
  rw [mass]
  cases value <;> simp only [Nat.add_zero] <;> omega

end MicroCFTA.SourcePruningEnumerationCachedPrepare

namespace MicroCFTA.SourcePruningEnumerationChildDispatch
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Empty rejects at the original native endpoint and retains exactly the input cache. -/
theorem empty_cached
    (checkEmpty : Bool) (r n p h k : Nat) (scs : List Suspended)
    (caller : Caller width) (before : Cached) (queries : Queries) :
    run checkEmpty r n p h k scs .empty caller before queries =
      ((.ok (some []), caller, queries, before.core, before.waiting), some before) := by
  simp [run]

end MicroCFTA.SourcePruningEnumerationChildDispatch
