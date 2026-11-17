import MicroCFTA.SourcePruningEnumerationSharedChildObservedResources
import MicroCFTA.SourceSynthesisProgramRolesNativeHeap

namespace MicroCFTA.SourceSynthesisProgramRolesObservedChild
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourcePruningEnumerationSharedIncomingReservation (Seed Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceSynthesisProgramEnumerationRoles (ProgramSlots)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
set_option autoImplicit false
variable {bits : Nat}

/-!
Note [Observed annotation children retain old Program marks]
The resource observer retains the literal child result at all five supplied
fuels. Its native Post preserves old node lookups. Its class protection and
reference effect preserve each old marked slot and its incoming exclusion.
These are the same algebraic steps as child_inputs_program_slots in the eager
reservation owner. This public observer derives those effects from the actual
run and past resources. It does not take the private ChildInputs as a premise.
The mark predicate stays fixed. Mu and Union annotation children receive no
new Program mark from this theorem.
-/

/-- An actual child singleton preserves all old Program slots at its returned endpoint. -/
theorem observed_complete_program_slots
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2)) (before : Cached)
    (checkEmpty : Bool) (bucket : List Suspended) (incoming : Node)
    (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (safe : Safe before.core) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate beforeCaller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (bounded : ∀ sc ∈ bucket, sc.var < before.core.counter)
    (pending : InputsPending before.core bucket)
    (available : Available beforeCaller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (fits : Fits seed.2 beforeCaller.checked)
    (reserved : Reserved bits seed (bucket.length + 1))
    (known : Heap (fun guard => guard ∈ seed.1) beforeCaller.checked.native.machine.heap)
    (valid : Constraint → Prop) (literal : String → Symbol) (marked : Nat → Prop)
    (slots : ProgramSlots valid literal beforeCaller.checked.native.machine.heap before.core marked)
    (avoids : ∀ held, marked held → Avoids before.core.representatives held bucket)
    (r n p h k : Nat) (fragment : Fragment) (returned : Core)
    (afterCaller : Caller (bits + 2)) (after : Cached) (savedQueries : Queries)
    (outer : Core) (waiting : EnumerationWaitingIndex.Waiting)
    (observed : SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run
      checkEmpty r n p h k bucket incoming beforeCaller before memos.query =
      ((.ok (some [.ok (fragment, returned)]), afterCaller, savedQueries, outer, waiting), some after)) :
    returned = after.core ∧
      ProgramSlots valid literal afterCaller.checked.native.machine.heap after.core marked := by
  obtain ⟨_final, _next, _afterRoots, _stable, post, _querySame, growth, _afterPaths,
      _storage, _afterRealized, _afterCounts, _afterFlags, _origin, protection,
      referenceEffect, _pendingAfter, shape, _afterFits, _afterKnown⟩ :=
    SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.observed_complete_with_fragments_resources
      seed formulas solver inventory beforeCaller before checkEmpty bucket incoming roots memos
      initial safe paths counts flags realized bounded pending available closed fits reserved known
      r n p h k [.ok (fragment, returned)] afterCaller after savedQueries outer waiting observed
      (.inr ⟨fragment, returned, rfl⟩)
  rcases shape with rejected | ⟨produced, singleton, _afterSafe, _bound, _pending, _avoid⟩
  · cases rejected
  · have pairSame : (fragment, returned) = (produced, after.core) :=
      Except.ok.inj (List.cons.inj singleton).1
    refine ⟨congrArg Prod.snd pairSame, ?_⟩
    have protects (held : Nat) (known : marked held) :
        EnumerationDriver.Protected held before.core after.core :=
      protection held (slots.bounded held known) (slots.roots held known) (avoids held known)
    have references (held : Nat) (known : marked held) :
        EnumerationReferences.ReferencesAllowed
          (fun target => ¬UnionFind.SameClass before.core.representatives held target) after.core :=
      referenceEffect _ (slots.incoming held known) (avoids held known)
    have carried := SourceSynthesisProgramRolesNativeHeap.keeps_program_slots
      beforeCaller.checked.native.machine.heap afterCaller.checked.native.machine.heap before.core marked
      post.effects.keeps slots
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro held known
      exact Nat.lt_of_lt_of_le (slots.bounded held known) growth
    · intro held known
      exact (protects held known).root
    · intro held known payload member sc listed same
      exact references held known payload member sc listed (((protects held known).classes sc.var).mp same)
    · intro held known
      obtain ⟨payload, stored, role⟩ := carried.stored held known
      exact ⟨payload, (protects held known).value.trans stored, role⟩

end MicroCFTA.SourceSynthesisProgramRolesObservedChild

#check MicroCFTA.SourceSynthesisProgramRolesObservedChild.observed_complete_program_slots
#print axioms MicroCFTA.SourceSynthesisProgramRolesObservedChild.observed_complete_program_slots
