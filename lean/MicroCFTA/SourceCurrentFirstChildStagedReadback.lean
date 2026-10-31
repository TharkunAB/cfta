import MicroCFTA.SourceCurrentFirstChildPost
import MicroCFTA.SourceSizedPrefixKnownOrdinaryHeap

/-! Successful first-child execution retains the original staged child handles and values. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentFirstChildStagedReadback
open EnumerationState EnumerationCorrectness EnumerationCompleteness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourcePruningEnumerationIncomingReservation (Seed Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceCurrentAllocatedFiniteOrdinaryStored (Stored)
open SourceSizedPrefixKnownOrdinary (KnownOrdinary)
attribute [local instance] FormulaExecutable.formulaDecidableEq
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {bits : Nat} [DecidableEq (EdgeKey Symbol Constraint)]

open scoped Classical in
/-- The first actual child success retains availability and exact readback for all remaining children. -/
theorem selected_first_child_staged_readback (bound : Nat) (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (before : Cached) (memos : Memos)
    (parentSlot parentHandle : Nat) (scs : List Suspended) (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edge : EdgeValue Symbol Constraint) (roots : Nat → Nat) (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (initial : Context formulas solver inventory caller memos)
    (known : KnownOrdinary bound caller.checked.native.machine.heap before)
    (parent : before.core.values[parentSlot]? = some (.unenumerated (some parentHandle) scs))
    (decoded : lookupNode caller.checked.native.machine.heap parentHandle = some (.node entry edges depth free))
    (selected : edge ∈ InternedEdgeResidency.nodeEdges (.node entry edges depth free))
    (safe : Safe before.core) (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter) (pending : InputsPending before.core scs)
    (allowed : arityAllows edge.children.length scs = true)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (fits : Fits seed.2 caller.checked) (stored : Stored caller.checked.native)
    (annotated : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (reserved : Reserved bits seed
      (((SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries).head?.getD (.empty, [])).2.length + 1)) :
    ∃ staged after, SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
        some [((edge.entry.key.symbol, staged, residual), after)] ∧
      ∀ incoming bucket rest, staged.map (fun input => (input.1, input.2.1)) = (incoming, bucket) :: rest →
        MergedOrdinaryHeight.height incoming < MergedOrdinaryHeight.height (.node entry edges depth free) ∧
        ∀ checkEmpty r n p h k,
          let actual := SourcePruningEnumerationChildDispatch.run checkEmpty r n p h k bucket incoming caller after memos.query
          match actual.1.1 with
          | .ok (some [.ok _]) => ∃ next final,
              Post formulas solver next caller actual.1.2.1 final ∧ final.query = actual.1.2.2.1 ∧
              ∀ value siblings, (value, siblings) ∈ rest →
                Available actual.1.2.1.checked.native.machine.heap value ∧ ∃ handle,
                encodeNode value = some handle ∧
                lookupNode actual.1.2.1.checked.native.machine.heap handle = some value ∧ value.free = []
          | _ => True := by
  letI : DecidableEq Node := fun a b => Classical.propDecidable (a = b)
  obtain ⟨staged, after, prepared, inputs, safeAfter, pathsAfter, realizedAfter, countsAfter, _flagsAfter,
    knownAfter, inputFacts⟩ := SourceSizedPrefixOrdinaryIncomingInputs.complete bound caller.checked.native.machine.heap before
      known parentSlot parentHandle scs parent entry edges depth free decoded edge selected roots
      initial.ready.good.heap safe realized paths counts flags bounded pending allowed tries residual projected
  refine ⟨staged, after, prepared, ?_⟩
  intro incoming bucket rest head
  have originalHead := inputs.symm.trans head
  obtain ⟨available, closed, _ordinary, smaller, _height, allocated, pendingAfter⟩ :=
    inputFacts incoming bucket (by rw [head]; exact List.mem_cons_self)
  refine ⟨smaller, ?_⟩
  intro checkEmpty r n p h k
  have currentReservation : Reserved bits seed (bucket.length + 1) := by
    simpa only [originalHead, List.head?_cons, Option.getD_some] using reserved
  have childPost := SourceCurrentFirstChildPost.child_continue_post bound seed formulas solver inventory caller after
    memos checkEmpty r n p h k incoming bucket roots initial safeAfter pathsAfter countsAfter allocated pendingAfter
    realizedAfter available closed fits currentReservation annotated stored knownAfter
  dsimp only at childPost ⊢
  generalize observed : SourcePruningEnumerationChildDispatch.run checkEmpty r n p h k bucket incoming caller after memos.query = actual
    at childPost ⊢
  rcases actual with ⟨⟨tag, reached, savedQueries, outer, waiting⟩, cache⟩
  cases tag with
  | error fault => trivial
  | ok possible =>
      cases possible with
      | none => trivial
      | some rows =>
          cases rows with
          | nil => trivial
          | cons firstRow tail =>
              cases firstRow with
              | error fault => trivial
              | ok row =>
                  cases tail with
                  | cons second remaining => trivial
                  | nil =>
                      obtain ⟨next, final, post, querySame⟩ := childPost
                      refine ⟨next, final, post, querySame, ?_⟩
                      intro value siblings member
                      obtain ⟨siblingAvailable, siblingClosed, _ordinary, _smaller, _height, _allocated, _pending⟩ :=
                        inputFacts value siblings (by rw [head]; exact List.mem_cons_of_mem _ member)
                      obtain ⟨handle, encoded, present⟩ := SourcePruningEnumerationNodes.available_readback
                        caller.checked.native.machine.heap value
                        initial.ready.good.heap.semantic.1.normal.facts.coherent siblingAvailable siblingClosed
                      refine ⟨post.effects.keeps.available value siblingAvailable, handle, encoded, ?_, siblingClosed⟩
                      exact SourceSizedPrefixKnownOrdinaryHeap.post_lookupNode post handle value present

end MicroCFTA.SourceCurrentFirstChildStagedReadback
