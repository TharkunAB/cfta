import MicroCFTA.SourceSynthesisHereditaryProgramFields
import MicroCFTA.SourcePruningEnumerationSelectedValue
import MicroCFTA.SourcePruningEnumerationEdgeInputs
import MicroCFTA.SourcePruningEnumerationSharedChildStableNeutral

/-!
# Full suspended restrictions at selected Program children

The recursive source certificate passes through actual one-layer preparation.
The selected row and its literal child index derive the child's certificate.
A successful shared child row excludes Empty. The Program child is ordinary
and retains its complete bucket. Type children have no retention conclusion.
These laws do not derive a certificate for every later selected cache slot.
-/
namespace MicroCFTA.SourceSynthesisSelectedProgramChildRetention
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceSynthesisHereditaryProgramFields (ValueFields EdgeFields)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Raw" => List (Except EnumerationState.Error
  (Fragment × EnumerationState.State Symbol Constraint))
variable {width : Nat}

/-- Complete source layouts assign Program operands to these physical positions. -/
def ProgramSlot (edge : EdgeValue Symbol Constraint) (index : Nat) : Prop :=
  (edge.children.length = 4 ∧ (index = 2 ∨ index = 3)) ∨
    (edge.children.length = 2 ∧ index = 1)

private theorem edge_child_fields
    {valid : Constraint → Prop} {literal : String → Symbol}
    {edge : EdgeValue Symbol Constraint} {index : Nat} {incoming : Node}
    (fields : EdgeFields valid literal edge) (slot : ProgramSlot edge index)
    (found : edge.children[index]? = some incoming) : ValueFields valid literal incoming := by
  cases fields with
  | annotated edge annotation guard children typed =>
      simp [ProgramSlot, children] at slot
  | application edge types marker function argument symbol guard children
      typesTyped markerTyped functionFields argumentFields =>
      have indices : index = 2 ∨ index = 3 := by
        simpa [ProgramSlot, children] using slot
      rcases indices with rfl | rfl
      · simp only [children, List.getElem?_cons_succ, List.getElem?_cons_zero] at found
        exact (Option.some.inj found) ▸ functionFields
      · simp only [children, List.getElem?_cons_succ, List.getElem?_cons_zero] at found
        exact (Option.some.inj found) ▸ argumentFields
  | filter edge goal candidates symbol guard children goalTyped candidateFields =>
      have indexSame : index = 1 := by simpa [ProgramSlot, children] using slot
      subst index
      simp only [children, List.getElem?_cons_succ, List.getElem?_cons_zero] at found
      exact (Option.some.inj found) ▸ candidateFields

/-- Actual child-input construction keeps the recursive fields and both descended buckets. -/
theorem input_fields
    {valid : Constraint → Prop} {literal : String → Symbol}
    {entry : Cache.Interned InternedBinderProtocol.NodeKey}
    {rows : List (EdgeValue Symbol Constraint)} {depth : Nat}
    {free : List InternedBinderProtocol.Reference} {edge : EdgeValue Symbol Constraint}
    {scs : List Suspended} {start index : Nat} {tries : List EqualityTrie.Trie}
    {incoming : Node} {bucket : List Suspended}
    (fields : ValueFields valid literal (.node entry rows depth free))
    (selected : edge ∈ rows) (slot : ProgramSlot edge index)
    (input : (SourcePruningEnumerationEdgeInputs.children edge scs start tries)[index]? =
      some (incoming, bucket)) :
    ValueFields valid literal incoming ∧
      bucket = descendScs index scs ++ descendScs index (suspendedVars start tries) := by
  have rowFields : EdgeFields valid literal edge := by
    cases fields with
    | node _ _ _ _ checked => exact checked edge selected
  rw [SourcePruningEnumerationEdgeInputs.children, List.getElem?_map] at input
  obtain ⟨indexed, indexedStored, pairSame⟩ := Option.map_eq_some_iff.mp input
  rw [List.getElem?_zipIdx] at indexedStored
  obtain ⟨child, childStored, rfl⟩ := Option.map_eq_some_iff.mp indexedStored
  have childSame : child = incoming := congrArg Prod.fst pairSame
  refine ⟨childSame ▸ edge_child_fields rowFields slot childStored, ?_⟩
  simpa only [Nat.zero_add] using (congrArg Prod.snd pairSame).symm

section Preparation
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- Actual one-layer preparation preserves a source Program value and its heap verbatim. -/
theorem prepared_fields
    {valid : Constraint → Prop} {literal : String → Symbol} {fuel : Nat}
    {source result : Node} {before after : InternedConstructorTemplates.State Symbol Constraint}
    (fields : ValueFields valid literal source)
    (actual : SourcePruningEnumerationSelectedValue.run fuel source before = .done result after) :
    result = source ∧ after = before ∧ ValueFields valid literal result := by
  cases fields with
  | empty =>
      cases actual
      exact ⟨rfl, rfl, .empty⟩
  | node entry rows depth free checked =>
      cases actual
      exact ⟨rfl, rfl, .node entry rows depth free checked⟩
end Preparation

section Child
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- A literal successful Program child row is ordinary and retains its entire bucket. -/
theorem successful_input_retained
    {valid : Constraint → Prop} {literal : String → Symbol}
    {entry : Cache.Interned InternedBinderProtocol.NodeKey}
    {rows : List (EdgeValue Symbol Constraint)} {depth : Nat}
    {free : List InternedBinderProtocol.Reference} {edge : EdgeValue Symbol Constraint}
    {scs : List Suspended} {start index : Nat} {tries : List EqualityTrie.Trie}
    {incoming : Node} {bucket : List Suspended}
    (fields : ValueFields valid literal (.node entry rows depth free))
    (selected : edge ∈ rows) (slot : ProgramSlot edge index)
    (input : (SourcePruningEnumerationEdgeInputs.children edge scs start tries)[index]? =
      some (incoming, bucket))
    {checkEmpty : Bool} {r n p h k : Nat} {beforeCaller afterCaller : Caller width}
    {before : Cached} {queries savedQueries : Queries} {raw : Raw}
    {outer : EnumerationState.State Symbol Constraint} {waiting : EnumerationWaitingIndex.Waiting}
    {cached : Option Cached} {fragment : Fragment} {output : EnumerationState.State Symbol Constraint}
    (actual : SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run
      checkEmpty r n p h k bucket incoming beforeCaller before queries =
      ((.ok (some raw), afterCaller, savedQueries, outer, waiting), cached))
    (member : Except.ok (fragment, output) ∈ raw) :
    ValueFields valid literal incoming ∧
      (match incoming with | .node _ _ _ _ => True | _ => False) ∧
      (match incoming with
        | .node _ _ _ _ => bucket
        | _ => if bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) then bucket else []) = bucket := by
  have own := (input_fields fields selected slot input).1
  have nonempty : incoming ≠ .empty := by
    intro empty
    have projected := congrArg (fun observation => observation.1.1) actual
    have rawSame : [] = raw := by
      simpa only [SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run,
        ite_eq_left empty, Except.ok.injEq, Option.some.injEq] using projected
    rw [← rawSame] at member
    cases member
  refine ⟨own, ?_⟩
  cases own with
  | empty => exact (nonempty rfl).elim
  | node => exact ⟨True.intro, rfl⟩

/-- Current source fields derive full Program-child restrictions in actual neutral semantics. -/
theorem program_child_neutral_semantics
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller width) (before : Cached)
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
    (ranges : SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.Ranges
      checkEmpty bucket incoming beforeCaller before memos.query)
    {valid : Constraint → Prop} {literal : String → Symbol}
    {entry : Cache.Interned InternedBinderProtocol.NodeKey}
    {rows : List (EdgeValue Symbol Constraint)} {depth : Nat}
    {free : List InternedBinderProtocol.Reference} {edge : EdgeValue Symbol Constraint}
    {scs : List Suspended} {start index : Nat} {tries : List EqualityTrie.Trie}
    (fields : ValueFields valid literal (.node entry rows depth free))
    (selected : edge ∈ rows) (slot : ProgramSlot edge index)
    (input : (SourcePruningEnumerationEdgeInputs.children edge scs start tries)[index]? =
      some (incoming, bucket))
    {r n p h k : Nat} {raw : Raw} {afterCaller : Caller width} {after : Cached}
    {savedQueries : Queries} {outer : EnumerationState.State Symbol Constraint}
    {waiting : EnumerationWaitingIndex.Waiting}
    (observed : ∀ extraRepresentative extraNative P H extraIndex, p ≤ P → h ≤ H →
      SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run
        checkEmpty (r + extraRepresentative) (n + extraNative) P H (k + extraIndex)
        bucket incoming beforeCaller before memos.query =
        ((.ok (some raw), afterCaller, savedQueries, outer, waiting), some after)) :
    ∀ held, held < before.core.counter → Avoids before.core.representatives held bucket →
    ∀ (ambient : InternedGuardedLanguage.Env Symbol)
      (residualMeaning : Constraint → Language.Term Symbol → Prop)
      (assignment : Nat → Language.Term Symbol) (fragment : Fragment)
      (output : EnumerationState.State Symbol Constraint), Except.ok (fragment, output) ∈ raw →
      (Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient afterCaller.checked.native.machine.heap) residualMeaning assignment
          (EnumerationFrame.neutralize held output) ↔
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient beforeCaller.checked.native.machine.heap) residualMeaning assignment
            (EnumerationFrame.neutralize held before.core) ∧
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient incoming (Fragments.fill assignment fragment) ∧
        ∀ sc ∈ bucket, Suspended.Holds assignment (Fragments.fill assignment fragment) sc) := by
  intro held inside avoids ambient residualMeaning assignment fragment output member
  have semantic :=
    SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.stable_neutral_semantics
      formulas solver inventory beforeCaller before checkEmpty bucket incoming roots memos initial
      safe paths counts flags realized bounded pending available closed ranges observed
      held inside avoids ambient residualMeaning assignment fragment output member
  have retention := successful_input_retained fields selected slot input
    (observed 0 0 p h 0 (Nat.le_refl _) (Nat.le_refl _)) member
  have ordinary := retention.2.1
  cases incoming <;> first
    | exact semantic
    | cases ordinary
end Child
end MicroCFTA.SourceSynthesisSelectedProgramChildRetention
