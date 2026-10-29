import MicroCFTA.SourcePruningEnumerationStorageProgress
import MicroCFTA.SourcePruningEnumerationChildTraversal
import MicroCFTA.SourcePruningEnumerationSelectedEdge

/-!
# Constructor cost through actual nonterminal child allocation

The trace supplies the actual ordered child calls and their returned caches.
The assignment installs one chosen term at each actual fresh graph slot.
Terminal assimilation and recursive callback progress remain separate.
-/
namespace MicroCFTA.SourcePruningEnumerationConstructorStorageProgress
open Language EnumerationState EnumerationCorrectness
open InternedConstructorTemplates SourcePruningEnumerationNodes
open EnumerationStorageProgress
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat}
local instance constructorStorageMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

private theorem shallow_shape
    (bucket : List Suspended) (incoming : Node) (before after : EnumerationState.State Symbol Constraint)
    (fragment : Fragment) (action : EnumerateM Symbol Constraint Fragment)
    (aligned : before.counter = before.values.length)
    (nonterminal : bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (prepared : SourcePruningEnumerationShallowChild.prepareChild bucket incoming = some action)
    (success : Success action before fragment after) :
    ∃ handle childBucket,
      fragment = .hole before.counter ∧
      after = {allocated (some handle) before with values :=
        (allocated (some handle) before).values.set before.counter (.unenumerated (some handle) childBucket)} := by
  cases incoming with
  | empty =>
      simp only [SourcePruningEnumerationShallowChild.prepareChild, Option.some.injEq] at prepared
      rw [← prepared] at success
      simp [Success, reject, ExceptT.run] at success
  | reference name => cases prepared
  | node entry _rows _depth _free =>
      simp only [SourcePruningEnumerationShallowChild.prepareChild, nonterminal,
        Bool.false_eq_true, ↓reduceIte, encodeNode, Option.some.injEq] at prepared
      rw [← prepared] at success
      obtain ⟨uv, middle, allocation, continued⟩ := (success_bind _ _ _ _ _).mp success
      have exactState : uv = before.counter ∧ middle = allocated (some (entry.identity + 1)) before := by
        simpa [Success, allocate_exact, ExceptT.run] using allocation
      obtain ⟨rfl, rfl⟩ := exactState
      obtain ⟨ignored, written, writeRun, pureRun⟩ := (success_bind _ _ _ _ _).mp continued
      cases ignored
      obtain ⟨rfl, rfl⟩ := (success_pure _ _ _ _).mp pureRun
      exact ⟨entry.identity + 1, bucket, rfl, (EnumerationDriver.modify_success _ _ _).mp writeRun⟩
  | union entry _members _depth _free =>
      simp only [SourcePruningEnumerationShallowChild.prepareChild, nonterminal,
        Bool.false_eq_true, ↓reduceIte, encodeNode, Option.some.injEq] at prepared
      rw [← prepared] at success
      obtain ⟨uv, middle, allocation, pureRun⟩ := (success_bind _ _ _ _ _).mp success
      have exactState : uv = before.counter ∧ middle = allocated (some (entry.identity + 1)) before := by
        simpa [Success, allocate_exact, ExceptT.run] using allocation
      obtain ⟨rfl, rfl⟩ := exactState
      obtain ⟨rfl, rfl⟩ := (success_pure _ _ _ _).mp pureRun
      refine ⟨entry.identity + 1, [], rfl, ?_⟩
      simp [allocated, aligned, List.set_append_right]

  | mu entry _body _depth _ordinary =>
      simp only [SourcePruningEnumerationShallowChild.prepareChild, nonterminal,
        Bool.false_eq_true, ↓reduceIte, encodeNode, Option.some.injEq] at prepared
      rw [← prepared] at success
      obtain ⟨uv, middle, allocation, pureRun⟩ := (success_bind _ _ _ _ _).mp success
      have exactState : uv = before.counter ∧ middle = allocated (some (entry.identity + 1)) before := by
        simpa [Success, allocate_exact, ExceptT.run] using allocation
      obtain ⟨rfl, rfl⟩ := exactState
      obtain ⟨rfl, rfl⟩ := (success_pure _ _ _ _).mp pureRun
      refine ⟨entry.identity + 1, [], rfl, ?_⟩
      simp [allocated, aligned, List.set_append_right]

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem child_cost
    (checkEmpty : Bool) (r n p h k : Nat) (bucket : List Suspended) (incoming : Node)
    (caller reached : Caller width) (before after : Cached) (queries saved : Queries)
    (fragment : Fragment) (outer : EnumerationState.State Symbol Constraint)
    (waiting : EnumerationWaitingIndex.Waiting)
    (assignment extended : Nat → Term Symbol)
    (aligned : before.core.counter = before.core.values.length)
    (agree : ∀ uv < before.core.counter, extended uv = assignment uv)
    (nonterminal : bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (observed : SourcePruningEnumerationChildDispatch.run checkEmpty r n p h k bucket incoming caller before queries =
      ((.ok (some [.ok (fragment, after.core)]), reached, saved, outer, waiting), some after)) :
    fragment = .hole before.core.counter ∧
    after.core.counter = before.core.counter + 1 ∧
    after.core.counter = after.core.values.length ∧
    (∀ uv < before.core.counter, after.core.values[uv]? = before.core.values[uv]?) ∧
    pendingSize after.core extended = pendingSize before.core assignment +
      NumberedTerms.size (extended before.core.counter) := by
  have nonempty : incoming ≠ .empty := by
    intro same
    subst incoming
    simp [SourcePruningEnumerationChildDispatch.run] at observed
  have noHere : (bucket.partition (fun sc => EqualityTrie.isTerminal sc.trie)).1 = [] := by
    simp only [List.partition_eq_filter_filter]
    exact List.filter_eq_nil_iff.mpr (fun sc member => List.any_eq_false.mp nonterminal sc member)
  cases partitioned : bucket.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
  | mk here descendants =>
      have hereSame : here = [] := by simpa only [partitioned] using noHere
      subst here
      have raw := congrArg (fun result => result.1.1) observed
      cases prepared : SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint) bucket incoming with
      | none =>
          simp only [SourcePruningEnumerationChildDispatch.run, SourcePruningEnumerationChildDispatch.observe,
            ite_eq_right nonempty, partitioned, prepared] at raw
          cases raw
      | some action =>
          simp only [SourcePruningEnumerationChildDispatch.run, SourcePruningEnumerationChildDispatch.observe,
            ite_eq_right nonempty, partitioned, prepared] at raw
          have actionRun : ExceptT.run (action before.core) = [.ok (fragment, after.core)] :=
            Option.some.inj (Except.ok.inj raw)
          have successful : Success action before.core fragment after.core := by
            rw [Success, actionRun]
            exact List.mem_cons_self
          obtain ⟨handle, childBucket, fragmentSame, shape⟩ :=
            shallow_shape bucket incoming before.core after.core fragment action aligned nonterminal prepared successful
          have baseStored := allocated_slot (some handle) before.core aligned
          have baseCost := EnumerationStorageProgress.allocate_pendingSize (some handle) before.core
            (allocated (some handle) before.core) before.core.counter assignment extended aligned agree
            (by simp [Success, allocate_exact, ExceptT.run])
          have writtenCost := EnumerationStorageProgress.values_set_pendingSize
            (allocated (some handle) before.core) before.core.counter
            (.unenumerated (some handle) []) (.unenumerated (some handle) childBucket) extended baseStored
          simp only at baseCost writtenCost
          refine ⟨fragmentSame, ?_, ?_, ?_, ?_⟩
          · rw [shape]
            rfl
          · rw [shape]
            simpa only [List.length_set] using allocated_supply (some handle) before.core aligned
          · intro uv inside
            have different : before.core.counter ≠ uv := by omega
            rw [shape]
            simp only [List.getElem?_set_ne different, allocated,
              List.getElem?_append_left (by omega : uv < before.core.values.length)]
          · rw [shape]
            simp only [pendingSize] at baseCost writtenCost ⊢
            omega

/-- An actual nonterminal trace constructs one assignment and charges its real fresh graph slots. -/
theorem trace_pendingSize
    {checkEmpty : Bool} {r n p h k : Nat} {inputs : List (Node × List Suspended)}
    {caller reached : Caller width} {before after : Cached} {queries saved : Queries}
    {fragments : List Fragment}
    (trace : SourcePruningEnumerationChildTraversal.Trace checkEmpty r n p h k inputs caller before queries
      fragments reached after saved)
    (assignment : Nat → Term Symbol) (terms : List (Term Symbol))
    (lengths : terms.length = inputs.length)
    (aligned : before.core.counter = before.core.values.length)
    (nonterminal : ∀ incoming bucket, (incoming, bucket) ∈ inputs →
      bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = false) :
    ∃ extended,
      extended = install assignment before.core.counter terms ∧
      (∀ uv < before.core.counter, extended uv = assignment uv) ∧
      after.core.counter = before.core.counter + terms.length ∧
      after.core.counter = after.core.values.length ∧
      (∀ uv < before.core.counter, after.core.values[uv]? = before.core.values[uv]?) ∧
      fragments.map (Fragments.fill extended) = terms ∧
      pendingSize after.core extended = pendingSize before.core assignment + NumberedTerms.forestSize terms := by
  induction trace generalizing assignment terms with
  | nil =>
      have termsNil : terms = [] := List.length_eq_zero_iff.mp (by simpa using lengths)
      subst terms
      exact ⟨assignment, rfl, fun _ _ => rfl, rfl, aligned, fun _ _ => rfl, rfl, by
        simp only [NumberedTerms.forestSize, Nat.add_zero]⟩
  | @cons incoming bucket rest caller middleCaller finalCaller before middle final queries middleQueries finalQueries
      fragment fragments outer waiting head tail ih =>
      cases terms with
      | nil => simp at lengths
      | cons term terms =>
          have remainingLength : terms.length = rest.length := by simpa using lengths
          let firstAssignment : Nat → Term Symbol := fun uv =>
            if uv = before.core.counter then term else assignment uv
          have firstAgree : ∀ uv < before.core.counter, firstAssignment uv = assignment uv := by
            intro uv bound
            simp only [firstAssignment, ite_eq_right (by omega : uv ≠ before.core.counter)]
          obtain ⟨fragmentSame, grows, middleAligned, headSlots, headCost⟩ :=
            child_cost checkEmpty r n p h k bucket incoming caller middleCaller before middle queries middleQueries
              fragment outer waiting assignment firstAssignment aligned firstAgree
              (nonterminal incoming bucket List.mem_cons_self) head
          have tailNonterminal : ∀ value scs, (value, scs) ∈ rest →
              scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false := by
            intro value scs member
            exact nonterminal value scs (List.mem_cons_of_mem _ member)
          obtain ⟨extended, installed, tailAgree, counter, finalAligned, tailSlots, filled, tailCost⟩ :=
            ih firstAssignment terms remainingLength middleAligned tailNonterminal
          refine ⟨extended, ?_, ?_, ?_, finalAligned, ?_, ?_, ?_⟩
          · simpa only [install, firstAssignment, grows] using installed
          · intro uv bound
            exact (tailAgree uv (by omega)).trans (firstAgree uv bound)
          · rw [counter, grows, List.length_cons]
            omega
          · intro uv bound
            exact (tailSlots uv (by omega)).trans (headSlots uv bound)
          · rw [fragmentSame]
            simp only [List.map_cons, Fragments.fill, filled]
            rw [tailAgree before.core.counter (by omega)]
            simp only [firstAssignment, ↓reduceIte]
          · simp only [firstAssignment, ↓reduceIte] at headCost
            rw [tailCost, headCost, NumberedTerms.forestSize]
            omega

/-- A real constructor trace and captured finalizer consume exactly one assigned constructor. -/
theorem constructor_pendingSize
    (checkEmpty : Bool) (r n p h k : Nat) (inputs : List (Node × List Suspended))
    (caller reached : Caller width) (before traversed after : Cached) (queries saved : Queries)
    (fragments : List Fragment) (assignment : Nat → Term Symbol) (symbol : Symbol)
    (terms : List (Term Symbol)) (target handle : Nat) (scs : List Suspended) (residual : Option Constraint)
    (lengths : terms.length = inputs.length)
    (aligned : before.core.counter = before.core.values.length)
    (nonterminal : ∀ incoming bucket, (incoming, bucket) ∈ inputs →
      bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (stored : before.core.values[target]? = some (.unenumerated (some handle) scs))
    (parent : assignment target = .node symbol terms)
    (completed : SourcePruningEnumerationChildTraversal.run checkEmpty r n p h k inputs caller before queries =
      .complete fragments reached saved traversed)
    (finalized : SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap k target
      (.node symbol fragments) (SourcePruningEnumerationSelectedEdge.finish residual (.node symbol fragments) traversed) =
      some after) :
    ∃ extended,
      extended = install assignment before.core.counter terms ∧
      (∀ uv < before.core.counter, extended uv = assignment uv) ∧
      Fragments.fill extended (.node symbol fragments) = assignment target ∧
      pendingSize after.core extended + 1 = pendingSize before.core assignment ∧
      pendingSize after.core extended < pendingSize before.core assignment := by
  have trace := SourcePruningEnumerationChildTraversal.complete_trace checkEmpty r n p h k
    inputs caller reached before traversed queries saved fragments completed
  obtain ⟨extended, installed, agree, _counter, _finalAligned, oldSlots, filled, traversalCost⟩ :=
    trace_pendingSize trace assignment terms lengths aligned nonterminal
  have inside : target < before.core.counter := by
    have bound := (List.getElem?_eq_some_iff.mp stored).elim (fun bound _ => bound)
    omega
  let recorded := SourcePruningEnumerationSelectedEdge.finish residual (.node symbol fragments) traversed
  have storedAfter : recorded.core.values[target]? = some (.unenumerated (some handle) scs) :=
    (oldSlots target inside).trans stored
  have finalCost := SourcePruningEnumerationStorageProgress.finalize_pendingSize
    reached.checked.native.machine.heap k target handle (.node symbol fragments) scs
    recorded after extended storedAfter finalized
  have recordingCost : pendingSize recorded.core extended = pendingSize traversed.core extended := rfl
  rw [recordingCost] at finalCost
  have targetSame : extended target = .node symbol terms := (agree target inside).trans parent
  have decrease : pendingSize after.core extended + 1 = pendingSize before.core assignment := by
    rw [targetSame, NumberedTerms.size] at finalCost
    omega
  refine ⟨extended, installed, agree, ?_, decrease, ?_⟩
  · simp only [Fragments.fill, filled, parent]
  · omega

end MicroCFTA.SourcePruningEnumerationConstructorStorageProgress
