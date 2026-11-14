import MicroCFTA.SourcePruningEnumerationIdentityResultMetadataErasure

set_option autoImplicit false

/-!
# Exact metadata transport through the existing child continuations

These theorem drafts preserve complete and stopped observations.
They add no operational worker or callback.
All new material in this file is uncompiled.
-/
namespace MicroCFTA.SourcePruningEnumerationIdentityResultMetadataErasure
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure)
open SourcePruningEnumerationSharedChildVisitors (visitChildren visitSelected visitCapturedWith shallowVisit)
open SourcePruningEnumerationSharedEagerChildren (eagerChild consumeSelected ordinaryNonterminal)
open SourcePruningEnumerationSharedBranching (scan)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Edge" => EdgeValue Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result
local notation "Observation" => SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.Observation
local notation "Hook" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.HookResult
local notation "Fold" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.Result
variable {width : Nat}
local notation "FoldFor" => fun (T : Type) => Fold (Output width T) (Failure width T) width
local notation "HookFor" => fun (T : Type) => Hook (Output width T) (Failure width T) width
local notation "Visitor" => fun (T : Type) => List Suspended → Node → Caller width → Cached → Queries →
  (Fragment → Caller width → Queries → Cached → FoldFor T) →
  (Observation width → Option Cached → FoldFor T) → FoldFor T

/-- List recursion preserves an exact transport equality of the existing child visitors. -/
theorem visitChildren_transport {Typing : Type} (left : Visitor Typing) (right : Visitor Unit)
    (transport : ∀ scs incoming current cache memos yes no,
      eraseFold (left scs incoming current cache memos yes no) =
        right scs incoming current cache memos
          (fun fragment reached saved after => eraseFold (yes fragment reached saved after))
          (fun observation candidate => eraseFold (no observation candidate)))
    (inputs : List (Node × List Suspended))
    (done : List Fragment → Caller width → Queries → Cached → FoldFor Typing)
    (stopped : List Fragment → Observation width → Option Cached → FoldFor Typing)
    (caller : Caller width) (before : Cached) (queries : Queries) :
    eraseFold (visitChildren left done stopped inputs caller before queries) =
      visitChildren right
        (fun fragments reached saved after => eraseFold (done fragments reached saved after))
        (fun completed observation candidate => eraseFold (stopped completed observation candidate))
        inputs caller before queries := by
  induction inputs generalizing done stopped caller before queries with
  | nil => rfl
  | cons input rest ih =>
      rcases input with ⟨value, bucket⟩
      simp only [visitChildren]
      rw [transport]
      apply congrArg (fun yes => right bucket value caller before queries yes
        (fun observation candidate => eraseFold (stopped [] observation candidate)))
      funext fragment reached saved after
      exact ih (fun fragments => done (fragment :: fragments))
        (fun completed => stopped (fragment :: completed)) reached after saved

/-- The same actual own-class preparation supplies both transported child tuples. -/
theorem visitSelected_transport {Typing : Type} (left : Visitor Typing) (right : Visitor Unit)
    (transport : ∀ scs incoming current cache memos yes no,
      eraseFold (left scs incoming current cache memos yes no) =
        right scs incoming current cache memos
          (fun fragment reached saved after => eraseFold (yes fragment reached saved after))
          (fun observation candidate => eraseFold (no observation candidate)))
    (consume : Receipt width → FoldFor Typing)
    (scs : List Suspended) (edge : Edge) (caller : Caller width) (before : Cached) (queries : Queries) :
    eraseFold (visitSelected left consume scs edge caller before queries) =
      visitSelected right (fun receipt => eraseFold (consume receipt)) scs edge caller before queries := by
  unfold visitSelected
  cases SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before with
  | none => rfl
  | some rows =>
      cases rows with
      | nil => rfl
      | cons first rest =>
          cases rest with
          | cons _ _ => rfl
          | nil =>
              rcases first with ⟨⟨symbol, staged, residual⟩, middle⟩
              dsimp only
              exact visitChildren_transport left right transport
                (staged.map (fun input => (input.1, input.2.1))) _ _ caller middle queries

/-- Shallow dispatch selects the same actual success or stop continuation. -/
theorem shallowVisit_erasure {Typing : Type}
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (r n p h k : Nat) (scs : List Suspended) (incoming : Node)
    (caller : Caller width) (before : Cached) (queries : Queries)
    (done : Fragment → Caller width → Queries → Cached → FoldFor Typing)
    (stopped : Observation width → Option Cached → FoldFor Typing) :
    eraseFold (shallowVisit checkEmpty r n p h k scs incoming caller before queries done stopped) =
      shallowVisit checkEmpty r n p h k scs incoming caller before queries
        (fun fragment reached saved after => eraseFold (done fragment reached saved after))
        (fun observation candidate => eraseFold (stopped observation candidate)) := by
  unfold shallowVisit
  cases SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run
      checkEmpty r n p h k scs incoming caller before queries with
  | mk observation candidate =>
      rcases observation with ⟨outcome, reached, saved, outer, waiting⟩
      cases outcome with
      | error fault => rfl
      | ok returned =>
          cases returned with
          | none => rfl
          | some rows =>
              cases rows with
              | nil => rfl
              | cons first rest =>
                  cases first with
                  | error fault => rfl
                  | ok pair =>
                      rcases pair with ⟨fragment, returned⟩
                      cases rest with
                      | cons _ _ => rfl
                      | nil => cases candidate <;> rfl

/-- A selected receipt retains the exact processed prefix and stop under erasure. -/
theorem consumeSelected_erasure {Typing : Type}
    (done : Fragment → Caller width → Queries → Cached → FoldFor Typing)
    (caller : Caller width) (queries : Queries) (receipt : Receipt width) :
    eraseFold (consumeSelected done caller queries receipt) =
      consumeSelected
        (fun fragment reached saved after => eraseFold (done fragment reached saved after))
        caller queries receipt := by
  unfold consumeSelected
  cases receipt with
  | complete fragment reached saved after => cases done fragment reached saved after <;> rfl
  | unhandled => rfl
  | rejected reached saved after => rfl
  | finalizeStopped fragment reached saved after => rfl
  | stopped completed observation candidate =>
      cases SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance
          (.stopped completed observation candidate) with
      | none => rfl
      | some endpoint => cases endpoint; rfl

/-- Capture and finalization retain the same receipt and native endpoint. -/
theorem visitCapturedWith_transport {Typing : Type} (left : Visitor Typing) (right : Visitor Unit)
    (transport : ∀ scs incoming current cache memos yes no,
      eraseFold (left scs incoming current cache memos yes no) =
        right scs incoming current cache memos
          (fun fragment reached saved after => eraseFold (yes fragment reached saved after))
          (fun observation candidate => eraseFold (no observation candidate)))
    (hook : Fragment → Caller width → Queries → Cached → HookFor Typing)
    (k target : Nat) (scs : List Suspended) (edge : Edge)
    (caller : Caller width) (queries : Queries) (before : Cached) :
    eraseFold (visitCapturedWith left hook k target scs edge caller queries before) =
      visitCapturedWith right
        (fun fragment reached saved after => eraseResult (hook fragment reached saved after))
        k target scs edge caller queries before := by
  unfold visitCapturedWith
  rw [visitSelected_transport left right transport]
  apply congrArg (fun consume => visitSelected right consume scs edge caller before queries)
  funext receipt
  cases receipt with
  | complete fragment reached saved after =>
      cases SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap k target fragment after with
      | none =>
          exact receipt_erasure hook caller queries (some (.finalizeStopped fragment reached saved after))
      | some finished =>
          exact receipt_erasure hook caller queries (some (.complete fragment reached saved finished))
  | unhandled => exact receipt_erasure hook caller queries (some .unhandled)
  | rejected reached saved after =>
      exact receipt_erasure hook caller queries (some (.rejected reached saved after))
  | finalizeStopped fragment reached saved after =>
      exact receipt_erasure hook caller queries (some (.finalizeStopped fragment reached saved after))
  | stopped completed observation candidate =>
      exact receipt_erasure hook caller queries (some (.stopped completed observation candidate))

/-- The actual eager child commutes with erasure at every native input. -/
theorem eagerChild_erasure {Typing : Type}
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge)
    (scs : List Suspended) (incoming : Node) (caller : Caller width) (before : Cached) (queries : Queries)
    (done : Fragment → Caller width → Queries → Cached → FoldFor Typing)
    (stopped : Observation width → Option Cached → FoldFor Typing) :
    eraseFold (eagerChild checkEmpty r n p h k edgesOf scs incoming caller before queries done stopped) =
      eagerChild checkEmpty r n p h k edgesOf scs incoming caller before queries
        (fun fragment reached saved after => eraseFold (done fragment reached saved after))
        (fun observation candidate => eraseFold (stopped observation candidate)) := by
  revert scs caller before queries done stopped
  refine (measure MergedOrdinaryHeight.height).wf.induction incoming ?_
  intro incoming ih scs caller before queries done stopped
  let left : Visitor Typing := fun bucket child current cache memos yes no =>
    if _lower : MergedOrdinaryHeight.height child < MergedOrdinaryHeight.height incoming then
      eagerChild checkEmpty r n p h k edgesOf bucket child current cache memos yes no
    else shallowVisit checkEmpty r n p h k bucket child current cache memos yes no
  let right : Visitor Unit := fun bucket child current cache memos yes no =>
    if _lower : MergedOrdinaryHeight.height child < MergedOrdinaryHeight.height incoming then
      eagerChild checkEmpty r n p h k edgesOf bucket child current cache memos yes no
    else shallowVisit checkEmpty r n p h k bucket child current cache memos yes no
  have childTransport : ∀ bucket child current cache memos yes no,
      eraseFold (left bucket child current cache memos yes no) =
        right bucket child current cache memos
          (fun fragment reached saved after => eraseFold (yes fragment reached saved after))
          (fun observation candidate => eraseFold (no observation candidate)) := by
    intro bucket child current cache memos yes no
    by_cases lower : MergedOrdinaryHeight.height child < MergedOrdinaryHeight.height incoming
    · simp only [left, right, lower, ↓reduceDIte, ↓reduceIte]
      exact ih child lower bucket current cache memos yes no
    · simp only [left, right, lower, ↓reduceDIte, ↓reduceIte]
      exact shallowVisit_erasure checkEmpty r n p h k bucket child current cache memos yes no
  conv =>
    lhs
    arg 1
    rw [eagerChild]
  conv =>
    rhs
    rw [eagerChild]
  by_cases ordinary : ordinaryNonterminal scs incoming = true
  · simp only [ordinary, ↓reduceIte]
    change eraseFold (scan
        (fun edge reached saved captured =>
          visitSelected left (consumeSelected done reached saved) scs edge reached captured saved)
        before (edgesOf incoming) caller queries) =
      scan (fun edge reached saved captured =>
          visitSelected right
            (consumeSelected
              (fun fragment actual current cache => eraseFold (done fragment actual current cache))
              reached saved)
            scs edge reached captured saved)
        before (edgesOf incoming) caller queries
    rw [scan_erasure]
    apply congrArg (fun visit => scan visit before (edgesOf incoming) caller queries)
    funext edge reached saved captured
    rw [visitSelected_transport left right childTransport]
    apply congrArg (fun consume => visitSelected right consume scs edge reached captured saved)
    funext receipt
    exact consumeSelected_erasure done reached saved receipt
  · simp only [ordinary, ↓reduceIte]
    exact shallowVisit_erasure checkEmpty r n p h k scs incoming caller before queries done stopped

/-- Common preparation commutes with the exact child and hook transports. -/
theorem runWithChild_transport {Typing : Type}
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (left : Visitor Typing) (right : Visitor Unit)
    (transport : ∀ scs incoming current cache memos yes no,
      eraseFold (left scs incoming current cache memos yes no) =
        right scs incoming current cache memos
          (fun fragment reached saved after => eraseFold (yes fragment reached saved after))
          (fun observation candidate => eraseFold (no observation candidate)))
    (hook : Fragment → Caller width → Queries → Cached → HookFor Typing)
    (checkEmpty : Bool) (entryFuel nativeFuel r n p h k uv : Nat)
    (edgesOf : Node → List Edge) (caller : Caller width) (before : Cached) (queries : Queries) :
    let actual := SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild left hook
      checkEmpty entryFuel nativeFuel r n p h k uv edgesOf caller before queries
    (actual.1, actual.2.map eraseFold) =
      SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild right
        (fun fragment reached saved after => eraseResult (hook fragment reached saved after))
        checkEmpty entryFuel nativeFuel r n p h k uv edgesOf caller before queries := by
  unfold SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild
  generalize SourcePruningEnumerationSelectedPreparation.run entryFuel nativeFuel uv caller before = preparation
  rcases preparation with ⟨raw, returned⟩
  dsimp only
  cases returned with
  | none => rfl
  | some result =>
      cases result with
      | failed fault heap => rfl
      | done value heap =>
          cases raw with
          | nil => rfl
          | cons first rest =>
              cases rest with
              | cons _ _ => cases first <;> rfl
              | nil =>
                  cases first with
                  | error fault => rfl
                  | ok pair =>
                      rcases pair with ⟨⟨target, handle, scs, decoded⟩, entered⟩
                      dsimp only
                      by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
                      · simp only [terminal, ↓reduceIte, Option.map_some]
                        apply Prod.ext
                        · rfl
                        · apply congrArg some
                          exact receipt_erasure hook _ _ _
                      · simp only [terminal, ↓reduceIte]
                        cases value with
                        | node entry rows depth free =>
                            simp only [Option.map_some]
                            apply Prod.ext
                            · rfl
                            · apply congrArg some
                              rw [scan_erasure]
                              apply congrArg (fun visit => scan visit
                                (EnumerationExpandableIndex.frame entered before)
                                (edgesOf (.node entry rows depth free))
                                (SourcePruningEnumerationSelectedValueCaller.advance caller heap) queries)
                              funext edge current saved cache
                              exact visitCapturedWith_transport left right transport hook k target scs edge current saved cache
                        | empty | reference _ | union _ _ _ _ | mu _ _ _ _ =>
                            all_goals
                              simp only [Option.map_some]
                              apply Prod.ext
                              · rfl
                              · apply congrArg some
                                exact receipt_erasure hook _ _ _

/-- The actual eager preparation retains its complete physical observation. -/
theorem prepared_erasure {Typing : Type}
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (hook : Fragment → Caller width → Queries → Cached → HookFor Typing)
    (checkEmpty : Bool) (entryFuel nativeFuel r n p h k uv : Nat)
    (edgesOf : Node → List Edge) (caller : Caller width) (before : Cached) (queries : Queries) :
    let actual := SourcePruningEnumerationSharedPreparedChildPolicy.runEager hook
      checkEmpty entryFuel nativeFuel r n p h k uv edgesOf caller before queries
    (actual.1, actual.2.map eraseFold) =
      SourcePruningEnumerationSharedPreparedChildPolicy.runEager
        (fun fragment reached saved after => eraseResult (hook fragment reached saved after))
        checkEmpty entryFuel nativeFuel r n p h k uv edgesOf caller before queries := by
  unfold SourcePruningEnumerationSharedPreparedChildPolicy.runEager
  exact runWithChild_transport
    (eagerChild checkEmpty r n p h k edgesOf) (eagerChild checkEmpty r n p h k edgesOf)
    (fun scs incoming current cache memos yes no =>
      eagerChild_erasure checkEmpty r n p h k edgesOf scs incoming current cache memos yes no)
    hook checkEmpty entryFuel nativeFuel r n p h k uv edgesOf caller before queries

end MicroCFTA.SourcePruningEnumerationIdentityResultMetadataErasure
