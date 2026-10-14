import MicroCFTA.InternedFreshOrdinaryMemoGateLift

/-!
# Complete equality-class graphs with shared unfolding memos

Each path receives both caches returned by the preceding false path.
The memo graph has exact source readback. Source construction derives
complete memo execution without a supplied successful gate call.
-/
namespace MicroCFTA.InternedFreshOrdinaryMemoGateTrace
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Outcome Syntax)
open InternedFreshOrdinaryGateRank (Node fromCompleted)
open InternedFreshOrdinaryUnfoldMemo (Memo Correct)
open EqualityNormalize

/-- A memo path graph starts below the constrained edge's root. -/
inductive PathTrace [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) :
    Path → Memo Symbol Guard → State Symbol Guard → Bool → Memo Symbol Guard → State Symbol Guard → Prop where
  | empty : PathTrace unconstrained values [] memo state false memo state
  | child (trace : ChildTrace unconstrained values index rest memo state answer saved final) :
      PathTrace unconstrained values (index :: rest) memo state answer saved final

/-- Ordered class paths share both returned caches and stop at their first true result. -/
inductive ClassTrace [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) :
    Class → Memo Symbol Guard → State Symbol Guard → Bool → Memo Symbol Guard → State Symbol Guard → Prop where
  | nil : ClassTrace unconstrained values [] memo state false memo state
  | stop (head : PathTrace unconstrained values path memo state true saved final) :
      ClassTrace unconstrained values (path :: rest) memo state true saved final
  | next (head : PathTrace unconstrained values path memo state false middleMemo middle)
      (tail : ClassTrace unconstrained values rest middleMemo middle answer saved final) :
      ClassTrace unconstrained values (path :: rest) memo state answer saved final

/-- Memo path execution recovers the same source path graph and constructor cache. -/
theorem erase_path [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) (path : Path) (memo : Memo Symbol Guard) (state : State Symbol Guard)
    (answer : Bool) (saved : Memo Symbol Guard) (final : State Symbol Guard)
    (trace : PathTrace unconstrained values path memo state answer saved final) :
    InternedFreshOrdinaryStatefulGateTrace.PathTrace unconstrained values path state answer final := by
  cases trace with
  | empty => exact .empty
  | child trace =>
      cases trace with
      | missing absent => exact .child (.missing absent)
      | present found trace => exact .child (.present found (erase_node _ _ _ _ _ _ _ _ trace))

/-- Memo class execution recovers the same complete source class graph. -/
theorem erase_class [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) (paths : Class) (memo : Memo Symbol Guard) (state : State Symbol Guard)
    (answer : Bool) (saved : Memo Symbol Guard) (final : State Symbol Guard)
    (trace : ClassTrace unconstrained values paths memo state answer saved final) :
    InternedFreshOrdinaryStatefulGateTrace.ClassTrace unconstrained values paths state answer final := by
  induction trace with
  | nil => exact .nil
  | stop head => exact .stop (erase_path _ _ _ _ _ _ _ _ head)
  | next head tail ih => exact .next (erase_path _ _ _ _ _ _ _ _ head) ih

/-- Every complete source path graph lifts to actual coherent memo calls and returned caches. -/
theorem lift_path [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) (path : Path) (state : State Symbol Guard) (answer : Bool) (final : State Symbol Guard)
    (trace : InternedFreshOrdinaryStatefulGateTrace.PathTrace unconstrained values path state answer final)
    (ready : Ready state) (available : ∀ value ∈ values, Available state value)
    (memo : Memo Symbol Guard) (correct : Correct state memo) :
    ∃ saved, PathTrace unconstrained values path memo state answer saved final ∧ Keeps state final saved := by
  cases trace with
  | empty => exact ⟨memo, .empty, pure_keeps _ memo ready correct⟩
  | child trace =>
      cases trace with
      | missing absent => exact ⟨memo, .child (.missing absent), pure_keeps _ memo ready correct⟩
      | present found trace =>
          obtain ⟨saved, actual, kept⟩ := lift_node _ _ _ _ _ _ trace ready
            (available _ (List.mem_of_getElem? found)) memo correct
          exact ⟨saved, .child (.present found actual), kept⟩

/-- Every complete source class graph composes actual coherent unfolding memos through its ordered paths. -/
theorem lift_class [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) (paths : Class) (state : State Symbol Guard) (answer : Bool) (final : State Symbol Guard)
    (trace : InternedFreshOrdinaryStatefulGateTrace.ClassTrace unconstrained values paths state answer final)
    (ready : Ready state) (available : ∀ value ∈ values, Available state value)
    (memo : Memo Symbol Guard) (correct : Correct state memo) :
    ∃ saved, ClassTrace unconstrained values paths memo state answer saved final ∧ Keeps state final saved := by
  revert correct memo available ready
  induction trace with
  | nil => intro ready available memo correct; exact ⟨memo, .nil, pure_keeps _ memo ready correct⟩
  | stop head =>
      intro ready available memo correct
      obtain ⟨saved, actual, kept⟩ := lift_path _ _ _ _ _ _ head ready available memo correct
      exact ⟨saved, .stop actual, kept⟩
  | next head tail ih =>
      intro ready available memo correct
      obtain ⟨middleMemo, first, firstKept⟩ := lift_path _ _ _ _ _ _ head ready available memo correct
      obtain ⟨saved, rest, restKept⟩ := ih firstKept.ready
        (fun value member => (available value member).grows _ _ firstKept.growth firstKept.history) middleMemo firstKept.correct
      exact ⟨saved, .next first rest, prepend_keeps firstKept restKept⟩

/-- Every ready source node has a complete memo graph with the exact finite source result. -/
theorem complete_node [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (node : Node Symbol Guard) (path : Path) (memo : Memo Symbol Guard) (correct : Correct node.state memo) :
    ∃ bound answer, ∃ after : Node Symbol Guard, ∃ saved,
      NodeTrace unconstrained path node.value memo node.state answer saved after.state ∧ Keeps node.state after.state saved ∧
      ∀ extra, InternedFreshOrdinaryStatefulGate.nodeMeets unconstrained (bound + extra) path node.value node.state =
        .done (some answer) after.state := by
  obtain ⟨fuel, answer, after, _, _, stable⟩ :=
    InternedFreshOrdinaryStatefulGateCompletion.node_eventually_exact unconstrained path node
  have done := stable 0
  rw [Nat.add_zero] at done
  have source := InternedFreshOrdinaryStatefulGateTrace.node_trace_of_done unconstrained fuel path node.value node.state answer after.state done
  obtain ⟨saved, actual, kept⟩ := lift_node _ _ _ _ _ _ source (node_ready node) node.available memo correct
  exact ⟨fuel, answer, after, saved, actual, kept, stable⟩

/-- Every ready equality class has a complete coherent memo graph with exact source result and cache. -/
theorem complete_class [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (node : Node Symbol Guard) (values : List (Value Symbol Guard))
    (available : ∀ value ∈ values, Available node.state value) (paths : Class)
    (memo : Memo Symbol Guard) (correct : Correct node.state memo) :
    ∃ bound answer, ∃ after : Node Symbol Guard, ∃ saved,
      ClassTrace unconstrained values paths memo node.state answer saved after.state ∧ Keeps node.state after.state saved ∧
      ∀ extra, InternedFreshOrdinaryStatefulGate.classMeets unconstrained (bound + extra) values paths node.state =
        .done (some answer) after.state := by
  obtain ⟨fuel, answer, after, source, _, _, stable⟩ :=
    InternedFreshOrdinaryStatefulGateTrace.cached_class_trace unconstrained node values available paths
  obtain ⟨saved, actual, kept⟩ := lift_class _ _ _ _ _ _ source (node_ready node) available memo correct
  exact ⟨fuel, answer, after, saved, actual, kept, stable⟩

/-- Original source construction derives complete memo node traces from the empty unfolding memo. -/
theorem source_nodes [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (unconstrained : Value Symbol Guard → Bool) :
    ∃ value state, ∃ _done : InternedFreshOrdinaryConstruction.build expression [] InternedConstructorTemplates.empty = .done value state,
      ∀ path, ∃ bound answer, ∃ after : Node Symbol Guard, ∃ saved,
        NodeTrace unconstrained path value InternedFreshOrdinaryUnfoldMemo.empty state answer saved after.state ∧
        Keeps state after.state saved ∧
        ∀ extra, InternedFreshOrdinaryStatefulGate.nodeMeets unconstrained (bound + extra) path value state =
          .done (some answer) after.state := by
  obtain ⟨value, state, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  exact ⟨value, state, done, fun path => complete_node unconstrained (fromCompleted expression value state done) path
    InternedFreshOrdinaryUnfoldMemo.empty (InternedFreshOrdinaryUnfoldMemo.empty_correct state)⟩

/-- Original outgoing source edges have complete equality-class memo traces with no supplied cache premises. -/
theorem source_classes [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (unconstrained : Value Symbol Guard → Bool) :
    ∃ value state, ∃ _done : InternedFreshOrdinaryConstruction.build expression [] InternedConstructorTemplates.empty = .done value state,
      ∀ entry edges depth free, value = .node entry edges depth free → ∀ edge ∈ edges, ∀ paths,
        ∃ bound answer, ∃ after : Node Symbol Guard, ∃ saved,
          ClassTrace unconstrained edge.children paths InternedFreshOrdinaryUnfoldMemo.empty state answer saved after.state ∧
          Keeps state after.state saved ∧
          ∀ extra, InternedFreshOrdinaryStatefulGate.classMeets unconstrained (bound + extra) edge.children paths state =
            .done (some answer) after.state := by
  obtain ⟨value, state, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  refine ⟨value, state, done, ?_⟩
  intro entry edges depth free original edge member paths
  let node := fromCompleted expression value state done
  apply complete_class unconstrained node edge.children ?_ paths InternedFreshOrdinaryUnfoldMemo.empty
    (InternedFreshOrdinaryUnfoldMemo.empty_correct state)
  intro child selected
  apply node.available.children child
  change child ∈ InternedProbeProvenance.children value
  rw [original]
  exact List.mem_flatMap.mpr ⟨edge, member, selected⟩

/-- Coherent unfolding memo composition is equivalent to the complete source class graph. -/
theorem class_trace_iff [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) (paths : Class) (state : State Symbol Guard) (answer : Bool) (final : State Symbol Guard)
    (ready : Ready state) (available : ∀ value ∈ values, Available state value)
    (memo : Memo Symbol Guard) (correct : Correct state memo) :
    InternedFreshOrdinaryStatefulGateTrace.ClassTrace unconstrained values paths state answer final ↔
      ∃ saved, ClassTrace unconstrained values paths memo state answer saved final ∧ Keeps state final saved := by
  constructor
  · exact fun trace => lift_class _ _ _ _ _ _ trace ready available memo correct
  · rintro ⟨saved, trace, _⟩
    exact erase_class _ _ _ _ _ _ _ _ trace

/-- Saved unfolding memos cannot change a certified class decision or final constructor cache. -/
theorem memo_independent [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) (paths : Class) (state : State Symbol Guard)
    (firstMemo secondMemo firstSaved secondSaved : Memo Symbol Guard)
    (first second : Bool) (firstState secondState : State Symbol Guard)
    (left : ClassTrace unconstrained values paths firstMemo state first firstSaved firstState)
    (right : ClassTrace unconstrained values paths secondMemo state second secondSaved secondState) :
    first = second ∧ firstState = secondState :=
  InternedFreshOrdinaryStatefulGateTrace.class_trace_unique _ _ _ _ _ _ _ _
    (erase_class _ _ _ _ _ _ _ _ left) (erase_class _ _ _ _ _ _ _ _ right)

end MicroCFTA.InternedFreshOrdinaryMemoGateTrace
