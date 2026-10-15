import MicroCFTA.SourceCurrentSecondaryCompletion
import MicroCFTA.EndpointMemoGateSource
import MicroCFTA.EndpointMemoGateClasses
import MicroCFTA.SourceQueryUnfoldMemo

/-!
# Actual memo calls through the current secondary gate

The receipts follow each demanded predicate and unfolding call. Secondary
ordinary endpoints do not call the descendant helper. The new constrained
Mu endpoint still calls the predicate first. False siblings pass the exact
returned tables. Completed receipts do not establish GHC publication.
-/
namespace MicroCFTA.SourceCurrentSecondaryMemos
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open SourceObservations SourceSymbolicIndex EqualityNormalize
open InternedFreshOrdinaryMemoGateTrace (Ready node_ready)
open EndpointMemoGateTrace (Memos Valid Keeps pure_keeps prepend_keeps)

local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "source" => SourceMemoGate.unconstrained

mutual
/-- Exact memo receipts refine a particular completed current-policy node trace. -/
inductive NodeReads [DecidableEq (EdgeKey Symbol Guard)] :
    {path : Path} → {value : Value Symbol Guard} → {state : State Symbol Guard} →
    {answer : Bool} → {final : State Symbol Guard} →
    SourceCurrentSecondaryTrace.NodeTrace source path value state answer final → Memos → Memos → Prop where
  | empty : NodeReads .empty memos memos
  | reference : NodeReads .reference memos memos
  | union (members : List (Value Symbol Guard)) : NodeReads (.union members) memos memos
  | finite {free : List InternedBinderProtocol.Reference} (fast : (depth == 0 && free.isEmpty) = true) :
      NodeReads (.finite fast) memos memos
  | endpoint {free : List InternedBinderProtocol.Reference} (slow : (depth == 0 && free.isEmpty) = false) :
      NodeReads (.endpoint slow) memos memos
  | branches {free : List InternedBinderProtocol.Reference} (slow : (depth == 0 && free.isEmpty) = false)
      (trace : EdgesReads edges memos saved) : NodeReads (.branches slow edges) memos saved
  | constrained (blocked : source (.mu entry body depth ordinary) = false)
      (actual : SourceUnconstrainedMemo.run (.mu entry body depth ordinary) memos.query.predicate =
        (false, savedPredicate)) :
      NodeReads (.constrained blocked) memos {memos with query := {memos.query with predicate := savedPredicate}}
  | closed (plain : source (.mu entry body depth ordinary) = true)
      (closed : (Value.mu entry body depth ordinary).free.isEmpty = true)
      (actual : SourceUnconstrainedMemo.run (.mu entry body depth ordinary) memos.query.predicate =
        (true, savedPredicate)) :
      NodeReads (.closed plain closed) memos {memos with query := {memos.query with predicate := savedPredicate}}
  | unfold (plain : source (.mu entry body depth ordinary) = true)
      (opened : (Value.mu entry body depth ordinary).free.isEmpty = false)
      (actual : InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) state = .done next after)
      (predicate : SourceUnconstrainedMemo.run (.mu entry body depth ordinary) memos.query.predicate =
        (true, middlePredicate))
      (unfolding : InternedFreshOrdinaryUnfoldMemo.run (.mu entry body depth ordinary) memos.unfolding state =
        .done (next, middleUnfolding) after)
      (trace : NodeReads nextTrace ⟨middleUnfolding, {memos.query with predicate := middlePredicate}⟩ saved) :
      NodeReads (.unfold plain opened actual nextTrace) memos saved

/-- A child receipt follows the actual selected physical record and all returned tables. -/
inductive ChildReads [DecidableEq (EdgeKey Symbol Guard)] :
    {values : List (Value Symbol Guard)} → {index : Nat} → {path : Path} → {state : State Symbol Guard} →
    {answer : Bool} → {final : State Symbol Guard} →
    SourceCurrentSecondaryTrace.ChildTrace source values index path state answer final → Memos → Memos → Prop where
  | missing (absent : values[index]? = none) : ChildReads (.missing absent) memos memos
  | present (found : values[index]? = some value) (trace : NodeReads nextTrace memos saved) :
      ChildReads (.present found nextTrace) memos saved

/-- False children pass their exact three tables onward; true children omit the suffix. -/
inductive EdgesReads [DecidableEq (EdgeKey Symbol Guard)] :
    {index : Nat} → {path : Path} → {edges : List (EdgeValue Symbol Guard)} → {state : State Symbol Guard} →
    {answer : Bool} → {final : State Symbol Guard} →
    SourceCurrentSecondaryTrace.EdgesTrace source index path edges state answer final → Memos → Memos → Prop where
  | nil : EdgesReads .nil memos memos
  | stop (head : ChildReads headTrace memos saved) : EdgesReads (.stop headTrace) memos saved
  | next (head : ChildReads headTrace memos middle) (tail : EdgesReads tailTrace middle saved) :
      EdgesReads (.next headTrace tailTrace) memos saved
end


/-- Each completed pure node graph derives all actual memo calls and the returned coherent caches. -/
theorem lift_node [DecidableEq (EdgeKey Symbol Guard)]
    (path : Path) (value : Value Symbol Guard) (state : State Symbol Guard) (answer : Bool) (final : State Symbol Guard)
    (trace : SourceCurrentSecondaryTrace.NodeTrace source path value state answer final)
    (ready : Ready state) (available : Available state value) (memos : Memos) (valid : Valid state memos) :
    ∃ saved, NodeReads trace memos saved ∧ Keeps state final saved := by
  revert valid memos available ready
  induction trace using SourceCurrentSecondaryTrace.NodeTrace.rec
      (motive_2 := fun values index path state answer final trace => Ready state →
        (∀ value ∈ values, Available state value) → ∀ memos, Valid state memos →
          ∃ saved, ChildReads trace memos saved ∧ Keeps state final saved)
      (motive_3 := fun index path edges state answer final trace => Ready state →
        (∀ value ∈ edges.flatMap EdgeValue.children, Available state value) → ∀ memos, Valid state memos →
          ∃ saved, EdgesReads trace memos saved ∧ Keeps state final saved) with
  | empty => intro ready available memos valid; exact ⟨memos, .empty, pure_keeps _ _ ready valid⟩
  | reference => intro ready available memos valid; exact ⟨memos, .reference, pure_keeps _ _ ready valid⟩
  | union members => intro ready available memos valid; exact ⟨memos, .union members, pure_keeps _ _ ready valid⟩
  | finite fast => intro ready available memos valid; exact ⟨memos, .finite fast, pure_keeps _ _ ready valid⟩
  | endpoint slow =>
      intro ready available memos valid
      exact ⟨memos, .endpoint slow, pure_keeps _ _ ready valid⟩
  | branches slow trace ih =>
      intro ready available memos valid
      obtain ⟨saved, actual, kept⟩ := ih ready (fun value member => available.children value member) memos valid
      exact ⟨saved, .branches slow actual, kept⟩
  | constrained blocked =>
      intro ready available memos valid
      have checked := SourceUnconstrainedMemo.run_exact _ _ ready.1.normal.facts.coherent available memos.query.predicate valid.query.predicate
      have actual : SourceUnconstrainedMemo.run _ memos.query.predicate =
          (false, (SourceUnconstrainedMemo.run _ memos.query.predicate).2) := Prod.ext (checked.1.trans blocked) rfl
      exact ⟨_, .constrained blocked actual, pure_keeps _ _ ready ⟨valid.unfolding, valid.query.descendants, checked.2⟩⟩
  | closed plain closed =>
      intro ready available memos valid
      have checked := SourceUnconstrainedMemo.run_exact _ _ ready.1.normal.facts.coherent available memos.query.predicate valid.query.predicate
      have actual : SourceUnconstrainedMemo.run _ memos.query.predicate =
          (true, (SourceUnconstrainedMemo.run _ memos.query.predicate).2) := Prod.ext (checked.1.trans plain) rfl
      exact ⟨_, .closed plain closed actual, pure_keeps _ _ ready ⟨valid.unfolding, valid.query.descendants, checked.2⟩⟩
  | unfold plain opened actual trace ih =>
      intro ready available memos valid
      have checked := SourceUnconstrainedMemo.run_exact _ _ ready.1.normal.facts.coherent available memos.query.predicate valid.query.predicate
      have predicate : SourceUnconstrainedMemo.run _ memos.query.predicate =
          (true, (SourceUnconstrainedMemo.run _ memos.query.predicate).2) := Prod.ext (checked.1.trans plain) rfl
      let middleQuery : SourceEndpointMemo.Memos :=
        {memos.query with predicate :=
          (SourceUnconstrainedMemo.run (ready.node _ available).value memos.query.predicate).2}
      have queryValid : SourceEndpointMemo.Valid _ middleQuery :=
        ⟨valid.query.descendants, checked.2⟩
      obtain ⟨after, afterMemo, memoActual, readback, afterCorrect, growth, history⟩ :=
        InternedFreshOrdinaryUnfoldMemo.run_complete (ready.node _ available) memos.unfolding valid.unfolding
      have fields := Outcome.done.inj (readback.symm.trans actual)
      have valueEqual := fields.1
      have stateEqual := fields.2
      have afterReady := stateEqual ▸ node_ready after
      have afterAvailable := stateEqual ▸ (valueEqual ▸ after.available)
      have memoCorrect := stateEqual ▸ afterCorrect
      have afterQuery := stateEqual ▸ SourceEndpointMemo.grows _ _ growth history _ queryValid
      obtain ⟨saved, next, kept⟩ := ih afterReady afterAvailable ⟨afterMemo, middleQuery⟩ ⟨memoCorrect, afterQuery⟩
      refine ⟨saved, .unfold plain opened actual predicate ?_ next,
        prepend_keeps (firstMemos := ⟨afterMemo, middleQuery⟩) ?_ kept⟩
      · simpa only [Ready.node, valueEqual, stateEqual] using memoActual
      · exact ⟨afterReady, ⟨memoCorrect, afterQuery⟩,
          by simpa only [Ready.node, stateEqual] using growth,
          by simpa only [Ready.node, stateEqual] using history⟩
  | missing absent ready available memos valid =>
      exact ⟨memos, .missing absent, pure_keeps _ _ ready valid⟩
  | present found trace ih ready available memos valid =>
      obtain ⟨saved, actual, kept⟩ := ih ready (available _ (List.mem_of_getElem? found)) memos valid
      exact ⟨saved, .present found actual, kept⟩
  | nil ready available memos valid =>
      exact ⟨memos, .nil, pure_keeps _ _ ready valid⟩
  | stop head ih ready available memos valid =>
      obtain ⟨saved, actual, kept⟩ := ih ready (fun value member => available value (by simp [member])) memos valid
      exact ⟨saved, .stop actual, kept⟩
  | next head tail headIH tailIH ready available memos valid =>
      obtain ⟨middle, first, firstKept⟩ := headIH ready (fun value member => available value (by simp [member])) memos valid
      obtain ⟨saved, rest, restKept⟩ := tailIH firstKept.ready
        (fun value member => (available value (by simp [member])).grows _ _ firstKept.growth firstKept.history)
        middle firstKept.valid
      exact ⟨saved, .next first rest, prepend_keeps firstKept restKept⟩

/-- A completed selected-child trace derives its exact three returned memo tables. -/
theorem lift_child [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) (index : Nat) (path : Path) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard)
    (trace : SourceCurrentSecondaryTrace.ChildTrace source values index path state answer final)
    (ready : Ready state) (available : ∀ value ∈ values, Available state value)
    (memos : Memos) (valid : Valid state memos) :
    ∃ saved, ChildReads trace memos saved ∧ Keeps state final saved := by
  cases trace with
  | missing absent => exact ⟨memos, .missing absent, pure_keeps _ _ ready valid⟩
  | present found trace =>
      obtain ⟨saved, actual, kept⟩ := lift_node _ _ _ _ _ trace ready
        (available _ (List.mem_of_getElem? found)) memos valid
      exact ⟨saved, .present found actual, kept⟩

/-- An ordered edge trace threads all three actual memo tables through false siblings. -/
theorem lift_edges [DecidableEq (EdgeKey Symbol Guard)]
    (index : Nat) (path : Path) (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard)
    (trace : SourceCurrentSecondaryTrace.EdgesTrace source index path edges state answer final)
    (ready : Ready state) (available : ∀ value ∈ edges.flatMap EdgeValue.children, Available state value)
    (memos : Memos) (valid : Valid state memos) :
    ∃ saved, EdgesReads trace memos saved ∧ Keeps state final saved := by
  revert valid memos available ready
  induction trace using SourceCurrentSecondaryTrace.EdgesTrace.rec
      (motive_1 := fun _ _ _ _ _ _ => True)
      (motive_2 := fun _ _ _ _ _ _ _ => True) with
  | empty | reference | union | finite | endpoint | branches | constrained | closed | unfold | missing | present => trivial
  | nil => intro ready available memos valid; exact ⟨memos, .nil, pure_keeps _ _ ready valid⟩
  | stop head _ =>
      intro ready available memos valid
      obtain ⟨saved, actual, kept⟩ := lift_child _ _ _ _ _ _ head ready
        (fun value member => available value (by simp [member])) memos valid
      exact ⟨saved, .stop actual, kept⟩
  | next head tail _ ih =>
      intro ready available memos valid
      obtain ⟨middle, first, firstKept⟩ := lift_child _ _ _ _ _ _ head ready
        (fun value member => available value (by simp [member])) memos valid
      obtain ⟨saved, rest, restKept⟩ := ih firstKept.ready
        (fun value member => (available value (by simp [member])).grows _ _ firstKept.growth firstKept.history)
        middle firstKept.valid
      exact ⟨saved, .next first rest, prepend_keeps firstKept restKept⟩


/-- A secondary path retains all three exact returned memo tables. -/
inductive PathReads [DecidableEq (EdgeKey Symbol Guard)] :
    {values : List (Value Symbol Guard)} → {path : Path} → {state : State Symbol Guard} →
    {answer : Bool} → {final : State Symbol Guard} →
    SourceCurrentSecondaryTrace.PathTrace source values path state answer final → Memos → Memos → Prop where
  | empty : PathReads .empty memos memos
  | child (trace : ChildReads childTrace memos saved) : PathReads (.child childTrace) memos saved

/-- Secondary false paths pass all three tables onward; true paths omit the suffix. -/
inductive ClassReads [DecidableEq (EdgeKey Symbol Guard)] :
    {values : List (Value Symbol Guard)} → {paths : Class} → {state : State Symbol Guard} →
    {answer : Bool} → {final : State Symbol Guard} →
    SourceCurrentSecondaryTrace.ClassTrace source values paths state answer final → Memos → Memos → Prop where
  | nil : ClassReads .nil memos memos
  | stop (head : PathReads headTrace memos saved) : ClassReads (.stop headTrace) memos saved
  | next (head : PathReads headTrace memos middle) (tail : ClassReads tailTrace middle saved) :
      ClassReads (.next headTrace tailTrace) memos saved

/-- Each completed secondary path derives actual coherent calls for all three memo families. -/
theorem lift_path [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) (path : Path) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard)
    (trace : SourceCurrentSecondaryTrace.PathTrace source values path state answer final)
    (ready : Ready state) (available : ∀ value ∈ values, Available state value)
    (memos : Memos) (valid : Valid state memos) :
    ∃ saved, PathReads trace memos saved ∧ Keeps state final saved := by
  cases trace with
  | empty => exact ⟨memos, .empty, pure_keeps _ _ ready valid⟩
  | child trace =>
      obtain ⟨saved, actual, kept⟩ := lift_child _ _ _ _ _ _ trace ready available memos valid
      exact ⟨saved, .child actual, kept⟩

/-- Each completed secondary class derives actual memo calls and ordered constructor effects. -/
theorem lift_class [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) (paths : Class) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard)
    (trace : SourceCurrentSecondaryTrace.ClassTrace source values paths state answer final)
    (ready : Ready state) (available : ∀ value ∈ values, Available state value)
    (memos : Memos) (valid : Valid state memos) :
    ∃ saved, ClassReads trace memos saved ∧ Keeps state final saved := by
  revert valid memos available ready
  induction trace with
  | nil => intro ready available memos valid; exact ⟨memos, .nil, pure_keeps _ _ ready valid⟩
  | stop head =>
      intro ready available memos valid
      obtain ⟨saved, actual, kept⟩ := lift_path _ _ _ _ _ head ready available memos valid
      exact ⟨saved, .stop actual, kept⟩
  | next head tail ih =>
      intro ready available memos valid
      obtain ⟨middle, first, firstKept⟩ := lift_path _ _ _ _ _ head ready available memos valid
      obtain ⟨saved, rest, restKept⟩ := ih firstKept.ready
        (fun value member => (available value member).grows _ _ firstKept.growth firstKept.history)
        middle firstKept.valid
      exact ⟨saved, .next first rest, prepend_keeps firstKept restKept⟩


private def Retains (before after : Memos) : Prop :=
  Extends before.unfolding after.unfolding ∧ after.query.descendants = before.query.descendants ∧
    Extends before.query.predicate after.query.predicate

private theorem retains_refl (memos : Memos) : Retains memos memos :=
  ⟨extends_refl _, rfl, extends_refl _⟩

private theorem retains_trans {before middle after : Memos}
    (first : Retains before middle) (second : Retains middle after) : Retains before after :=
  ⟨extends_trans first.1 second.1, second.2.1.trans first.2.1, extends_trans first.2.2 second.2.2⟩

private theorem predicate_call_extends {input : Value Symbol Guard}
    {before after : SourceUnconstrainedMemo.Memo} {answer : Bool}
    (actual : SourceUnconstrainedMemo.run input before = (answer, after)) : Extends before after := by
  simpa only [actual] using SourceEndpointMemo.predicate_extends input before

/-- Actual node calls retain earlier entries and do not change the descendant table. -/
theorem node_tables [DecidableEq (EdgeKey Symbol Guard)]
    {path : Path} {value : Value Symbol Guard} {before after : State Symbol Guard} {answer : Bool}
    {trace : SourceCurrentSecondaryTrace.NodeTrace source path value before answer after}
    {memos saved : Memos} (reads : NodeReads trace memos saved) :
    Extends memos.unfolding saved.unfolding ∧ saved.query.descendants = memos.query.descendants ∧
      Extends memos.query.predicate saved.query.predicate := by
  change Retains memos saved
  induction reads using NodeReads.rec
      (motive_2 := fun {_values _index _path _state _answer _final} _ before after _ => Retains before after)
      (motive_3 := fun {_values _index _path _state _answer _final} _ before after _ => Retains before after) with
  | empty | reference | union | finite | endpoint => exact retains_refl _
  | branches _ _ ih => exact ih
  | constrained blocked actual =>
      refine ⟨extends_refl _, rfl, ?_⟩
      exact predicate_call_extends actual
  | closed plain closed actual =>
      refine ⟨extends_refl _, rfl, ?_⟩
      exact predicate_call_extends actual
  | unfold plain opened actual predicate unfolding trace ih =>
      apply retains_trans (middle := _) ?_ ih
      refine ⟨SourceQueryUnfoldMemo.run_extends _ _ _ _ _ _ unfolding, rfl, ?_⟩
      exact predicate_call_extends predicate
  | missing => exact retains_refl _
  | present _ _ ih => exact ih
  | nil => exact retains_refl _
  | stop _ ih => exact ih
  | next _ _ headIH tailIH => exact retains_trans headIH tailIH

/-- A selected child retains both memo histories and the exact descendant table. -/
theorem child_tables [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {index : Nat} {path : Path} {before after : State Symbol Guard} {answer : Bool}
    {trace : SourceCurrentSecondaryTrace.ChildTrace source values index path before answer after}
    {memos saved : Memos} (reads : ChildReads trace memos saved) :
    Extends memos.unfolding saved.unfolding ∧ saved.query.descendants = memos.query.descendants ∧
      Extends memos.query.predicate saved.query.predicate := by
  cases reads with
  | missing => exact retains_refl _
  | present _ called => exact node_tables called

/-- Ordered edge calls preserve entries across the exact visited prefix. -/
theorem edges_tables [DecidableEq (EdgeKey Symbol Guard)]
    {index : Nat} {path : Path} {edges : List (EdgeValue Symbol Guard)}
    {before after : State Symbol Guard} {answer : Bool}
    {trace : SourceCurrentSecondaryTrace.EdgesTrace source index path edges before answer after}
    {memos saved : Memos} (reads : EdgesReads trace memos saved) :
    Extends memos.unfolding saved.unfolding ∧ saved.query.descendants = memos.query.descendants ∧
      Extends memos.query.predicate saved.query.predicate := by
  change Retains memos saved
  induction reads using EdgesReads.rec
      (motive_1 := fun {_path _value _state _answer _final} _ _ _ _ => True)
      (motive_2 := fun {_values _index _path _state _answer _final} _ _ _ _ => True) with
  | empty | reference | union | finite | endpoint | branches | constrained | closed | unfold | missing | present => trivial
  | nil => exact retains_refl _
  | stop head _ => exact child_tables head
  | next head tail _ ih => exact retains_trans (child_tables head) ih

/-- A path retains earlier memo entries and does not call the descendant helper. -/
theorem path_tables [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {path : Path} {before after : State Symbol Guard} {answer : Bool}
    {trace : SourceCurrentSecondaryTrace.PathTrace source values path before answer after}
    {memos saved : Memos} (reads : PathReads trace memos saved) :
    Extends memos.unfolding saved.unfolding ∧ saved.query.descendants = memos.query.descendants ∧
      Extends memos.query.predicate saved.query.predicate := by
  cases reads with
  | empty => exact retains_refl _
  | child called => exact child_tables called

/-- Every demanded class prefix retains completed entries in all three tables. -/
theorem class_tables [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {paths : Class} {before after : State Symbol Guard} {answer : Bool}
    {trace : SourceCurrentSecondaryTrace.ClassTrace source values paths before answer after}
    {memos saved : Memos} (reads : ClassReads trace memos saved) :
    Extends memos.unfolding saved.unfolding ∧ saved.query.descendants = memos.query.descendants ∧
      Extends memos.query.predicate saved.query.predicate := by
  change Retains memos saved
  induction reads with
  | nil => exact retains_refl _
  | stop head => exact path_tables head
  | next head tail ih => exact retains_trans (path_tables head) ih

/-- An actual completed current secondary class derives calls, validity, and retained entries. -/
theorem completed_class [DecidableEq (EdgeKey Symbol Guard)]
    (reaches : Value Symbol Guard → Bool) (fuel : Nat) (values : List (Value Symbol Guard))
    (paths : Class) (before : State Symbol Guard) (answer : Bool) (after : State Symbol Guard)
    (actual : SourceCurrentMuEndpoint.classMeets false source reaches fuel values paths before = .done (some answer) after)
    (ready : Ready before) (available : ∀ value ∈ values, Available before value)
    (memos : Memos) (valid : Valid before memos) :
    ∃ trace : SourceCurrentSecondaryTrace.ClassTrace source values paths before answer after,
      ∃ saved, ClassReads trace memos saved ∧ Keeps before after saved ∧
        Extends memos.unfolding saved.unfolding ∧ saved.query.descendants = memos.query.descendants ∧
          Extends memos.query.predicate saved.query.predicate := by
  let trace := SourceCurrentSecondaryTrace.actual_current_class_trace_of_done source reaches fuel values paths before answer after actual
  obtain ⟨saved, reads, kept⟩ := lift_class _ _ _ _ _ trace ready available memos valid
  exact ⟨trace, saved, reads, kept, class_tables reads⟩


/-- Certified original inputs derive stable finite class execution and all actual memo receipts. -/
theorem complete_class [DecidableEq (EdgeKey Symbol Guard)]
    (reaches : Value Symbol Guard → Bool) (node : InternedFreshOrdinaryGateRank.Node Symbol Guard)
    (values : List (Value Symbol Guard)) (available : ∀ value ∈ values, Available node.state value)
    (paths : Class) (memos : Memos) (valid : Valid node.state memos) :
    ∃ bound answer, ∃ after : InternedFreshOrdinaryGateRank.Node Symbol Guard,
      ∃ trace : SourceCurrentSecondaryTrace.ClassTrace source values paths node.state answer after.state,
        ∃ saved, ClassReads trace memos saved ∧ Keeps node.state after.state saved ∧
          Extends memos.unfolding saved.unfolding ∧ saved.query.descendants = memos.query.descendants ∧
          Extends memos.query.predicate saved.query.predicate ∧
          ∀ extra, SourceCurrentMuEndpoint.classMeets false source reaches (bound + extra) values paths node.state =
            .done (some answer) after.state := by
  obtain ⟨bound, answer, after, _, _, stable⟩ :=
    SourceCurrentSecondaryCompletion.class_eventually_exact source node values available paths
  have actual : SourceCurrentMuEndpoint.classMeets false source reaches bound values paths node.state =
      .done (some answer) after.state := by
    rw [SourceCurrentSecondaryTrace.actual_current_class_eq]
    simpa only [Nat.add_zero] using stable 0
  obtain ⟨trace, saved, reads, kept, unfolding, descendants, predicate⟩ :=
    completed_class reaches bound values paths node.state answer after.state actual (node_ready node) available memos valid
  refine ⟨bound, answer, after, trace, saved, reads, kept, unfolding, descendants, predicate, ?_⟩
  intro extra
  rw [SourceCurrentSecondaryTrace.actual_current_class_eq]
  exact stable extra

/-- Actual closed construction derives node checks and initially empty memo receipts without heap premises. -/
theorem source_nodes [DecidableEq (EdgeKey Symbol Guard)]
    (expression : InternedNestedConstruction.Syntax Symbol Guard) (reaches : Value Symbol Guard → Bool) :
    ∃ value heap, ∃ _done : InternedFreshOrdinaryConstruction.build expression [] InternedConstructorTemplates.empty = .done value heap,
      ∀ path, ∃ bound answer, ∃ after : InternedFreshOrdinaryGateRank.Node Symbol Guard,
        ∃ trace : SourceCurrentSecondaryTrace.NodeTrace source path value heap answer after.state,
          ∃ saved, NodeReads trace EndpointMemoGateTrace.empty saved ∧ Keeps heap after.state saved ∧
            saved.query.descendants = EndpointMemoGateTrace.empty.query.descendants ∧
            ∀ extra, SourceCurrentMuEndpoint.nodeMeets false source reaches (bound + extra) path value heap =
              .done (some answer) after.state := by
  obtain ⟨value, heap, done, paths⟩ := SourceCurrentSecondaryCompletion.source_node_trace expression source
  refine ⟨value, heap, done, ?_⟩
  intro path
  obtain ⟨bound, answer, after, trace, _, _, stable⟩ := paths path
  let original := InternedFreshOrdinaryGateRank.fromCompleted expression value heap done
  obtain ⟨saved, reads, kept⟩ := lift_node path value heap answer after.state trace
    (node_ready original) original.available EndpointMemoGateTrace.empty (EndpointMemoGateTrace.empty_valid heap)
  refine ⟨bound, answer, after, trace, saved, reads, kept, (node_tables reads).2.1, ?_⟩
  intro extra
  rw [SourceCurrentSecondaryTrace.actual_current_node_eq]
  exact stable extra

end MicroCFTA.SourceCurrentSecondaryMemos
