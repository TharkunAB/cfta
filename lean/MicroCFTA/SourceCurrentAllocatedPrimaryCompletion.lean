import MicroCFTA.SourceCurrentAllocatedGateReadValidity

/-!
# Actual current primary execution derives anchored memo reads

The completed source gate constructs receipts whose closed descendant
query uses its actual input node. The older unanchored receipt is retained
only by explicit erasure. No final validity premise is required.
-/
namespace MicroCFTA.SourceCurrentAllocatedPrimaryReads
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open SourceObservations SourceSymbolicIndex EqualityNormalize
open InternedFreshOrdinaryMemoGateTrace (Ready node_ready)
open EndpointMemoGateTrace (Memos Valid Keeps pure_keeps prepend_keeps)
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source

/-- An open endpoint skips the helper; a closed endpoint retains its actual paired memo result. -/
private theorem endpoint_lift [DecidableEq (EdgeKey Symbol Guard)]
    {free : List InternedBinderProtocol.Reference} (slow : (depth == 0 && free.isEmpty) = false)
    (state : State Symbol Guard) (ready : Ready state)
    (available : Available state (.node entry edges depth free)) (memos : Memos) (valid : Valid state memos) :
    ∃ saved, NodeReads (EndpointStatefulGateTrace.NodeTrace.endpoint slow :
      EndpointStatefulGateTrace.NodeTrace source reaches [] (.node entry edges depth free) state
        (!free.isEmpty || reaches (.node entry edges depth free)) state) memos saved ∧
      Keeps state state saved := by
  by_cases closed : free.isEmpty = true
  · have checked := SourceEndpointMemoCorrect.run_checked _ _ ready.1.normal.facts.coherent available memos.query valid.query
    have actual : SourceEndpointMemo.run _ memos.query =
        (reaches (.node entry edges depth free), (SourceEndpointMemo.run _ memos.query).2) :=
      Prod.ext checked.answer rfl
    exact ⟨_, .endpoint_closed slow closed actual,
      pure_keeps _ _ ready ⟨valid.unfolding, checked.valid⟩⟩
  · exact ⟨memos, .endpoint_open slow (Bool.eq_false_iff.mpr closed), pure_keeps _ _ ready valid⟩

/-- Each completed pure node graph derives all actual memo calls and the returned coherent caches. -/
theorem lift_node [DecidableEq (EdgeKey Symbol Guard)]
    (path : Path) (value : Value Symbol Guard) (state : State Symbol Guard) (answer : Bool) (final : State Symbol Guard)
    (trace : EndpointStatefulGateTrace.NodeTrace source reaches path value state answer final)
    (ready : Ready state) (available : Available state value) (memos : Memos) (valid : Valid state memos) :
    ∃ saved, NodeReads trace memos saved ∧ Keeps state final saved := by
  revert valid memos available ready
  induction trace using EndpointStatefulGateTrace.NodeTrace.rec
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
      exact endpoint_lift slow _ ready available memos valid
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
    (trace : EndpointStatefulGateTrace.ChildTrace source reaches values index path state answer final)
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
    (trace : EndpointStatefulGateTrace.EdgesTrace source reaches index path edges state answer final)
    (ready : Ready state) (available : ∀ value ∈ edges.flatMap EdgeValue.children, Available state value)
    (memos : Memos) (valid : Valid state memos) :
    ∃ saved, EdgesReads trace memos saved ∧ Keeps state final saved := by
  revert valid memos available ready
  induction trace using EndpointStatefulGateTrace.EdgesTrace.rec
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

/-- Each completed primary path derives actual coherent calls for all three memo families. -/
theorem lift_path [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) (path : Path) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard)
    (trace : EndpointStatefulGateTrace.PathTrace source reaches values path state answer final)
    (ready : Ready state) (available : ∀ value ∈ values, Available state value)
    (memos : Memos) (valid : Valid state memos) :
    ∃ saved, PathReads trace memos saved ∧ Keeps state final saved := by
  cases trace with
  | empty => exact ⟨memos, .empty, pure_keeps _ _ ready valid⟩
  | child trace =>
      obtain ⟨saved, actual, kept⟩ := lift_child _ _ _ _ _ _ trace ready available memos valid
      exact ⟨saved, .child actual, kept⟩

/-- Each completed primary class derives actual memo calls and ordered constructor effects. -/
theorem lift_class [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) (paths : Class) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard)
    (trace : EndpointStatefulGateTrace.ClassTrace source reaches values paths state answer final)
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

/-- An actual completed primary worker derives its exact graph and all three returned memo families. -/
theorem completed_class [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (values : List (Value Symbol Guard)) (paths : Class) (state : State Symbol Guard)
    (answer : Bool) (final : State Symbol Guard)
    (actual : EndpointStatefulGate.classMeets source reaches fuel values paths state = .done (some answer) final)
    (ready : Ready state) (available : ∀ value ∈ values, Available state value)
    (memos : Memos) (valid : Valid state memos) :
    ∃ trace : EndpointStatefulGateTrace.ClassTrace source reaches values paths state answer final,
      ∃ saved, ClassReads trace memos saved ∧ Keeps state final saved := by
  let trace := EndpointStatefulGateTrace.class_trace_of_done source reaches fuel values paths state answer final actual
  obtain ⟨saved, reads, kept⟩ := lift_class _ _ _ _ _ trace ready available memos valid
  exact ⟨trace, saved, reads, kept⟩

/-- Current certified inputs derive finite stable primary class execution with all three actual memo receipts. -/
theorem complete_class [DecidableEq (EdgeKey Symbol Guard)]
    (node : InternedFreshOrdinaryGateRank.Node Symbol Guard) (values : List (Value Symbol Guard))
    (available : ∀ value ∈ values, Available node.state value) (paths : Class)
    (memos : Memos) (valid : Valid node.state memos) :
    ∃ bound answer, ∃ after : InternedFreshOrdinaryGateRank.Node Symbol Guard,
      ∃ trace : EndpointStatefulGateTrace.ClassTrace source reaches values paths node.state answer after.state,
        ∃ saved, ClassReads trace memos saved ∧ Keeps node.state after.state saved ∧
          ∀ extra, EndpointStatefulGate.classMeets source reaches (bound + extra) values paths node.state =
            .done (some answer) after.state := by
  obtain ⟨bound, answer, after, _, _, stable⟩ :=
    EndpointStatefulGateCompletion.class_eventually_exact source reaches node values available paths
  have done := stable 0
  rw [Nat.add_zero] at done
  obtain ⟨trace, saved, reads, kept⟩ := completed_class bound values paths node.state answer after.state
    done (node_ready node) available memos valid
  exact ⟨bound, answer, after, trace, saved, reads, kept, stable⟩

end MicroCFTA.SourceCurrentAllocatedPrimaryReads
