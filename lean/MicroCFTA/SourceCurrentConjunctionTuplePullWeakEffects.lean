import MicroCFTA.SourceCurrentConjunctionTuplePullClosedSample
import MicroCFTA.MergedFreshOrdinaryColdEffects

set_option autoImplicit false

/-!
# Weak physical effects of demanded tuple sampling

Only an actual demanded singleton exposure changes the heap. Semantic heap
facts and closed available operands supply its effects. Every returned
fault retains the exact reached heap. Successful samples contain resident
rows with closed children. No equality or cost invariant is a premise.
-/
namespace MicroCFTA.SourceCurrentConjunctionTuplePullWeakEffects
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceCurrentConjunctionRowsWorker (Physical Outcome)
open SourceCurrentConjunctionTuplePull (Cursor Event step expose start)
open SourceCurrentConjunctionTuplePullEffects (Inputs)
open SourceCurrentConjunctionTuplePullClosed (ClosedOperands ClosedRows)
open SourceCurrentConjunctionTuplePullDriveEffects (Collected StatusInputs)
open SourceCurrentConjunctionTuplePullClosedSample (ClosedCollected StatusClosed ResultClosed)
open SourceCurrentConjunctionTuplePullAdmission (Status advance drive)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard

private structure HeapEffects (before after : Physical Symbol Formula) : Prop where
  semantic : SemanticHeap after.heap
  covered : Covered [] after.heap
  growth : Grows before.heap after.heap
  history : Extends before.heap.nodes.issued after.heap.nodes.issued

private theorem HeapEffects.refl (before : Physical Symbol Formula)
    (semantic : SemanticHeap before.heap) (covered : Covered [] before.heap) : HeapEffects before before :=
  ⟨semantic, covered, grows_refl _, extends_refl _⟩

private theorem HeapEffects.trans {before middle after : Physical Symbol Formula}
    (first : HeapEffects before middle) (later : HeapEffects middle after) : HeapEffects before after :=
  ⟨later.semantic, later.covered, grows_trans first.growth later.growth,
    extends_trans first.history later.history⟩

private theorem edges_grows {before after : State Symbol Guard} (growth : Grows before after)
    {rows : List Edge} (resident : Edges before rows) : Edges after rows :=
  fun edge member => InternedEdgeResidency.edge_grows before after growth edge (resident edge member)

private theorem inputs_grows {before after : State Symbol Guard} (cursor : Cursor Symbol Formula)
    (growth : Grows before after) (history : Extends before.nodes.issued after.nodes.issued)
    (inputs : Inputs before cursor) : Inputs after cursor := by
  revert inputs
  induction cursor with
  | empty => intro _; trivial
  | seed node => intro available; exact available.grows _ _ growth history
  | seedRows rows => intro resident; exact edges_grows growth resident
  | extend node inner ih =>
      intro inputs
      exact ⟨inputs.1.grows _ _ growth history, ih inputs.2⟩
  | readOperand node inner tuple ih =>
      intro inputs
      exact ⟨inputs.1.grows _ _ growth history, ih inputs.2.1, edges_grows growth inputs.2.2⟩
  | scanOperand node inner tuple remaining ih =>
      intro inputs
      exact ⟨inputs.1.grows _ _ growth history, ih inputs.2.1,
        edges_grows growth inputs.2.2.1, edges_grows growth inputs.2.2.2⟩

private def CursorInputs (heap : State Symbol Guard) (cursor : Cursor Symbol Formula) : Prop :=
  Inputs heap cursor ∧ ClosedOperands cursor ∧ ClosedRows cursor

private def GoodEvent (heap : State Symbol Guard) : Event Symbol Formula → Prop
  | .more next => CursorInputs heap next
  | .yield tuple next => Edges heap tuple ∧ ClosedEdges tuple ∧ CursorInputs heap next
  | .ended => True

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

omit [DecidableEq Symbol] in
private theorem expose_effects (h : Nat) (node : Node) (before : Physical Symbol Formula)
    (semantic : SemanticHeap before.heap) (covered : Covered [] before.heap)
    (available : Available before.heap node) (closed : node.free = []) :
    HeapEffects before (expose h node before).state ∧
      ∀ rows after, expose h node before = .done rows after → Edges after.heap rows ∧ ClosedEdges rows := by
  have first := MergedFreshOrdinaryColdEffects.nodeEdges_verified h node before.heap semantic covered available closed
  cases read : MergedFreshOrdinaryExposure.nodeEdges h node before.heap with
  | done rows heap =>
      rw [read] at first
      simp only [expose, SourceCurrentConjunctionRowsWorker.exposures, read, Outcome.bind,
        List.headD_cons, Outcome.state]
      exact ⟨⟨first.semantic, first.covered, first.growth, first.history⟩,
        by intro result after same; cases same; exact ⟨first.edges _ _ rfl, first.closed _ _ rfl⟩⟩
  | pending key heap | unresolved key heap =>
      rw [read] at first
      exact False.elim first.outcome
  | exhausted heap =>
      rw [read] at first
      simp only [expose, SourceCurrentConjunctionRowsWorker.exposures, read, Outcome.bind, Outcome.state]
      exact ⟨⟨first.semantic, first.covered, first.growth, first.history⟩,
        by intro rows after same; cases same⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))] in
private theorem pure_effects (before : Physical Symbol Formula)
    (semantic : SemanticHeap before.heap) (covered : Covered [] before.heap)
    (event : Event Symbol Formula) (good : GoodEvent before.heap event) :
    HeapEffects before (Outcome.done event before).state ∧
      ∀ result after, Outcome.done event before = .done result after → GoodEvent after.heap result :=
  ⟨HeapEffects.refl before semantic covered, by intro result after same; cases same; exact good⟩

private theorem step_effects (h : Nat) (cursor : Cursor Symbol Formula) (before : Physical Symbol Formula)
    (semantic : SemanticHeap before.heap) (covered : Covered [] before.heap)
    (inputs : CursorInputs before.heap cursor) :
    HeapEffects before (step h cursor before).state ∧
      ∀ event after, step h cursor before = .done event after → GoodEvent after.heap event := by
  induction cursor generalizing before with
  | empty => exact pure_effects before semantic covered .ended trivial
  | seed node =>
      have first := expose_effects h node before semantic covered inputs.1 inputs.2.1
      cases read : expose h node before with
      | failed fault after =>
          simp only [step, read, Outcome.bind, Outcome.state]
          exact ⟨by simpa only [read, Outcome.state] using first.1,
            by intro event final same; cases same⟩
      | done rows after =>
          have kept : HeapEffects before after := by simpa only [read, Outcome.state] using first.1
          have returned := first.2 rows after read
          simp only [step, read, Outcome.bind, Outcome.state]
          exact ⟨kept, by intro event final same; cases same; exact ⟨returned.1, trivial, returned.2⟩⟩
  | seedRows rows =>
      cases rows with
      | nil => exact pure_effects before semantic covered .ended trivial
      | cons edge rest =>
          refine pure_effects before semantic covered (.yield [edge] (.seedRows rest)) ?_
          refine ⟨?_, ?_, ?_, trivial, ?_⟩
          · intro selected member
            simpa only [List.mem_singleton.mp member] using inputs.1 edge List.mem_cons_self
          · intro selected member
            simpa only [List.mem_singleton.mp member] using inputs.2.2 edge List.mem_cons_self
          · exact fun selected member => inputs.1 selected (List.mem_cons_of_mem _ member)
          · exact fun selected member => inputs.2.2 selected (List.mem_cons_of_mem _ member)
  | extend node inner ih =>
      have first := ih before semantic covered ⟨inputs.1.2, inputs.2.1.2, inputs.2.2⟩
      cases observed : step h inner before with
      | failed fault after =>
          simp only [step, observed, Outcome.bind, Outcome.state]
          exact ⟨by simpa only [observed, Outcome.state] using first.1,
            by intro event final same; cases same⟩
      | done event after =>
          have kept : HeapEffects before after := by simpa only [observed, Outcome.state] using first.1
          have continued := first.2 event after observed
          have available := inputs.1.1.grows before.heap after.heap kept.growth kept.history
          cases event with
          | more next =>
              simp only [step, observed, Outcome.bind, Outcome.state]
              refine ⟨kept, ?_⟩
              intro event final same
              cases same
              exact ⟨⟨available, continued.1⟩, ⟨inputs.2.1.1, continued.2.1⟩, continued.2.2⟩
          | yield tuple next =>
              simp only [step, observed, Outcome.bind, Outcome.state]
              refine ⟨kept, ?_⟩
              intro event final same
              cases same
              exact ⟨⟨available, continued.2.2.1, continued.1⟩,
                ⟨inputs.2.1.1, continued.2.2.2.1⟩, continued.2.2.2.2, continued.2.1⟩
          | ended =>
              simp only [step, observed, Outcome.bind, Outcome.state]
              exact ⟨kept, by intro event final same; cases same; trivial⟩
  | readOperand node inner tuple _ih =>
      cases tuple with
      | nil =>
          exact pure_effects before semantic covered (.more (.extend node inner))
            ⟨⟨inputs.1.1, inputs.1.2.1⟩, inputs.2.1, inputs.2.2.1⟩
      | cons first rest =>
          have exposed := expose_effects h node before semantic covered inputs.1.1 inputs.2.1.1
          cases read : expose h node before with
          | failed fault after =>
              simp only [step, read, Outcome.bind, Outcome.state]
              exact ⟨by simpa only [read, Outcome.state] using exposed.1,
                by intro event final same; cases same⟩
          | done rows after =>
              have kept : HeapEffects before after := by simpa only [read, Outcome.state] using exposed.1
              have prior := inputs_grows (.readOperand node inner (first :: rest)) kept.growth kept.history inputs.1
              have returned := exposed.2 rows after read
              simp only [step, read, Outcome.bind, Outcome.state]
              refine ⟨kept, ?_⟩
              intro event final same
              cases same
              exact ⟨⟨prior.1, prior.2.1, prior.2.2, returned.1⟩,
                inputs.2.1, inputs.2.2.1, inputs.2.2.2, returned.2⟩
  | scanOperand node inner tuple remaining _ih =>
      cases tuple with
      | nil =>
          exact pure_effects before semantic covered (.more (.extend node inner))
            ⟨⟨inputs.1.1, inputs.1.2.1⟩, inputs.2.1, inputs.2.2.1⟩
      | cons first rest =>
          cases remaining with
          | nil =>
              exact pure_effects before semantic covered (.more (.extend node inner))
                ⟨⟨inputs.1.1, inputs.1.2.1⟩, inputs.2.1, inputs.2.2.1⟩
          | cons edge rows =>
              have continued : CursorInputs before.heap (.scanOperand node inner (first :: rest) rows) :=
                ⟨⟨inputs.1.1, inputs.1.2.1, inputs.1.2.2.1,
                    fun selected member => inputs.1.2.2.2 selected (List.mem_cons_of_mem _ member)⟩,
                  inputs.2.1, inputs.2.2.1, inputs.2.2.2.1,
                    fun selected member => inputs.2.2.2.2 selected (List.mem_cons_of_mem _ member)⟩
              have resident : Edges before.heap (edge :: first :: rest) := by
                intro selected member
                rcases List.mem_cons.mp member with rfl | member
                · exact inputs.1.2.2.2 selected List.mem_cons_self
                · exact inputs.1.2.2.1 selected member
              have closed : ClosedEdges (edge :: first :: rest) := by
                intro selected member
                rcases List.mem_cons.mp member with rfl | member
                · exact inputs.2.2.2.2 selected List.mem_cons_self
                · exact inputs.2.2.2.1 selected member
              simp only [step]
              split
              · split
                · exact pure_effects before semantic covered _ ⟨resident, closed, continued⟩
                · exact pure_effects before semantic covered _ continued
              · exact pure_effects before semantic covered _ continued

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))] in
private theorem collected_grows {before after : State Symbol Guard} (growth : Grows before after)
    {tuples : List (List Edge)} (resident : Collected before tuples) : Collected after tuples :=
  fun tuple member => edges_grows growth (resident tuple member)

private theorem advance_effects (h budget : Nat) (cursor : Cursor Symbol Formula)
    (collected : List (List Edge)) (before : Physical Symbol Formula)
    (semantic : SemanticHeap before.heap) (covered : Covered [] before.heap)
    (inputs : CursorInputs before.heap cursor) (resident : Collected before.heap collected)
    (closed : ClosedCollected collected) :
    HeapEffects before (advance h budget cursor collected before).state ∧
      ∀ status after, advance h budget cursor collected before = .done status after →
        StatusInputs after.heap status ∧ StatusClosed status := by
  have first := step_effects h cursor before semantic covered inputs
  cases observed : step h cursor before with
  | failed fault after =>
      simp only [advance, observed, Outcome.bind, Outcome.state]
      exact ⟨by simpa only [observed, Outcome.state] using first.1,
        by intro status final same; cases same⟩
  | done event after =>
      have kept : HeapEffects before after := by simpa only [observed, Outcome.state] using first.1
      have supported := first.2 event after observed
      have oldRows := collected_grows kept.growth resident
      cases event with
      | more next =>
          simp only [advance, observed, Outcome.bind, Outcome.state]
          refine ⟨kept, ?_⟩
          intro status final same
          cases same
          exact ⟨⟨supported.1, oldRows⟩, supported.2.1, supported.2.2, closed⟩
      | ended =>
          simp only [advance, observed, Outcome.bind, Outcome.state]
          exact ⟨kept, by intro status final same; cases same; exact ⟨oldRows, closed⟩⟩
      | yield tuple next =>
          have sampled : Collected after.heap (collected ++ [tuple]) := by
            intro row member
            rcases List.mem_append.mp member with old | added
            · exact oldRows row old
            · simpa only [List.mem_singleton.mp added] using supported.1
          have closedSample : ClosedCollected (collected ++ [tuple]) := by
            intro row member
            rcases List.mem_append.mp member with old | added
            · exact closed row old
            · simpa only [List.mem_singleton.mp added] using supported.2.1
          simp only [advance, observed, Outcome.bind]
          split <;> refine ⟨kept, ?_⟩ <;> intro status final same <;> cases same <;>
            exact ⟨⟨supported.2.2.1, sampled⟩,
              supported.2.2.2.1, supported.2.2.2.2, closedSample⟩

private theorem drive_effects (steps h budget : Nat) (cursor : Cursor Symbol Formula)
    (collected : List (List Edge)) (before : Physical Symbol Formula)
    (semantic : SemanticHeap before.heap) (covered : Covered [] before.heap)
    (inputs : CursorInputs before.heap cursor) (resident : Collected before.heap collected)
    (closed : ClosedCollected collected) :
    HeapEffects before (drive steps h budget cursor collected before).state ∧
      ∀ status after, drive steps h budget cursor collected before = .done status after →
        StatusInputs after.heap status ∧ StatusClosed status := by
  induction steps generalizing cursor collected before with
  | zero =>
      exact ⟨HeapEffects.refl before semantic covered,
        by intro status final same; cases same; exact ⟨⟨inputs.1, resident⟩, inputs.2.1, inputs.2.2, closed⟩⟩
  | succ steps ih =>
      have first := advance_effects h budget cursor collected before semantic covered inputs resident closed
      cases observed : advance h budget cursor collected before with
      | failed fault after =>
          simp only [drive, observed, Outcome.bind, Outcome.state]
          exact ⟨by simpa only [observed, Outcome.state] using first.1,
            by intro status final same; cases same⟩
      | done status after =>
          have kept : HeapEffects before after := by simpa only [observed, Outcome.state] using first.1
          have supported := first.2 status after observed
          cases status with
          | running next sampled =>
              have later := ih next sampled after kept.semantic kept.covered
                ⟨supported.1.1, supported.2.1, supported.2.2.1⟩ supported.1.2 supported.2.2.2
              simp only [drive, observed, Outcome.bind]
              exact ⟨kept.trans later.1, later.2⟩
          | fit sampled | overflow sampled next =>
              simp only [drive, observed, Outcome.bind, Outcome.state]
              exact ⟨kept, by intro result final same; cases same; exact supported⟩

/-- Every total sample outcome retains weak heap effects and all successful resident closed rows. -/
theorem sample_effects (h budget : Nat) (nodes : List Node) (before : Physical Symbol Formula)
    (semantic : SemanticHeap before.heap) (covered : Covered [] before.heap)
    (available : Values before.heap nodes) (closed : ClosedValues nodes) :
    let actual := SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before
    SemanticHeap actual.state.heap ∧ Covered [] actual.state.heap ∧ Grows before.heap actual.state.heap ∧
      Extends before.heap.nodes.issued actual.state.heap.nodes.issued ∧
      ∀ result after, actual = .done result after → StatusInputs after.heap result.toStatus ∧ ResultClosed result := by
  obtain ⟨steps, eventual⟩ := SourceCurrentConjunctionTuplePullTotal.sample_observation h budget nodes before
  have actual := eventual 0
  simp only [Nat.add_zero, SourceCurrentConjunctionTuplePullAdmission.sample] at actual
  have first := drive_effects steps h budget (start nodes) [] before semantic covered
    ⟨SourceCurrentConjunctionTuplePullEffects.start_inputs before.heap nodes available,
      SourceCurrentConjunctionTuplePullClosed.start_closed nodes closed,
      SourceCurrentConjunctionTuplePullClosed.start_rows nodes⟩
    (by intro tuple member; cases member) (by intro tuple member; cases member)
  have kept := first.1
  rw [actual, SourceCurrentConjunctionTuplePullTotal.observe_state] at kept
  refine ⟨kept.semantic, kept.covered, kept.growth, kept.history, ?_⟩
  intro result after done
  have returned : drive steps h budget (start nodes) [] before = .done result.toStatus after := by
    rw [actual, done]
    rfl
  have supported := first.2 result.toStatus after returned
  refine ⟨supported.1, ?_⟩
  cases result <;> exact supported.2

/-- Actual fitting samples supply every tuple's resident rows and closed children. -/
theorem sample_fit (h budget : Nat) (nodes : List Node) (before after : Physical Symbol Formula)
    (tuples : List (List Edge))
    (actual : SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before = .done (.fit tuples) after)
    (semantic : SemanticHeap before.heap) (covered : Covered [] before.heap)
    (available : Values before.heap nodes) (closed : ClosedValues nodes) :
    ∀ tuple ∈ tuples, Edges after.heap tuple ∧ ClosedEdges tuple := by
  have returned := (sample_effects h budget nodes before semantic covered available closed).2.2.2.2
    (.fit tuples) after actual
  exact fun tuple member => ⟨returned.1 tuple member, returned.2 tuple member⟩

end MicroCFTA.SourceCurrentConjunctionTuplePullWeakEffects
