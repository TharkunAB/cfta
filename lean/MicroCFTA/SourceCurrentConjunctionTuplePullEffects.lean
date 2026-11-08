import MicroCFTA.SourceCurrentConjunctionTuplePull
import MicroCFTA.SourceCurrentConjunctionRowsExposureFields
import MicroCFTA.SourceCurrentConjunctionExposureProbes

set_option autoImplicit false

/-!
Actual cursor transitions retain full physical readiness and clean probes.
Only a demanded singleton exposure reads the heap. The cursor invariant
records available operands and resident rows. It supplies no future read.
All exposure faults retain their actual returned state.
-/
namespace MicroCFTA.SourceCurrentConjunctionTuplePullEffects
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceCurrentConjunctionRowsWorker (Physical Outcome)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionTuplePull (Cursor Event expose step start)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Heap" => InternedFreshOrdinaryProbeHeap.Heap

/-- Every suspended operand is available and every retained row is resident. -/
def Inputs (heap : InternedConstructorTemplates.State Symbol Guard) : Cursor Symbol Formula → Prop
  | .empty => True
  | .seed node => Available heap node
  | .seedRows rows => Edges heap rows
  | .extend node inner => Available heap node ∧ Inputs heap inner
  | .readOperand node inner tuple => Available heap node ∧ Inputs heap inner ∧ Edges heap tuple
  | .scanOperand node inner tuple remaining =>
      Available heap node ∧ Inputs heap inner ∧ Edges heap tuple ∧ Edges heap remaining

/-- A successful event retains its continuation and its yielded resident tuple. -/
def EventInputs (heap : InternedConstructorTemplates.State Symbol Guard) : Event Symbol Formula → Prop
  | .more next => Inputs heap next
  | .yield tuple next => Edges heap tuple ∧ Inputs heap next
  | .ended => True

private theorem edges_keeps {before after : InternedConstructorTemplates.State Symbol Guard}
    (kept : SourceEqualityRequiredCache.Keeps before after) {rows : List Edge}
    (resident : Edges before rows) : Edges after rows :=
  fun edge member => InternedEdgeResidency.edge_grows before after kept.growth edge (resident edge member)

/-- Actual cache retention carries every suspended operand and row. -/
theorem Inputs.keeps {before after : InternedConstructorTemplates.State Symbol Guard}
    (cursor : Cursor Symbol Formula) (kept : SourceEqualityRequiredCache.Keeps before after)
    (inputs : Inputs before cursor) : Inputs after cursor := by
  revert inputs
  induction cursor with
  | empty => intro _; trivial
  | seed node => intro available; exact kept.available node available
  | seedRows rows => intro resident; exact edges_keeps kept resident
  | extend node inner ih => intro inputs; exact ⟨kept.available node inputs.1, ih inputs.2⟩
  | readOperand node inner tuple ih =>
      intro inputs
      exact ⟨kept.available node inputs.1, ih inputs.2.1, edges_keeps kept inputs.2.2⟩
  | scanOperand node inner tuple remaining ih =>
      intro inputs
      exact ⟨kept.available node inputs.1, ih inputs.2.1,
        edges_keeps kept inputs.2.2.1, edges_keeps kept inputs.2.2.2⟩

private theorem fold_inputs (heap : InternedConstructorTemplates.State Symbol Guard)
    (nodes : List Node) (available : Values heap nodes) (cursor : Cursor Symbol Formula)
    (inputs : Inputs heap cursor) : Inputs heap (nodes.foldr Cursor.extend cursor) := by
  revert available
  induction nodes with
  | nil => intro _; exact inputs
  | cons node nodes ih =>
      intro available
      exact ⟨available node List.mem_cons_self,
        ih (fun value member => available value (List.mem_cons_of_mem _ member))⟩

/-- Starting the source fold needs only its actual available input operands. -/
theorem start_inputs (heap : InternedConstructorTemplates.State Symbol Guard)
    (nodes : List Node) (available : Values heap nodes) : Inputs heap (start nodes) := by
  cases nodes with
  | nil => trivial
  | cons first rest =>
      exact fold_inputs heap rest
        (fun value member => available value (List.mem_cons_of_mem _ member)) (.seed first)
        (available first List.mem_cons_self)

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

omit [DecidableEq Symbol] in
/-- One demanded singleton read retains full effects and returns resident rows. -/
theorem expose_effects (h : Nat) (node : Node) (before : Physical Symbol Formula)
    (ready : Ready before) (available : Available before.heap node) :
    Effects before (expose h node before).state ∧
      ∀ rows after, expose h node before = .done rows after → Edges after.heap rows := by
  have first := SourceEqualityExposureCosts.nodeEdges_verified h node before.heap
    ready.semantic ready.costs available
  have annotated := SourceCurrentOpenExposureFields.nodeEdges_heap
    (SourceCurrentConjunctionEquality.FieldAvailable before.equality) h node before.heap
    ready.semantic ready.fields available
  have kept : Effects before
      (⟨(MergedFreshOrdinaryExposure.nodeEdges h node before.heap).state, before.equality⟩ : Physical Symbol Formula) :=
    ⟨first.keeps, ⟨first.semantic, first.costs, ready.valid, annotated⟩,
      SourceEqualityConstraintMemoAllocation.grows_refl _⟩
  cases read : MergedFreshOrdinaryExposure.nodeEdges h node before.heap with
  | done rows heap =>
      rw [read] at kept first
      simp only [expose, SourceCurrentConjunctionRowsWorker.exposures, read, Outcome.bind,
        List.headD_cons, Outcome.state]
      exact ⟨kept, by intro result final same; cases same; exact first.rows rows heap rfl⟩
  | pending key heap =>
      rw [read] at kept
      simp only [expose, SourceCurrentConjunctionRowsWorker.exposures, read, Outcome.bind, Outcome.state]
      exact ⟨kept, by intro rows final same; cases same⟩
  | unresolved name heap =>
      rw [read] at kept
      simp only [expose, SourceCurrentConjunctionRowsWorker.exposures, read, Outcome.bind, Outcome.state]
      exact ⟨kept, by intro rows final same; cases same⟩
  | exhausted heap =>
      rw [read] at kept
      simp only [expose, SourceCurrentConjunctionRowsWorker.exposures, read, Outcome.bind, Outcome.state]
      exact ⟨kept, by intro rows final same; cases same⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))] in
private theorem pure_effects (before : Physical Symbol Formula) (ready : Ready before)
    (event : Event Symbol Formula) (inputs : EventInputs before.heap event) :
    Effects before (Outcome.done event before).state ∧
      ∀ result after, Outcome.done event before = .done result after → EventInputs after.heap result :=
  ⟨Effects.refl before ready, by intro result after same; cases same; exact inputs⟩

/-- Every actual transition retains full effects, including every read fault. -/
theorem step_effects (h : Nat) (cursor : Cursor Symbol Formula) (before : Physical Symbol Formula)
    (ready : Ready before) (inputs : Inputs before.heap cursor) :
    Effects before (step h cursor before).state ∧
      ∀ event after, step h cursor before = .done event after → EventInputs after.heap event := by
  induction cursor generalizing before with
  | empty => exact pure_effects before ready .ended trivial
  | seed node =>
      have first := expose_effects h node before ready inputs
      cases read : expose h node before with
      | failed fault after =>
          simp only [step, read, Outcome.bind, Outcome.state]
          exact ⟨by simpa only [read, Outcome.state] using first.1,
            by intro event final same; cases same⟩
      | done rows after =>
          have kept : Effects before after := by simpa only [read, Outcome.state] using first.1
          simp only [step, read, Outcome.bind, Outcome.state]
          exact ⟨kept, by intro event final same; cases same; exact first.2 rows after read⟩
  | seedRows rows =>
      cases rows with
      | nil => exact pure_effects before ready .ended trivial
      | cons edge rows =>
          exact pure_effects before ready (.yield [edge] (.seedRows rows))
            ⟨(by intro value member; simpa only [List.mem_singleton.mp member] using
              inputs edge List.mem_cons_self),
              fun value member => inputs value (List.mem_cons_of_mem _ member)⟩
  | extend node inner ih =>
      have first := ih before ready inputs.2
      cases observed : step h inner before with
      | failed fault after =>
          simp only [step, observed, Outcome.bind, Outcome.state]
          exact ⟨by simpa only [observed, Outcome.state] using first.1,
            by intro event final same; cases same⟩
      | done event after =>
          have kept : Effects before after := by simpa only [observed, Outcome.state] using first.1
          have continued := first.2 event after observed
          have nodeAvailable := kept.keeps.available node inputs.1
          cases event with
          | more next =>
              simp only [step, observed, Outcome.bind, Outcome.state]
              exact ⟨kept, by intro event final same; cases same; exact ⟨nodeAvailable, continued⟩⟩
          | yield tuple next =>
              simp only [step, observed, Outcome.bind, Outcome.state]
              refine ⟨kept, ?_⟩
              intro event final same
              cases same
              exact ⟨nodeAvailable, continued.2, continued.1⟩
          | ended =>
              simp only [step, observed, Outcome.bind, Outcome.state]
              exact ⟨kept, by intro event final same; cases same; trivial⟩
  | readOperand node inner tuple ih =>
      cases tuple with
      | nil => exact pure_effects before ready (.more (.extend node inner)) ⟨inputs.1, inputs.2.1⟩
      | cons first rest =>
          have exposed := expose_effects h node before ready inputs.1
          cases read : expose h node before with
          | failed fault after =>
              simp only [step, read, Outcome.bind, Outcome.state]
              exact ⟨by simpa only [read, Outcome.state] using exposed.1,
                by intro event final same; cases same⟩
          | done rows after =>
              have kept : Effects before after := by simpa only [read, Outcome.state] using exposed.1
              simp only [step, read, Outcome.bind, Outcome.state]
              refine ⟨kept, ?_⟩
              intro event final same
              cases same
              exact ⟨kept.keeps.available node inputs.1, Inputs.keeps inner kept.keeps inputs.2.1,
                edges_keeps kept.keeps inputs.2.2, exposed.2 rows after read⟩
  | scanOperand node inner tuple remaining ih =>
      cases tuple with
      | nil => exact pure_effects before ready (.more (.extend node inner)) ⟨inputs.1, inputs.2.1⟩
      | cons first rest =>
          cases remaining with
          | nil => exact pure_effects before ready (.more (.extend node inner)) ⟨inputs.1, inputs.2.1⟩
          | cons edge rows =>
              have continued : Inputs before.heap (.scanOperand node inner (first :: rest) rows) :=
                ⟨inputs.1, inputs.2.1, inputs.2.2.1,
                  fun value member => inputs.2.2.2 value (List.mem_cons_of_mem _ member)⟩
              have yielded : Edges before.heap (edge :: first :: rest) := by
                intro value member
                rcases List.mem_cons.mp member with rfl | member
                · exact inputs.2.2.2 value List.mem_cons_self
                · exact inputs.2.2.1 value member
              simp only [step]
              split
              · split
                · exact pure_effects before ready _ ⟨yielded, continued⟩
                · exact pure_effects before ready _ continued
              · exact pure_effects before ready _ continued

omit [DecidableEq Symbol] in
/-- A demanded singleton read retains clean probes on success and failure. -/
theorem expose_probes (h : Nat) (node : Node) (before : Physical Symbol Formula)
    (ready : Ready before) (probes : Heap before.heap) (available : Available before.heap node) :
    Heap (expose h node before).state.heap := by
  have clean := SourceCurrentConjunctionExposureProbes.exposures_heap h [node] before
    ready.semantic ready.costs probes
    (by intro value member; simpa only [List.mem_singleton.mp member] using available)
  cases read : SourceCurrentConjunctionRowsWorker.exposures h [node] before <;>
    simpa only [expose, read, Outcome.bind, Outcome.state] using clean

/-- Every actual transition retains clean probes without a completion premise. -/
theorem step_probes (h : Nat) (cursor : Cursor Symbol Formula) (before : Physical Symbol Formula)
    (ready : Ready before) (probes : Heap before.heap) (inputs : Inputs before.heap cursor) :
    Heap (step h cursor before).state.heap := by
  induction cursor generalizing before with
  | empty => exact probes
  | seedRows rows => cases rows <;> exact probes
  | seed node =>
      have clean := expose_probes h node before ready probes inputs
      cases read : expose h node before <;>
        simpa only [step, read, Outcome.bind, Outcome.state] using clean
  | extend node inner ih =>
      have clean := ih before ready probes inputs.2
      cases observed : step h inner before with
      | failed fault after => simpa only [step, observed, Outcome.bind, Outcome.state] using clean
      | done event after =>
          cases event <;> simpa only [step, observed, Outcome.bind, Outcome.state] using clean
  | readOperand node inner tuple ih =>
      cases tuple with
      | nil => exact probes
      | cons first rest =>
          have clean := expose_probes h node before ready probes inputs.1
          cases read : expose h node before <;>
            simpa only [step, read, Outcome.bind, Outcome.state] using clean
  | scanOperand node inner tuple remaining ih =>
      cases tuple with
      | nil => exact probes
      | cons first rest =>
          cases remaining with
          | nil => exact probes
          | cons edge rows => simp only [step]; split <;> (try split) <;> exact probes

end MicroCFTA.SourceCurrentConjunctionTuplePullEffects
