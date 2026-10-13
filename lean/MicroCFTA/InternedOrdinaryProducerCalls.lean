import MicroCFTA.InternedPendingProducerReplay

/-!
# Actual stopped callbacks of ordinary-name producers

Each captured ordinary name retains its actual introducing callback entry.
The source path starts in that entry's body and ends at the current expression.
Each producer ordinary callback stops at the same exact pending request.
-/
namespace MicroCFTA.InternedOrdinaryProducerCalls
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedProvenance InternedFreeAbsenceContext
open InternedNestedMissReadback
open InternedActiveSourceOrigins InternedActiveSourceReplay
open InternedBinderProtocol (Reference NodeKey)

variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]
variable (blocked : NodeKey) (final : State Symbol Guard)

/-- Every ordinary input retains its enclosing producer and actual descendant path. -/
def Inputs (expression : Syntax Symbol Guard)
    (names : List Reference) (state : State Symbol Guard) : Prop :=
  ∀ index level, names[index]? = some (.uninterned level) →
    ∃ producer : Crossing Symbol Guard, ∃ crossings,
      producer.name = .uninterned level ∧
      Path producer.body (producer.name :: producer.names) expression names crossings ∧
      crossings.length = index ∧ Grows producer.start state ∧
      (∀ crossing ∈ crossings, Grows producer.start crossing.before ∧ Grows crossing.start state) ∧
      callback producer.body (producer.names.map Value.reference) producer.name producer.start = .pending blocked final

variable {blocked final}

/-- Later effects retain each source path and its enclosing stopped callback. -/
theorem Inputs.grows {expression : Syntax Symbol Guard}
    {names : List Reference} {before after : State Symbol Guard}
    (inputs : Inputs blocked final expression names before) (growth : Grows before after) : Inputs blocked final expression names after := by
  intro index level member
  obtain ⟨producer, crossings, named, path, position, initial, traces, stoppedProducer⟩ := inputs index level member
  exact ⟨producer, crossings, named, path, position, grows_trans initial growth,
    fun crossing included => ⟨(traces crossing included).1, grows_trans (traces crossing included).2 growth⟩, stoppedProducer⟩

/-- An ordinary child extends each producer's source path. -/
theorem Inputs.node {edges : List (EdgeSyntax Symbol Guard)}
    {symbol : Symbol} {guard : Guard} {children : List (Syntax Symbol Guard)} {child : Syntax Symbol Guard}
    {state : State Symbol Guard} (inputs : Inputs blocked final (.node edges) names state)
    (edge : .mk symbol guard children ∈ edges) (member : child ∈ children) : Inputs blocked final child names state := by
  intro index level included
  obtain ⟨producer, crossings, named, path, position, initial, traces, stoppedProducer⟩ := inputs index level included
  exact ⟨producer, crossings, named, by simpa using path.trans (.node edge member (.here child names)), position, initial, traces, stoppedProducer⟩

/-- A union operand extends each producer's source path. -/
theorem Inputs.union {members : List (Syntax Symbol Guard)}
    {child : Syntax Symbol Guard} {state : State Symbol Guard} (inputs : Inputs blocked final (.union members) names state)
    (member : child ∈ members) : Inputs blocked final child names state := by
  intro index level included
  obtain ⟨producer, crossings, named, path, position, initial, traces, stoppedProducer⟩ := inputs index level included
  exact ⟨producer, crossings, named, by simpa using path.trans (.union member (.here child names)), position, initial, traces, stoppedProducer⟩

/-- An actual entry either introduces this name or extends its enclosing producer's path. -/
theorem crossing_inputs (crossing : Crossing Symbol Guard)
    (inputs : Inputs blocked final (.binder crossing.smart crossing.body) crossing.names crossing.before)
    (stopped : callback crossing.body (crossing.names.map Value.reference) crossing.name crossing.start = .pending blocked final) :
    Inputs blocked final crossing.body (crossing.name :: crossing.names) crossing.start := by
  intro index level member
  cases index with
  | zero =>
      have own : crossing.name = .uninterned level := by simpa using member
      exact ⟨crossing, [], own, .here _ _, rfl, grows_refl _,
        (by intro selected impossible; cases impossible), stopped⟩
  | succ index =>
      have captured : crossing.names[index]? = some (.uninterned level) := by simpa using member
      obtain ⟨producer, crossings, named, path, position, initial, traces, stoppedProducer⟩ := inputs index level captured
      refine ⟨producer, [crossing] ++ crossings, named, path.trans (.binder crossing (.here _ _)),
        by simp [position], grows_trans initial crossing.facts.2, ?_, stoppedProducer⟩
      intro selected included
      rcases List.mem_append.mp included with own | old
      · have same : selected = crossing := List.mem_singleton.mp own
        subst selected
        exact ⟨initial, grows_refl _⟩
      · exact ⟨(traces selected old).1, grows_trans (traces selected old).2 crossing.facts.2⟩

/-- Membership can forget the input index while retaining the same producer and stopped call. -/
theorem Inputs.capture {expression : Syntax Symbol Guard} {names : List Reference} {state : State Symbol Guard}
    (inputs : Inputs blocked final expression names state) (level : Nat) (member : .uninterned level ∈ names) :
    ∃ producer : Crossing Symbol Guard, ∃ crossings,
      producer.name = .uninterned level ∧
      Path producer.body (producer.name :: producer.names) expression names crossings ∧
      Grows producer.start state ∧
      (∀ crossing ∈ crossings, Grows producer.start crossing.before ∧ Grows crossing.start state) ∧
      callback producer.body (producer.names.map Value.reference) producer.name producer.start = .pending blocked final := by
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨producer, crossings, named, path, _, initial, traces, stopped⟩ := inputs index level found
  exact ⟨producer, crossings, named, path, initial, traces, stopped⟩

/-- The stopped-callback invariant retains the previously proved source-path invariant. -/
theorem Inputs.paths {expression : Syntax Symbol Guard} {names : List Reference} {state : State Symbol Guard}
    (inputs : Inputs blocked final expression names state) :
    InternedOrdinaryProducerPaths.Inputs expression names state := by
  intro level member
  obtain ⟨producer, crossings, named, path, initial, traces, _⟩ := inputs.capture level member
  exact ⟨producer, crossings, named, path, initial, traces⟩

end MicroCFTA.InternedOrdinaryProducerCalls
