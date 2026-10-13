import MicroCFTA.InternedPendingOrdinaryOrigins

/-!
# Source paths from ordinary-name producers

Each captured ordinary name retains its actual introducing callback entry.
The source path starts in that entry's body and ends at the current expression.
Each crossed callback also retains its position in the cache history.
-/
namespace MicroCFTA.InternedOrdinaryProducerPaths
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedProvenance InternedFreeAbsenceContext
open InternedNestedMissReadback
open InternedActiveSourceOrigins InternedActiveSourceReplay
open InternedBinderProtocol (Reference NodeKey)

/-- Every ordinary input retains its enclosing producer and actual descendant path. -/
def Inputs [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (names : List Reference) (state : State Symbol Guard) : Prop :=
  ∀ level, .uninterned level ∈ names →
    ∃ producer : Crossing Symbol Guard, ∃ crossings,
      producer.name = .uninterned level ∧
      Path producer.body (producer.name :: producer.names) expression names crossings ∧
      Grows producer.start state ∧
      ∀ crossing ∈ crossings, Grows producer.start crossing.before ∧ Grows crossing.start state

/-- Later effects retain each source path and all its completed introductions. -/
theorem Inputs.grows [DecidableEq (EdgeKey Symbol Guard)] {expression : Syntax Symbol Guard}
    {names : List Reference} {before after : State Symbol Guard}
    (inputs : Inputs expression names before) (growth : Grows before after) : Inputs expression names after := by
  intro level member
  obtain ⟨producer, crossings, named, path, initial, traces⟩ := inputs level member
  exact ⟨producer, crossings, named, path, grows_trans initial growth,
    fun crossing included => ⟨(traces crossing included).1, grows_trans (traces crossing included).2 growth⟩⟩

/-- An ordinary child extends each producer's source path. -/
theorem Inputs.node [DecidableEq (EdgeKey Symbol Guard)] {edges : List (EdgeSyntax Symbol Guard)}
    {symbol : Symbol} {guard : Guard} {children : List (Syntax Symbol Guard)} {child : Syntax Symbol Guard}
    {state : State Symbol Guard} (inputs : Inputs (.node edges) names state)
    (edge : .mk symbol guard children ∈ edges) (member : child ∈ children) : Inputs child names state := by
  intro level included
  obtain ⟨producer, crossings, named, path, initial, traces⟩ := inputs level included
  exact ⟨producer, crossings, named, by simpa using path.trans (.node edge member (.here child names)), initial, traces⟩

/-- A union operand extends each producer's source path. -/
theorem Inputs.union [DecidableEq (EdgeKey Symbol Guard)] {members : List (Syntax Symbol Guard)}
    {child : Syntax Symbol Guard} {state : State Symbol Guard} (inputs : Inputs (.union members) names state)
    (member : child ∈ members) : Inputs child names state := by
  intro level included
  obtain ⟨producer, crossings, named, path, initial, traces⟩ := inputs level included
  exact ⟨producer, crossings, named, by simpa using path.trans (.union member (.here child names)), initial, traces⟩

/-- An actual entry either introduces this name or extends its enclosing producer's path. -/
theorem crossing_inputs [DecidableEq (EdgeKey Symbol Guard)] (crossing : Crossing Symbol Guard)
    (inputs : Inputs (.binder crossing.smart crossing.body) crossing.names crossing.before) :
    Inputs crossing.body (crossing.name :: crossing.names) crossing.start := by
  intro level member
  rcases List.mem_cons.mp member with own | captured
  · exact ⟨crossing, [], own.symm, .here _ _, grows_refl _, by intro selected impossible; cases impossible⟩
  · obtain ⟨producer, crossings, named, path, initial, traces⟩ := inputs level captured
    refine ⟨producer, [crossing] ++ crossings, named, path.trans (.binder crossing (.here _ _)),
      grows_trans initial crossing.facts.2, ?_⟩
    intro selected included
    rcases List.mem_append.mp included with own | old
    · have same : selected = crossing := List.mem_singleton.mp own
      subst selected
      exact ⟨initial, grows_refl _⟩
    · exact ⟨(traces selected old).1, grows_trans (traces selected old).2 crossing.facts.2⟩

/-- The captured environment is the exact suffix below the producer's ordinary name. -/
theorem Inputs.producer [DecidableEq (EdgeKey Symbol Guard)] {expression : Syntax Symbol Guard}
    {names : List Reference} {state : State Symbol Guard} (inputs : Inputs expression names state)
    (level : Nat) (member : .uninterned level ∈ names) :
    ∃ producer : Crossing Symbol Guard, ∃ crossings depth,
      producer.name = .uninterned level ∧
      Path producer.body (.uninterned level :: producer.names) expression names crossings ∧
      names = crossings.map Crossing.name ++ .uninterned level :: producer.names ∧
      producer.names.length < names.length ∧
      callback producer.body (producer.names.map Value.reference) .depth producer.before = .done depth producer.start ∧
      depth.depth = level ∧ Grows producer.start state ∧
      ∀ crossing ∈ crossings, Grows producer.start crossing.before ∧ Grows crossing.start state := by
  obtain ⟨producer, crossings, named, path, initial, traces⟩ := inputs level member
  obtain ⟨depth, done, same⟩ := InternedPendingOrdinaryMismatch.ordinary_readback producer level named
  have namesEq := InternedActiveSourceReplay.Path.names path
  refine ⟨producer, crossings, depth, named, by simpa only [named] using path,
    by simpa only [named] using namesEq, ?_, done, same, initial, traces⟩
  rw [namesEq, List.length_append, List.length_cons]
  omega

/-- The path invariant implies the earlier callback-only introduction invariant. -/
theorem Inputs.origins [DecidableEq (EdgeKey Symbol Guard)] {expression : Syntax Symbol Guard}
    {names : List Reference} {state : State Symbol Guard} (inputs : Inputs expression names state) :
    InternedPendingOrdinaryOrigins.Inputs names state := by
  intro level member
  obtain ⟨producer, crossings, depth, named, path, suffix, shorter, done, same, initial, traces⟩ :=
    inputs.producer level member
  exact ⟨producer.body, producer.names, producer.before, depth, producer.start,
    shorter, producer.context, done, same, initial⟩

end MicroCFTA.InternedOrdinaryProducerPaths
