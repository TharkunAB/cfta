import MicroCFTA.InternedFreshOrdinarySourceHistory

/-!
# Original source paths for every active repaired reservation

The scope retains each reservation's path from the initial call.
Descendant callbacks also retain the existing active source path and both
cache histories. A fresh reservation records its actual current root path.
-/
namespace MicroCFTA.InternedFreshOrdinaryRootScope
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax)
open InternedFreshOrdinaryActiveOrigins (Origin Path Crossing)
open InternedFreshOrdinarySourceHistory
open InternedBinderProtocol (NodeKey)

/-- Every active permission retains its originating source call and the actual route to the current expression. -/
def Scoped [DecidableEq (EdgeKey Symbol Guard)] (root : Syntax Symbol Guard) (initial : List (Value Symbol Guard))
    (blocked : NodeKey) (stop : State Symbol Guard)
    (waiting : List NodeKey) (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) : Prop :=
  ∀ key ∈ waiting, ∃ origin : Origin Symbol Guard key, StoppedRooted root initial blocked stop origin ∧ ∃ crossings,
    Path origin.body origin.localInputs expression environment crossings ∧ Grows origin.allocated state ∧
      ∀ crossing ∈ crossings, Grows origin.allocated crossing.before ∧ Grows crossing.start state

/-- Later source effects retain every active source path and crossing history. -/
theorem Scoped.grows [DecidableEq (EdgeKey Symbol Guard)] {expression : Syntax Symbol Guard}
    {before after : State Symbol Guard} (scope : Scoped root initial blocked stop waiting expression environment before)
    (growth : Grows before after) : Scoped root initial blocked stop waiting expression environment after := by
  intro key member
  obtain ⟨origin, rooted, crossings, path, initial, traces⟩ := scope key member
  exact ⟨origin, rooted, crossings, path, grows_trans initial growth,
    fun crossing included => ⟨(traces crossing included).1, grows_trans (traces crossing included).2 growth⟩⟩

/-- A node child extends the active source path without changing lexical inputs. -/
theorem Scoped.node [DecidableEq (EdgeKey Symbol Guard)] {edges : List (EdgeSyntax Symbol Guard)}
    {symbol : Symbol} {guard : Guard} {children : List (Syntax Symbol Guard)} {child : Syntax Symbol Guard}
    {state : State Symbol Guard} (scope : Scoped root initial blocked stop waiting (.node edges) environment state)
    (edge : .mk symbol guard children ∈ edges) (member : child ∈ children) : Scoped root initial blocked stop waiting child environment state := by
  intro key included
  obtain ⟨origin, rooted, crossings, path, growth, traces⟩ := scope key included
  exact ⟨origin, rooted, crossings, by simpa using path.trans (.node edge member (.here child environment)), growth, traces⟩

/-- A union operand extends the active source path without changing lexical inputs. -/
theorem Scoped.union [DecidableEq (EdgeKey Symbol Guard)] {members : List (Syntax Symbol Guard)}
    {child : Syntax Symbol Guard} {state : State Symbol Guard} (scope : Scoped root initial blocked stop waiting (.union members) environment state)
    (member : child ∈ members) : Scoped root initial blocked stop waiting child environment state := by
  intro key included
  obtain ⟨origin, rooted, crossings, path, growth, traces⟩ := scope key included
  exact ⟨origin, rooted, crossings, by simpa using path.trans (.union member (.here child environment)), growth, traces⟩

/-- An actual callback entry extends every active ancestor's source path. -/
theorem Scoped.enter [DecidableEq (EdgeKey Symbol Guard)] (crossing : Crossing Symbol Guard)
    (scope : Scoped root initial blocked stop waiting (.binder crossing.smart crossing.body) crossing.environment crossing.before) :
    Scoped root initial blocked stop waiting crossing.body (.reference crossing.name :: crossing.environment) crossing.start := by
  intro key included
  obtain ⟨origin, rooted, crossings, path, growth, traces⟩ := scope key included
  refine ⟨origin, rooted, [crossing] ++ crossings, path.trans (.binder crossing (.here _ _)),
    grows_trans growth crossing.facts.2, ?_⟩
  intro selected member
  rcases List.mem_append.mp member with own | old
  · have same : selected = crossing := List.mem_singleton.mp own
    subst selected
    exact ⟨growth, grows_refl _⟩
  · exact ⟨(traces selected old).1, grows_trans (traces selected old).2 crossing.facts.2⟩

/-- The fresh body's own reservation starts a new path and retains all older paths. -/
theorem Scoped.reserve [DecidableEq (EdgeKey Symbol Guard)] (origin : Origin Symbol Guard key) (rooted : StoppedRooted root initial blocked stop origin)
    (older : Scoped root initial blocked stop waiting origin.body origin.localInputs origin.allocated) :
    Scoped root initial blocked stop (key :: waiting) origin.body origin.localInputs origin.allocated := by
  intro selected member
  rcases List.mem_cons.mp member with rfl | previous
  · exact ⟨origin, rooted, [], .here _ _, grows_refl _, by intro crossing impossible; cases impossible⟩
  · exact older selected previous

end MicroCFTA.InternedFreshOrdinaryRootScope
