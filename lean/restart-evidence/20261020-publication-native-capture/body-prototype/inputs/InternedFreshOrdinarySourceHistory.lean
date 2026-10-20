import MicroCFTA.InternedFreshOrdinaryJointMismatch

/-!
# Actual source paths and ordinary capture producers

A reached source expression retains its path from the original call.
Every crossed callback starts before the current cache. Its actual context
and selected argument remain available in that path.
-/
namespace MicroCFTA.InternedFreshOrdinarySourceHistory
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryContext InternedFreshOrdinaryActiveOrigins
open InternedBinderProtocol (Reference NodeKey)

/-- A reached source expression retains every actual callback crossing and its later cache history. -/
def Reached [DecidableEq (EdgeKey Symbol Guard)] (root : Syntax Symbol Guard)
    (initial : List (Value Symbol Guard)) (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) : Prop :=
  ∃ crossings, Path root initial expression environment crossings ∧
    ∀ crossing ∈ crossings, Grows crossing.start state

/-- The original source call starts with an empty callback path. -/
theorem reached_initial [DecidableEq (EdgeKey Symbol Guard)] (root : Syntax Symbol Guard)
    (initial : List (Value Symbol Guard)) (state : State Symbol Guard) : Reached root initial root initial state :=
  ⟨[], .here _ _, by intro crossing impossible; cases impossible⟩

/-- Later source effects retain the original path and every crossing history. -/
theorem Reached.grows [DecidableEq (EdgeKey Symbol Guard)] {root expression : Syntax Symbol Guard}
    {initial environment : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (reached : Reached root initial expression environment before) (growth : Grows before after) :
    Reached root initial expression environment after := by
  obtain ⟨crossings, path, traces⟩ := reached
  exact ⟨crossings, path, fun crossing member => grows_trans (traces crossing member) growth⟩

/-- A node child extends the original path without changing its lexical values. -/
theorem Reached.node [DecidableEq (EdgeKey Symbol Guard)] {root : Syntax Symbol Guard}
    {edges : List (EdgeSyntax Symbol Guard)} {symbol : Symbol} {guard : Guard}
    {children : List (Syntax Symbol Guard)} {child : Syntax Symbol Guard}
    {initial environment : List (Value Symbol Guard)} {state : State Symbol Guard}
    (reached : Reached root initial (.node edges) environment state)
    (edge : .mk symbol guard children ∈ edges) (member : child ∈ children) :
    Reached root initial child environment state := by
  obtain ⟨crossings, path, traces⟩ := reached
  exact ⟨crossings, by simpa using path.trans (.node edge member (.here _ _)), traces⟩

/-- A union operand extends the original path without changing its lexical values. -/
theorem Reached.union [DecidableEq (EdgeKey Symbol Guard)] {root : Syntax Symbol Guard}
    {members : List (Syntax Symbol Guard)} {child : Syntax Symbol Guard}
    {initial environment : List (Value Symbol Guard)} {state : State Symbol Guard}
    (reached : Reached root initial (.union members) environment state) (member : child ∈ members) :
    Reached root initial child environment state := by
  obtain ⟨crossings, path, traces⟩ := reached
  exact ⟨crossings, by simpa using path.trans (.union member (.here _ _)), traces⟩

/-- An actual callback entry retains the new crossing and every earlier callback history. -/
theorem Reached.enter [DecidableEq (EdgeKey Symbol Guard)] {root : Syntax Symbol Guard}
    {initial : List (Value Symbol Guard)} (crossing : Crossing Symbol Guard)
    (reached : Reached root initial (.binder crossing.smart crossing.body) crossing.environment crossing.before) :
    Reached root initial crossing.body (.reference crossing.name :: crossing.environment) crossing.start := by
  obtain ⟨crossings, path, traces⟩ := reached
  refine ⟨[crossing] ++ crossings, path.trans (.binder crossing (.here _ _)), ?_⟩
  intro selected member
  rcases List.mem_append.mp member with own | old
  · have same := List.mem_singleton.mp own
    subst selected
    exact grows_refl _
  · exact grows_trans (traces selected old) crossing.facts.2

/-- Every crossed binder has fewer captured slots than the final descendant expression. -/
theorem Path.crossing_shorter [DecidableEq (EdgeKey Symbol Guard)]
    {root expression : Syntax Symbol Guard} {initial environment : List (Value Symbol Guard)}
    {crossings : List (Crossing Symbol Guard)} (path : Path root initial expression environment crossings)
    (selected : Crossing Symbol Guard) (member : selected ∈ crossings) :
    selected.environment.length < environment.length := by
  induction path with
  | here => cases member
  | node edge child nested ih | union child nested ih => exact ih member
  | binder crossing nested ih =>
      rcases List.mem_append.mp member with old | own
      · exact ih old
      · have same := List.mem_singleton.mp own
        subst selected
        have inputs := congrArg List.length nested.inputs
        simp only [List.length_append, List.length_map, List.length_cons] at inputs
        omega

/-- Each crossed callback retains its exact descendant path to the current expression. -/
theorem Path.crossing_tail [DecidableEq (EdgeKey Symbol Guard)]
    {root expression : Syntax Symbol Guard} {initial environment : List (Value Symbol Guard)}
    {crossings : List (Crossing Symbol Guard)} (path : Path root initial expression environment crossings)
    (selected : Crossing Symbol Guard) (member : selected ∈ crossings) :
    ∃ inner, Path selected.body (.reference selected.name :: selected.environment) expression environment inner := by
  induction path with
  | here => cases member
  | node edge child nested ih | union child nested ih => exact ih member
  | binder crossing nested ih =>
      rcases List.mem_append.mp member with old | own
      · exact ih old
      · have same := List.mem_singleton.mp own
        subst selected
        exact ⟨_, nested⟩

/-- An actual earlier producer retains its shorter captures, completed Depth call, and path to the current expression. -/
def ProducedAt [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (level : Nat) : Prop :=
  ∃ body captures before depth after inner,
    captures.length < environment.length ∧ Context before captures ∧
    callback body captures .depth before = .done depth after ∧ ordinaryLevel depth = level ∧
    Path body (.reference (.uninterned (ordinaryLevel depth)) :: captures) expression environment inner ∧ Grows after state

/-- A captured ordinary name is initial or came from an actual earlier ordinary callback. -/
theorem Reached.ordinary_capture [DecidableEq (EdgeKey Symbol Guard)] {root expression : Syntax Symbol Guard}
    {initial environment : List (Value Symbol Guard)} {state : State Symbol Guard}
    (reached : Reached root initial expression environment state) (value : Value Symbol Guard)
    (member : value ∈ environment) (level : Nat) (free : .uninterned level ∈ value.free) :
    (∃ original ∈ initial, .uninterned level ∈ original.free) ∨ ProducedAt expression environment state level := by
  obtain ⟨crossings, path, traces⟩ := reached
  rw [path.inputs] at member
  rcases List.mem_append.mp member with localValue | original
  · obtain ⟨crossing, crossed, same⟩ := List.mem_map.mp localValue
    have shorter := Path.crossing_shorter path crossing crossed
    obtain ⟨inner, descendant⟩ := Path.crossing_tail path crossing crossed
    rw [← same] at free
    have named : crossing.name = .uninterned level := (List.mem_singleton.mp free).symm
    have growth := traces crossing crossed
    rcases crossing with ⟨smart, body, captures, before, name, start, context, entered⟩
    cases entered with
    | depth => cases named
    | @ordinary depth after done =>
        exact Or.inr ⟨body, captures, before, depth, _, inner, shorter, context, done,
          Reference.uninterned.inj named, descendant, growth⟩
    | fresh => cases named
  · exact Or.inl ⟨value, original, free⟩

/-- The original source path to the active reservation's binder call. -/
def Rooted [DecidableEq (EdgeKey Symbol Guard)] (root : Syntax Symbol Guard)
    (initial : List (Value Symbol Guard)) (origin : Origin Symbol Guard key) : Prop :=
  Reached root initial (.binder origin.smart origin.body) origin.environment origin.before

/-- A stopped source path retains the actual pending outcome of every enclosing callback. -/
def StoppedReached [DecidableEq (EdgeKey Symbol Guard)] (root : Syntax Symbol Guard)
    (initial : List (Value Symbol Guard)) (blocked : NodeKey) (stop : State Symbol Guard)
    (expression : Syntax Symbol Guard) (environment : List (Value Symbol Guard)) (state : State Symbol Guard) : Prop :=
  ∃ crossings, Path root initial expression environment crossings ∧
    ∀ crossing ∈ crossings, Grows crossing.start state ∧
      callback crossing.body crossing.environment crossing.name crossing.start = .pending blocked stop

/-- The original stopped call has no enclosing callback. -/
theorem stopped_initial [DecidableEq (EdgeKey Symbol Guard)] (root : Syntax Symbol Guard)
    (initial : List (Value Symbol Guard)) (blocked : NodeKey) (stop state : State Symbol Guard) :
    StoppedReached root initial blocked stop root initial state :=
  ⟨[], .here _ _, by intro crossing impossible; cases impossible⟩

/-- A stopped source path retains the original cache history. -/
theorem StoppedReached.reached [DecidableEq (EdgeKey Symbol Guard)]
    {root expression : Syntax Symbol Guard}
    (stopped : StoppedReached root initial blocked stop expression environment state) :
    Reached root initial expression environment state := by
  obtain ⟨crossings, path, traces⟩ := stopped
  exact ⟨crossings, path, fun crossing member => (traces crossing member).1⟩

/-- Later source effects retain all enclosing pending equations. -/
theorem StoppedReached.grows [DecidableEq (EdgeKey Symbol Guard)] {before after : State Symbol Guard}
    (stopped : StoppedReached root initial blocked stop expression environment before) (growth : Grows before after) :
    StoppedReached root initial blocked stop expression environment after := by
  obtain ⟨crossings, path, traces⟩ := stopped
  exact ⟨crossings, path, fun crossing member => ⟨grows_trans (traces crossing member).1 growth, (traces crossing member).2⟩⟩

/-- A stopped node child retains every enclosing pending callback. -/
theorem StoppedReached.node [DecidableEq (EdgeKey Symbol Guard)] {edges : List (EdgeSyntax Symbol Guard)}
    {symbol : Symbol} {guard : Guard} {children : List (Syntax Symbol Guard)} {child : Syntax Symbol Guard}
    (stopped : StoppedReached root initial blocked stop (.node edges) environment state)
    (edge : .mk symbol guard children ∈ edges) (member : child ∈ children) :
    StoppedReached root initial blocked stop child environment state := by
  obtain ⟨crossings, path, traces⟩ := stopped
  exact ⟨crossings, by simpa using path.trans (.node edge member (.here _ _)), traces⟩

/-- A stopped union operand retains every enclosing pending callback. -/
theorem StoppedReached.union [DecidableEq (EdgeKey Symbol Guard)] {members : List (Syntax Symbol Guard)}
    {child : Syntax Symbol Guard} (stopped : StoppedReached root initial blocked stop (.union members) environment state)
    (member : child ∈ members) : StoppedReached root initial blocked stop child environment state := by
  obtain ⟨crossings, path, traces⟩ := stopped
  exact ⟨crossings, by simpa using path.trans (.union member (.here _ _)), traces⟩

/-- An actual stopped callback entry adds its pending equation to the original source path. -/
theorem StoppedReached.enter [DecidableEq (EdgeKey Symbol Guard)] (crossing : Crossing Symbol Guard)
    (stopped : StoppedReached root initial blocked stop (.binder crossing.smart crossing.body) crossing.environment crossing.before)
    (pending : callback crossing.body crossing.environment crossing.name crossing.start = .pending blocked stop) :
    StoppedReached root initial blocked stop crossing.body (.reference crossing.name :: crossing.environment) crossing.start := by
  obtain ⟨crossings, path, traces⟩ := stopped
  refine ⟨[crossing] ++ crossings, path.trans (.binder crossing (.here _ _)), ?_⟩
  intro selected member
  rcases List.mem_append.mp member with own | old
  · have same := List.mem_singleton.mp own
    subst selected
    exact ⟨grows_refl _, pending⟩
  · exact ⟨grows_trans (traces selected old).1 crossing.facts.2, (traces selected old).2⟩

/-- A shorter producer retains its completed Depth callback, stopped ordinary callback, and stopped binder call. -/
def PendingProducedAt [DecidableEq (EdgeKey Symbol Guard)] (blocked : NodeKey) (stop : State Symbol Guard)
    (expression : Syntax Symbol Guard) (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (level : Nat) : Prop :=
  ∃ body captures before depth after inner,
    captures.length < environment.length ∧ Context before captures ∧
    callback body captures .depth before = .done depth after ∧ ordinaryLevel depth = level ∧
    Path body (.reference (.uninterned (ordinaryLevel depth)) :: captures) expression environment inner ∧ Grows after state ∧
    callback body captures (.uninterned (ordinaryLevel depth)) after = .pending blocked stop ∧
    ∀ smart, InternedFreshOrdinaryConstruction.build (.binder smart body) captures before = .pending blocked stop

/-- The pending producer retains the earlier completed-probe history. -/
theorem PendingProducedAt.produced [DecidableEq (EdgeKey Symbol Guard)]
    {expression : Syntax Symbol Guard}
    (producer : PendingProducedAt blocked stop expression environment state level) : ProducedAt expression environment state level := by
  obtain ⟨body, captures, before, depth, after, inner, shorter, context, done, selected, path, growth, _, _⟩ := producer
  exact ⟨body, captures, before, depth, after, inner, shorter, context, done, selected, path, growth⟩

/-- A stopped source path derives the actual pending ordinary callback of each noninitial ordinary capture. -/
theorem StoppedReached.ordinary_capture [DecidableEq (EdgeKey Symbol Guard)]
    (stopped : StoppedReached root initial blocked stop expression environment state)
    (value : Value Symbol Guard) (member : value ∈ environment) (level : Nat) (free : .uninterned level ∈ value.free) :
    (∃ original ∈ initial, .uninterned level ∈ original.free) ∨ PendingProducedAt blocked stop expression environment state level := by
  obtain ⟨crossings, path, traces⟩ := stopped
  rw [path.inputs] at member
  rcases List.mem_append.mp member with localValue | original
  · obtain ⟨crossing, crossed, same⟩ := List.mem_map.mp localValue
    have shorter := Path.crossing_shorter path crossing crossed
    obtain ⟨inner, descendant⟩ := Path.crossing_tail path crossing crossed
    rw [← same] at free
    have named : crossing.name = .uninterned level := (List.mem_singleton.mp free).symm
    obtain ⟨growth, pending⟩ := traces crossing crossed
    rcases crossing with ⟨smart, body, captures, before, name, start, context, entered⟩
    cases entered with
    | depth => cases named
    | @ordinary depth after done =>
        refine Or.inr ⟨body, captures, before, depth, _, inner, shorter, context, done,
          Reference.uninterned.inj named, descendant, growth, pending, ?_⟩
        intro selectedSmart
        rw [InternedFreshOrdinaryConstruction.build]
        change ((callback body captures .depth before).bind fun found afterDepth =>
          (callback body captures (.uninterned (ordinaryLevel found)) afterDepth).bind fun ordinary afterOrdinary =>
            InternedNestedConstruction.request selectedSmart found ordinary (callback body captures) afterOrdinary) = .pending blocked stop
        simp only [done, Outcome.bind, pending]
    | fresh => cases named
  · exact Or.inl ⟨value, original, free⟩

/-- The original path to an active reservation retains all enclosing pending callback equations. -/
def StoppedRooted [DecidableEq (EdgeKey Symbol Guard)] (root : Syntax Symbol Guard)
    (initial : List (Value Symbol Guard)) (blocked : NodeKey) (stop : State Symbol Guard) (origin : Origin Symbol Guard key) : Prop :=
  StoppedReached root initial blocked stop (.binder origin.smart origin.body) origin.environment origin.before

/-- An active reservation's captured ordinary name has an initial value or an actual stopped shorter producer. -/
theorem StoppedRooted.ordinary_capture [DecidableEq (EdgeKey Symbol Guard)]
    {origin : Origin Symbol Guard key}
    (rooted : StoppedRooted root initial blocked stop origin) (level : Nat) (member : .uninterned level ∈ origin.depth.free) :
    (∃ original ∈ initial, .uninterned level ∈ original.free) ∨
      PendingProducedAt blocked stop (.binder origin.smart origin.body) origin.environment origin.before level := by
  obtain ⟨value, supplied, captured⟩ := InternedFreshOrdinaryJointMismatch.Origin.ordinary_capture origin level member
  exact StoppedReached.ordinary_capture rooted value supplied level captured

/-- An active ancestor's old ordinary capture has its actual initial or shorter producer history. -/
theorem Rooted.ordinary_capture [DecidableEq (EdgeKey Symbol Guard)] {root : Syntax Symbol Guard}
    {initial : List (Value Symbol Guard)} {origin : Origin Symbol Guard key}
    (rooted : Rooted root initial origin) (level : Nat) (member : .uninterned level ∈ origin.depth.free) :
    (∃ original ∈ initial, .uninterned level ∈ original.free) ∨
      ProducedAt (.binder origin.smart origin.body) origin.environment origin.before level := by
  obtain ⟨value, supplied, captured⟩ := InternedFreshOrdinaryJointMismatch.Origin.ordinary_capture origin level member
  exact Reached.ordinary_capture rooted value supplied level captured

end MicroCFTA.InternedFreshOrdinarySourceHistory
