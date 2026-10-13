import MicroCFTA.InternedLiveSiteReadiness
import MicroCFTA.InternedPendingScopes

/-!
# Active source reservations and actual descendant paths

Each active reservation retains its original source callbacks and lexical
inputs. Descendant paths record the actual Depth, ordinary, or fresh body
entry at each crossed binder. The paths retain cache growth for each entry.
-/
namespace MicroCFTA.InternedActiveSourceOrigins
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedNestedMissReadback InternedStoredMuOrigins InternedNestedSpecialization
open InternedFreeAbsenceContext InternedRequestAgreement
open InternedBinderProtocol (Reference NodeKey)

/-- A callback entry follows the actual source order and reservation result. -/
inductive Entered [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (body : Syntax Symbol Guard)
    (names : List Reference) (before : State Symbol Guard) : Reference → State Symbol Guard → Prop where
  | depth : Entered smart body names before .depth before
  | ordinary (depth : Value Symbol Guard) (afterDepth : State Symbol Guard)
      (done : callback body (names.map Value.reference) .depth before = .done depth afterDepth) :
      Entered smart body names before (.uninterned depth.depth) afterDepth
  | fresh (depth ordinary : Value Symbol Guard) (afterDepth cut : State Symbol Guard)
      (depthDone : callback body (names.map Value.reference) .depth before = .done depth afterDepth)
      (ordinaryDone : callback body (names.map Value.reference) (.uninterned depth.depth) afterDepth = .done ordinary cut)
      (missing : cut.nodes.table (muKey depth ordinary) = none) :
      Entered smart body names before (.interned (Cache.intern cut.nodes (muKey depth ordinary)).1.identity)
        {cut with nodes := (Cache.intern cut.nodes (muKey depth ordinary)).2}

/-- One source crossing records the chosen literal and its exact entry state. -/
structure Crossing (Symbol Guard : Type) [DecidableEq (EdgeKey Symbol Guard)] where
  smart : Bool
  body : Syntax Symbol Guard
  names : List Reference
  before : State Symbol Guard
  name : Reference
  start : State Symbol Guard
  context : Context before names
  entered : Entered smart body names before name start

/-- A reservation preserves both semantic tables and all prior literal inputs. -/
theorem reserve_context (key : NodeKey) (state : State Symbol Guard) (names : List Reference)
    (context : Context state names) :
    Context {state with nodes := (Cache.intern state.nodes key).2} names := by
  let allocated := {state with nodes := (Cache.intern state.nodes key).2}
  have growth : Grows state allocated :=
    ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
  have history := InternedFreshProbeKeys.intern_issued_extends state.nodes key context.normal.facts.coherent.valid.2
  exact ⟨reserve_normal key state context.normal,
    fun value member => (context.inputs value member).grows state allocated growth history,
    context.profiles, context.freeNames⟩

/-- Each recorded entry derives its full local context and actual cache growth. -/
theorem Crossing.facts [DecidableEq (EdgeKey Symbol Guard)] (crossing : Crossing Symbol Guard) :
    Context crossing.start (crossing.name :: crossing.names) ∧ Grows crossing.before crossing.start := by
  rcases crossing with ⟨smart, body, names, before, name, start, context, entered⟩
  cases entered with
  | depth => exact ⟨context.local .depth (depth_available before), grows_refl _⟩
  | @ordinary depth afterDepth done =>
      have afterContext : Context start names := by
        simpa only [done, Outcome.state] using context.callback body .depth (depth_available before)
      have growth : Grows before start := by
        simpa only [done, Outcome.state] using
          (callback_growing body (names.map Value.reference) .depth before context.normal.facts.coherent.valid).2
      exact ⟨afterContext.local _ (ordinary_available start depth.depth), growth⟩
  | @fresh depth ordinary afterDepth cut depthDone ordinaryDone missing =>
      have depthContext : Context afterDepth names := by
        simpa only [depthDone, Outcome.state] using context.callback body .depth (depth_available before)
      have cutContext : Context cut names := by
        simpa only [ordinaryDone, Outcome.state] using
          depthContext.callback body (.uninterned depth.depth) (ordinary_available afterDepth depth.depth)
      have depthGrowth : Grows before afterDepth := by
        simpa only [depthDone, Outcome.state] using
          (callback_growing body (names.map Value.reference) .depth before context.normal.facts.coherent.valid).2
      have ordinaryGrowth : Grows afterDepth cut := by
        simpa only [ordinaryDone, Outcome.state] using
          (callback_growing body (names.map Value.reference) (.uninterned depth.depth) afterDepth depthContext.normal.facts.coherent.valid).2
      have reserved := reserve_context (muKey depth ordinary) cut names cutContext
      exact ⟨reserved.local _ (InternedConstructionProvenance.reserve_available _ cut cutContext.normal.facts.coherent cutContext.normal.facts.cached).2,
        grows_trans depthGrowth (grows_trans ordinaryGrowth
          ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩)⟩

/-- A source descendant path retains every actual crossed callback entry. -/
inductive Path [DecidableEq (EdgeKey Symbol Guard)] :
    Syntax Symbol Guard → List Reference → Syntax Symbol Guard → List Reference → List (Crossing Symbol Guard) → Prop where
  | here (expression names) : Path expression names expression names []
  | node {edges symbol guard children child target names current crossings}
      (edge : .mk symbol guard children ∈ edges) (member : child ∈ children)
      (nested : Path child names target current crossings) : Path (.node edges) names target current crossings
  | union {members child target names current crossings} (member : child ∈ members)
      (nested : Path child names target current crossings) : Path (.union members) names target current crossings
  | binder (crossing : Crossing Symbol Guard) {target current crossings}
      (nested : Path crossing.body (crossing.name :: crossing.names) target current crossings) :
      Path (.binder crossing.smart crossing.body) crossing.names target current (crossings ++ [crossing])

/-- Descending again extends the original source path and retains each crossing. -/
theorem Path.trans [DecidableEq (EdgeKey Symbol Guard)]
    {expression middle target : Syntax Symbol Guard} {names middleNames current : List Reference}
    {firstCrossings secondCrossings : List (Crossing Symbol Guard)}
    (first : Path expression names middle middleNames firstCrossings)
    (second : Path middle middleNames target current secondCrossings) :
    Path expression names target current (secondCrossings ++ firstCrossings) := by
  induction first with
  | here => simpa using second
  | node edge member nested ih => exact .node edge member (ih second)
  | union member nested ih => exact .union member (ih second)
  | binder crossing nested ih => simpa only [List.append_assoc] using Path.binder crossing (ih second)

/-- The original miss retains both completed probes and the raw Depth-body call. -/
structure Origin (Symbol Guard : Type) [DecidableEq (EdgeKey Symbol Guard)] (key : NodeKey) where
  smart : Bool
  body : Syntax Symbol Guard
  names : List Reference
  before : State Symbol Guard
  rawDepth : Value Symbol Guard
  afterRawDepth : State Symbol Guard
  depth : Value Symbol Guard
  afterDepth : State Symbol Guard
  ordinary : Value Symbol Guard
  cut : State Symbol Guard
  context : Context before names
  rawDepthDone : build body (.reference .depth :: names.map Value.reference) before = .done rawDepth afterRawDepth
  depthDone : callback body (names.map Value.reference) .depth before = .done depth afterDepth
  ordinaryDone : callback body (names.map Value.reference) (.uninterned depth.depth) afterDepth = .done ordinary cut
  sameKey : key = muKey depth ordinary
  missing : cut.nodes.table key = none
  cutContext : Context cut names
  depthAvailable : Available cut depth
  ordinaryAvailable : Available cut ordinary

/-- The source entry installed by this reservation. -/
def Origin.entry [DecidableEq (EdgeKey Symbol Guard)] (origin : Origin Symbol Guard key) : Interned NodeKey :=
  (Cache.intern origin.cut.nodes key).1

/-- The exact initial state of the active fresh body. -/
def Origin.allocated [DecidableEq (EdgeKey Symbol Guard)] (origin : Origin Symbol Guard key) : State Symbol Guard :=
  {origin.cut with nodes := (Cache.intern origin.cut.nodes key).2}

/-- The active fresh body's original literal lexical inputs. -/
def Origin.localNames [DecidableEq (EdgeKey Symbol Guard)] (origin : Origin Symbol Guard key) : List Reference :=
  .interned origin.entry.identity :: origin.names

/-- Every active permission retains its originating source call and the actual route to the current expression. -/
def Scoped [DecidableEq (EdgeKey Symbol Guard)] (waiting : List NodeKey) (expression : Syntax Symbol Guard)
    (names : List Reference) (state : State Symbol Guard) : Prop :=
  ∀ key ∈ waiting, ∃ origin : Origin Symbol Guard key, ∃ crossings,
    Path origin.body origin.localNames expression names crossings ∧ Grows origin.allocated state ∧
      ∀ crossing ∈ crossings, Grows origin.allocated crossing.before ∧ Grows crossing.start state

/-- Later source effects retain every active source path and crossing history. -/
theorem Scoped.grows [DecidableEq (EdgeKey Symbol Guard)] {expression : Syntax Symbol Guard}
    {before after : State Symbol Guard} (scope : Scoped waiting expression names before)
    (growth : Grows before after) : Scoped waiting expression names after := by
  intro key member
  obtain ⟨origin, crossings, path, initial, traces⟩ := scope key member
  exact ⟨origin, crossings, path, grows_trans initial growth,
    fun crossing included => ⟨(traces crossing included).1, grows_trans (traces crossing included).2 growth⟩⟩

/-- A node child extends the active source path without changing lexical inputs. -/
theorem Scoped.node [DecidableEq (EdgeKey Symbol Guard)] {edges : List (EdgeSyntax Symbol Guard)}
    {symbol : Symbol} {guard : Guard} {children : List (Syntax Symbol Guard)} {child : Syntax Symbol Guard}
    {state : State Symbol Guard} (scope : Scoped waiting (.node edges) names state)
    (edge : .mk symbol guard children ∈ edges) (member : child ∈ children) : Scoped waiting child names state := by
  intro key included
  obtain ⟨origin, crossings, path, growth, traces⟩ := scope key included
  exact ⟨origin, crossings, by simpa using path.trans (.node edge member (.here child names)), growth, traces⟩

/-- A union operand extends the active source path without changing lexical inputs. -/
theorem Scoped.union [DecidableEq (EdgeKey Symbol Guard)] {members : List (Syntax Symbol Guard)}
    {child : Syntax Symbol Guard} {state : State Symbol Guard} (scope : Scoped waiting (.union members) names state)
    (member : child ∈ members) : Scoped waiting child names state := by
  intro key included
  obtain ⟨origin, crossings, path, growth, traces⟩ := scope key included
  exact ⟨origin, crossings, by simpa using path.trans (.union member (.here child names)), growth, traces⟩

/-- An actual callback entry extends every active ancestor's source path. -/
theorem Scoped.enter [DecidableEq (EdgeKey Symbol Guard)] (crossing : Crossing Symbol Guard)
    (scope : Scoped waiting (.binder crossing.smart crossing.body) crossing.names crossing.before) :
    Scoped waiting crossing.body (crossing.name :: crossing.names) crossing.start := by
  intro key included
  obtain ⟨origin, crossings, path, growth, traces⟩ := scope key included
  refine ⟨origin, [crossing] ++ crossings, path.trans (.binder crossing (.here _ _)),
    grows_trans growth crossing.facts.2, ?_⟩
  intro selected member
  rcases List.mem_append.mp member with own | old
  · have same : selected = crossing := List.mem_singleton.mp own
    subst selected
    exact ⟨growth, grows_refl _⟩
  · exact ⟨(traces selected old).1, grows_trans (traces selected old).2 crossing.facts.2⟩

/-- The fresh body's own reservation starts a new path and retains all older paths. -/
theorem Scoped.reserve [DecidableEq (EdgeKey Symbol Guard)] (origin : Origin Symbol Guard key)
    (older : Scoped waiting origin.body origin.localNames origin.allocated) :
    Scoped (key :: waiting) origin.body origin.localNames origin.allocated := by
  intro selected member
  rcases List.mem_cons.mp member with rfl | previous
  · exact ⟨origin, [], .here _ _, grows_refl _, by intro crossing impossible; cases impossible⟩
  · exact older selected previous

end MicroCFTA.InternedActiveSourceOrigins
