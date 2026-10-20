import MicroCFTA.InternedFreshOrdinaryContext
import MicroCFTA.InternedFreshOrdinaryGrowth

/-!
# Repaired active reservations with arbitrary actual captured values

Active origins retain both repaired probes and their complete source
contexts. Actual descendant paths retain Depth, selected ordinary, and
fresh body entries. Captured environments can contain available records.
They are not restricted to lists of literal recursion references.
-/
namespace MicroCFTA.InternedFreshOrdinaryActiveOrigins
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedNestedFacts InternedNestedProvenance
open InternedFreshOrdinaryContext
open InternedBinderProtocol (Reference NodeKey)

/-- Actual repaired callback effects retain valid constructor caches and exact physical growth. -/
theorem callback_growing [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (name : Reference) (state : State Symbol Guard)
    (valid : InternedConstructorTemplates.Valid state) :
    InternedConstructorTemplates.Valid (InternedFreshOrdinaryFacts.callback body environment name state).state ∧
      Grows state (InternedFreshOrdinaryFacts.callback body environment name state).state := by
  unfold InternedFreshOrdinaryFacts.callback
  exact InternedNestedConstruction.bind_correct _ _ state
    (InternedFreshOrdinaryGrowth.build_correct body (.reference name :: environment) state valid)
    (fun value after afterValid => InternedNestedConstruction.work_correct (withoutSelfReference name value) after afterValid)

/-- A callback entry follows the actual source order and reservation result. -/
inductive Entered [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (body : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (before : State Symbol Guard) : Reference → State Symbol Guard → Prop where
  | depth : Entered smart body environment before .depth before
  | ordinary (depth : Value Symbol Guard) (afterDepth : State Symbol Guard)
      (done : InternedFreshOrdinaryFacts.callback body (environment) .depth before = .done depth afterDepth) :
      Entered smart body environment before (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) afterDepth
  | fresh (depth ordinary : Value Symbol Guard) (afterDepth cut : State Symbol Guard)
      (depthDone : InternedFreshOrdinaryFacts.callback body (environment) .depth before = .done depth afterDepth)
      (ordinaryDone : InternedFreshOrdinaryFacts.callback body (environment) (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) afterDepth = .done ordinary cut)
      (missing : cut.nodes.table (muKey depth ordinary) = none) :
      Entered smart body environment before (.interned (Cache.intern cut.nodes (muKey depth ordinary)).1.identity)
        {cut with nodes := (Cache.intern cut.nodes (muKey depth ordinary)).2}

/-- One source crossing records the chosen literal and its exact entry state. -/
structure Crossing (Symbol Guard : Type) [DecidableEq (EdgeKey Symbol Guard)] where
  smart : Bool
  body : Syntax Symbol Guard
  environment : List (Value Symbol Guard)
  before : State Symbol Guard
  name : Reference
  start : State Symbol Guard
  context : Context before environment
  entered : Entered smart body environment before name start

/-- A reservation preserves both semantic tables and all prior literal inputs. -/
theorem reserve_context (key : NodeKey) (state : State Symbol Guard) (environment : List (Value Symbol Guard))
    (context : Context state environment) :
    Context {state with nodes := (Cache.intern state.nodes key).2} environment := context.reserve key

/-- Each recorded entry derives its full local context and actual cache growth. -/
theorem Crossing.facts [DecidableEq (EdgeKey Symbol Guard)] (crossing : Crossing Symbol Guard) :
    Context crossing.start (.reference crossing.name :: crossing.environment) ∧ Grows crossing.before crossing.start := by
  rcases crossing with ⟨smart, body, environment, before, name, start, context, entered⟩
  cases entered with
  | depth => exact ⟨context.local .depth (depth_available before), grows_refl _⟩
  | @ordinary depth afterDepth done =>
      have afterContext : Context start environment := by
        simpa only [done, Outcome.state] using context.callback body .depth (depth_available before)
      have growth : Grows before start := by
        simpa only [done, Outcome.state] using
          (callback_growing body (environment) .depth before context.normal.facts.coherent.valid).2
      exact ⟨afterContext.local _ (ordinary_available start (InternedFreshOrdinaryConstruction.ordinaryLevel depth)), growth⟩
  | @fresh depth ordinary afterDepth cut depthDone ordinaryDone missing =>
      have depthContext : Context afterDepth environment := by
        simpa only [depthDone, Outcome.state] using context.callback body .depth (depth_available before)
      have cutContext : Context cut environment := by
        simpa only [ordinaryDone, Outcome.state] using
          depthContext.callback body (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) (ordinary_available afterDepth (InternedFreshOrdinaryConstruction.ordinaryLevel depth))
      have depthGrowth : Grows before afterDepth := by
        simpa only [depthDone, Outcome.state] using
          (callback_growing body (environment) .depth before context.normal.facts.coherent.valid).2
      have ordinaryGrowth : Grows afterDepth cut := by
        simpa only [ordinaryDone, Outcome.state] using
          (callback_growing body (environment) (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) afterDepth depthContext.normal.facts.coherent.valid).2
      have reserved := reserve_context (muKey depth ordinary) cut environment cutContext
      exact ⟨reserved.local _ (InternedConstructionProvenance.reserve_available _ cut cutContext.normal.facts.coherent cutContext.normal.facts.cached).2,
        grows_trans depthGrowth (grows_trans ordinaryGrowth
          ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩)⟩

/-- A source descendant path retains every actual crossed callback entry. -/
inductive Path [DecidableEq (EdgeKey Symbol Guard)] :
    Syntax Symbol Guard → List (Value Symbol Guard) → Syntax Symbol Guard → List (Value Symbol Guard) → List (Crossing Symbol Guard) → Prop where
  | here (expression environment) : Path expression environment expression environment []
  | node {edges symbol guard children child target environment current crossings}
      (edge : .mk symbol guard children ∈ edges) (member : child ∈ children)
      (nested : Path child environment target current crossings) : Path (.node edges) environment target current crossings
  | union {members child target environment current crossings} (member : child ∈ members)
      (nested : Path child environment target current crossings) : Path (.union members) environment target current crossings
  | binder (crossing : Crossing Symbol Guard) {target current crossings}
      (nested : Path crossing.body (.reference crossing.name :: crossing.environment) target current crossings) :
      Path (.binder crossing.smart crossing.body) crossing.environment target current (crossings ++ [crossing])

/-- Descending again extends the original source path and retains each crossing. -/
theorem Path.trans [DecidableEq (EdgeKey Symbol Guard)]
    {expression middle target : Syntax Symbol Guard} {environment middleInputs current : List (Value Symbol Guard)}
    {firstCrossings secondCrossings : List (Crossing Symbol Guard)}
    (first : Path expression environment middle middleInputs firstCrossings)
    (second : Path middle middleInputs target current secondCrossings) :
    Path expression environment target current (secondCrossings ++ firstCrossings) := by
  induction first with
  | here => simpa using second
  | node edge member nested ih => exact .node edge member (ih second)
  | union member nested ih => exact .union member (ih second)
  | binder crossing nested ih => simpa only [List.append_assoc] using Path.binder crossing (ih second)

/-- The actual crossed references form the complete lexical prefix before unchanged captured values. -/
theorem Path.inputs [DecidableEq (EdgeKey Symbol Guard)]
    {expression target : Syntax Symbol Guard} {environment current : List (Value Symbol Guard)}
    {crossings : List (Crossing Symbol Guard)} (path : Path expression environment target current crossings) :
    current = crossings.map (fun crossing => Value.reference crossing.name) ++ environment := by
  induction path with
  | here => rfl
  | node edge member nested ih | union member nested ih => exact ih
  | binder crossing nested ih => simpa [List.map_append, List.append_assoc] using ih

/-- The original miss retains both completed probes and the raw Depth-body call. -/
structure Origin (Symbol Guard : Type) [DecidableEq (EdgeKey Symbol Guard)] (key : NodeKey) where
  smart : Bool
  body : Syntax Symbol Guard
  environment : List (Value Symbol Guard)
  before : State Symbol Guard
  rawDepth : Value Symbol Guard
  afterRawDepth : State Symbol Guard
  depth : Value Symbol Guard
  afterDepth : State Symbol Guard
  ordinary : Value Symbol Guard
  cut : State Symbol Guard
  context : Context before environment
  rawDepthDone : InternedFreshOrdinaryConstruction.build body (.reference .depth :: environment) before = .done rawDepth afterRawDepth
  depthDone : InternedFreshOrdinaryFacts.callback body (environment) .depth before = .done depth afterDepth
  ordinaryDone : InternedFreshOrdinaryFacts.callback body (environment) (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) afterDepth = .done ordinary cut
  sameKey : key = muKey depth ordinary
  missing : cut.nodes.table key = none
  cutContext : Context cut environment
  depthAvailable : Available cut depth
  ordinaryAvailable : Available cut ordinary

/-- The source entry installed by this reservation. -/
def Origin.entry [DecidableEq (EdgeKey Symbol Guard)] (origin : Origin Symbol Guard key) : Interned NodeKey :=
  (Cache.intern origin.cut.nodes key).1

/-- The exact initial state of the active fresh body. -/
def Origin.allocated [DecidableEq (EdgeKey Symbol Guard)] (origin : Origin Symbol Guard key) : State Symbol Guard :=
  {origin.cut with nodes := (Cache.intern origin.cut.nodes key).2}

/-- The active fresh body's original literal lexical inputs. -/
def Origin.localInputs [DecidableEq (EdgeKey Symbol Guard)] (origin : Origin Symbol Guard key) : List (Value Symbol Guard) :=
  .reference (.interned origin.entry.identity) :: origin.environment

/-- Equal actual pair keys identify both complete original probe records after source growth. -/
theorem Origin.probes_eq [DecidableEq (EdgeKey Symbol Guard)] (origin : Origin Symbol Guard key)
    (final : State Symbol Guard) (coherent : Coherent final) (growth : Grows origin.allocated final)
    (depth ordinary : Value Symbol Guard) (depthAvailable : Available final depth) (ordinaryAvailable : Available final ordinary)
    (sameKey : key = muKey depth ordinary) : depth = origin.depth ∧ ordinary = origin.ordinary := by
  have allocated : Grows origin.cut origin.allocated :=
    ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
  have completeGrowth := grows_trans allocated growth
  have references : depth.referenceOf = origin.depth.referenceOf ∧ ordinary.referenceOf = origin.ordinary.referenceOf := by
    simpa only [muKey, NodeKey.mu.injEq, InternedBinderProtocol.MuKey.mk.injEq] using sameKey.symm.trans origin.sameKey
  exact ⟨InternedFreshProbeKeys.resident_reference_injective final coherent depth origin.depth depthAvailable.resident
      (InternedFreshProbeKeys.resident_grows origin.cut final completeGrowth origin.depth origin.depthAvailable.resident) references.1,
    InternedFreshProbeKeys.resident_reference_injective final coherent ordinary origin.ordinary ordinaryAvailable.resident
      (InternedFreshProbeKeys.resident_grows origin.cut final completeGrowth origin.ordinary origin.ordinaryAvailable.resident) references.2⟩

/-- Every active permission retains its originating source call and the actual route to the current expression. -/
def Scoped [DecidableEq (EdgeKey Symbol Guard)] (waiting : List NodeKey) (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) : Prop :=
  ∀ key ∈ waiting, ∃ origin : Origin Symbol Guard key, ∃ crossings,
    Path origin.body origin.localInputs expression environment crossings ∧ Grows origin.allocated state ∧
      ∀ crossing ∈ crossings, Grows origin.allocated crossing.before ∧ Grows crossing.start state

/-- Later source effects retain every active source path and crossing history. -/
theorem Scoped.grows [DecidableEq (EdgeKey Symbol Guard)] {expression : Syntax Symbol Guard}
    {before after : State Symbol Guard} (scope : Scoped waiting expression environment before)
    (growth : Grows before after) : Scoped waiting expression environment after := by
  intro key member
  obtain ⟨origin, crossings, path, initial, traces⟩ := scope key member
  exact ⟨origin, crossings, path, grows_trans initial growth,
    fun crossing included => ⟨(traces crossing included).1, grows_trans (traces crossing included).2 growth⟩⟩

/-- A node child extends the active source path without changing lexical inputs. -/
theorem Scoped.node [DecidableEq (EdgeKey Symbol Guard)] {edges : List (EdgeSyntax Symbol Guard)}
    {symbol : Symbol} {guard : Guard} {children : List (Syntax Symbol Guard)} {child : Syntax Symbol Guard}
    {state : State Symbol Guard} (scope : Scoped waiting (.node edges) environment state)
    (edge : .mk symbol guard children ∈ edges) (member : child ∈ children) : Scoped waiting child environment state := by
  intro key included
  obtain ⟨origin, crossings, path, growth, traces⟩ := scope key included
  exact ⟨origin, crossings, by simpa using path.trans (.node edge member (.here child environment)), growth, traces⟩

/-- A union operand extends the active source path without changing lexical inputs. -/
theorem Scoped.union [DecidableEq (EdgeKey Symbol Guard)] {members : List (Syntax Symbol Guard)}
    {child : Syntax Symbol Guard} {state : State Symbol Guard} (scope : Scoped waiting (.union members) environment state)
    (member : child ∈ members) : Scoped waiting child environment state := by
  intro key included
  obtain ⟨origin, crossings, path, growth, traces⟩ := scope key included
  exact ⟨origin, crossings, by simpa using path.trans (.union member (.here child environment)), growth, traces⟩

/-- An actual callback entry extends every active ancestor's source path. -/
theorem Scoped.enter [DecidableEq (EdgeKey Symbol Guard)] (crossing : Crossing Symbol Guard)
    (scope : Scoped waiting (.binder crossing.smart crossing.body) crossing.environment crossing.before) :
    Scoped waiting crossing.body (.reference crossing.name :: crossing.environment) crossing.start := by
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
    (older : Scoped waiting origin.body origin.localInputs origin.allocated) :
    Scoped (key :: waiting) origin.body origin.localInputs origin.allocated := by
  intro selected member
  rcases List.mem_cons.mp member with rfl | previous
  · exact ⟨origin, [], .here _ _, grows_refl _, by intro crossing impossible; cases impossible⟩
  · exact older selected previous

end MicroCFTA.InternedFreshOrdinaryActiveOrigins
