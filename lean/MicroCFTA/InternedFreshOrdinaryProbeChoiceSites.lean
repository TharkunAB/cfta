import MicroCFTA.InternedFreshOrdinaryCompletedSites
import MicroCFTA.InternedFreshOrdinaryActiveOrigins
import MicroCFTA.InternedProbeChoiceSites

/-!
# Completed probe routes with the repaired ordinary policy

A completed enclosing call contains both actual probes at every binder.
The selected route retains its actual source bodies and computed ordinary
levels. Captured environments can contain arbitrary available records.
-/
namespace MicroCFTA.InternedFreshOrdinaryProbeChoiceSites
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome work request work_correct request_correct)
open InternedNestedProvenance (depth_available ordinary_available)
open InternedNestedSpecialization
open InternedFreshOrdinaryContext InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedProbeChoiceSites (Route)
open InternedBinderProtocol (Reference)

/-- One actual crossing retains the depth call that determines its optional Unint argument. -/
structure Crossing (Symbol Guard : Type) [DecidableEq (EdgeKey Symbol Guard)] where
  ordinary : Bool
  body : Syntax Symbol Guard
  environment : List (Value Symbol Guard)
  before : State Symbol Guard
  depth : Value Symbol Guard
  afterDepth : State Symbol Guard
  context : Context before environment
  depthDone : callback body environment .depth before = .done depth afterDepth

/-- The chosen probe name uses the depth value from this exact source execution. -/
def Crossing.name [DecidableEq (EdgeKey Symbol Guard)] (crossing : Crossing Symbol Guard) : Reference :=
  if crossing.ordinary then .uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel crossing.depth) else .depth

/-- Each crossed callback captures exactly the outer crossed references and the original lexical inputs. -/
def Captures [DecidableEq (EdgeKey Symbol Guard)] (environment : List (Value Symbol Guard)) : List (Crossing Symbol Guard) → Prop
  | [] => True
  | first :: rest => first.environment = rest.map (fun crossing => Value.reference crossing.name) ++ environment ∧ Captures environment rest

/-- An outer callback extends the common captured suffix for all inner crossings. -/
theorem captures_snoc [DecidableEq (EdgeKey Symbol Guard)] (environment : List (Value Symbol Guard))
    (crossings : List (Crossing Symbol Guard)) (outer : Crossing Symbol Guard) :
    Captures environment (crossings ++ [outer]) ↔
      outer.environment = environment ∧ Captures (.reference outer.name :: environment) crossings := by
  induction crossings with
  | nil => simp [Captures]
  | cons first rest ih =>
      simp [Captures, List.map_append, List.append_assoc, ih, and_left_comm]

/-- Every selected completed route retains exact source bodies and the captured suffix at each actual crossing. -/
theorem completed_scoped_route [DecidableEq (EdgeKey Symbol Guard)]
    {expression target : Syntax Symbol Guard} {choices : List (Syntax Symbol Guard × Bool)}
    (site : Route expression target choices)
    (environment : List (Value Symbol Guard)) (before final : State Symbol Guard) (value : Value Symbol Guard)
    (context : Context before environment)
    (completed : build expression environment before = .done value final) :
    ∃ crossings : List (Crossing Symbol Guard), ∃ start result finish,
      crossings.map (fun crossing => (crossing.body, crossing.ordinary)) = choices ∧
      build target (crossings.map (fun crossing => Value.reference crossing.name) ++ environment) start = .done result finish ∧
      Context start (crossings.map (fun crossing => Value.reference crossing.name) ++ environment) ∧ Grows before start ∧ Grows finish final ∧
      Captures environment crossings ∧
      ∀ crossing ∈ crossings, Grows before crossing.before ∧ Grows crossing.afterDepth final := by
  induction site generalizing environment before final value with
  | here expression =>
      exact ⟨[], before, value, final, rfl, by simpa using completed, by simpa using context, grows_refl _, grows_refl _, True.intro, by simp⟩
  | @node edges symbol guard children child target choices edge member nested ih =>
      obtain ⟨childStart, childValue, childEnd, childDone, childContext, initialGrowth, suffix⟩ :=
        InternedFreshOrdinaryCompletedSites.zero_site (.node edge member (.here child)) rfl environment before final value context completed
      obtain ⟨crossings, start, result, finish, flags, done, ctx, front, back, captures, traces⟩ :=
        ih environment childStart childEnd childValue childContext childDone
      refine ⟨crossings, start, result, finish, flags, done, ctx, grows_trans initialGrowth front, grows_trans back suffix, captures, ?_⟩
      intro crossing member
      exact ⟨grows_trans initialGrowth (traces crossing member).1, grows_trans (traces crossing member).2 suffix⟩
  | @union members child target choices member nested ih =>
      obtain ⟨childStart, childValue, childEnd, childDone, childContext, initialGrowth, suffix⟩ :=
        InternedFreshOrdinaryCompletedSites.zero_site (.union member (.here child)) rfl environment before final value context completed
      obtain ⟨crossings, start, result, finish, flags, done, ctx, front, back, captures, traces⟩ :=
        ih environment childStart childEnd childValue childContext childDone
      refine ⟨crossings, start, result, finish, flags, done, ctx, grows_trans initialGrowth front, grows_trans back suffix, captures, ?_⟩
      intro crossing member
      exact ⟨grows_trans initialGrowth (traces crossing member).1, grows_trans (traces crossing member).2 suffix⟩
  | @binder smart body target choices ordinary nested ih =>
      rw [build] at completed
      change ((callback body environment .depth before).bind fun depth middle =>
        (callback body environment (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) middle).bind fun second after =>
          request smart depth second (callback body environment) after) = .done value final at completed
      obtain ⟨depth, afterDepth, depthDone, later⟩ := bind_done _ _ _ _ completed
      obtain ⟨second, afterSecond, secondDone, requestDone⟩ := bind_done _ _ _ _ later
      have depthContext : Context afterDepth environment := by
        simpa only [depthDone, Outcome.state] using context.callback body .depth (depth_available before)
      have secondContext : Context afterSecond environment := by
        simpa only [secondDone, Outcome.state] using
          depthContext.callback body (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) (ordinary_available afterDepth (InternedFreshOrdinaryConstruction.ordinaryLevel depth))
      have depthGrowth : Grows before afterDepth := by
        simpa only [depthDone, Outcome.state] using
          (InternedFreshOrdinaryActiveOrigins.callback_growing body environment .depth before context.normal.facts.coherent.valid).2
      have secondGrowth : Grows afterDepth afterSecond := by
        simpa only [secondDone, Outcome.state] using
          (InternedFreshOrdinaryActiveOrigins.callback_growing body environment (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth))
            afterDepth depthContext.normal.facts.coherent.valid).2
      have finalGrowth : Grows afterSecond final := by
        simpa only [requestDone, Outcome.state] using
          (request_correct smart depth second (callback body environment)
            (InternedFreshOrdinaryActiveOrigins.callback_growing body environment)
            afterSecond secondContext.normal.facts.coherent.valid).2
      let crossing : Crossing Symbol Guard := ⟨ordinary, body, environment, before, depth, afterDepth, context, depthDone⟩
      have selected : ∃ selectedStart selectedValue selectedEnd,
          callback body environment crossing.name selectedStart = .done selectedValue selectedEnd ∧
          Context selectedStart environment ∧ Available selectedStart (.reference crossing.name) ∧
          Grows before selectedStart ∧ Grows selectedEnd final := by
        cases ordinary with
        | false => exact ⟨before, depth, afterDepth, depthDone, context, depth_available before,
            grows_refl _, grows_trans secondGrowth finalGrowth⟩
        | true => exact ⟨afterDepth, second, afterSecond, secondDone, depthContext,
            ordinary_available afterDepth (InternedFreshOrdinaryConstruction.ordinaryLevel depth), depthGrowth, finalGrowth⟩
      obtain ⟨selectedStart, selectedValue, selectedEnd, selectedDone, selectedContext, argument, initialGrowth, suffix⟩ := selected
      obtain ⟨raw, afterRaw, rawDone, filterDone⟩ := bind_done _ _ _ _ selectedDone
      have localContext := selectedContext.local crossing.name argument
      have afterRawContext : Context afterRaw (.reference crossing.name :: environment) := by
        simpa only [List.map_cons, rawDone, Outcome.state] using localContext.build body
      have filterGrowth : Grows afterRaw selectedEnd := by
        simpa only [filterDone, Outcome.state] using
          (work_correct (withoutSelfReference crossing.name raw) afterRaw afterRawContext.normal.facts.coherent.valid).2
      obtain ⟨crossings, start, result, finish, flags, done, ctx, front, back, captures, traces⟩ :=
        ih (.reference crossing.name :: environment) selectedStart afterRaw raw localContext (by simpa only [List.map_cons] using rawDone)
      refine ⟨crossings ++ [crossing], start, result, finish, ?_, ?_, ?_, grows_trans initialGrowth front,
        grows_trans back (grows_trans filterGrowth suffix), ?_, ?_⟩
      · simp [List.map_append, flags, crossing]
      · simpa only [List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append] using done
      · simpa only [List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append] using ctx
      · exact (captures_snoc environment crossings crossing).mpr ⟨rfl, captures⟩
      · intro selected member
        rcases List.mem_append.mp member with nestedMember | ownMember
        · exact ⟨grows_trans initialGrowth (traces selected nestedMember).1,
            grows_trans (traces selected nestedMember).2 (grows_trans filterGrowth suffix)⟩
        · have equal : selected = crossing := List.mem_singleton.mp ownMember
          subst selected
          exact ⟨grows_refl _, grows_trans secondGrowth finalGrowth⟩

/-- Every selected route retains exact source bodies in the actual completed execution. -/
theorem completed_route [DecidableEq (EdgeKey Symbol Guard)]
    {expression target : Syntax Symbol Guard} {choices : List (Syntax Symbol Guard × Bool)}
    (site : Route expression target choices)
    (environment : List (Value Symbol Guard)) (before final : State Symbol Guard) (value : Value Symbol Guard)
    (context : Context before environment) (completed : build expression environment before = .done value final) :
    ∃ crossings : List (Crossing Symbol Guard), ∃ start result finish,
      crossings.map (fun crossing => (crossing.body, crossing.ordinary)) = choices ∧
      build target (crossings.map (fun crossing => Value.reference crossing.name) ++ environment) start = .done result finish ∧
      Context start (crossings.map (fun crossing => Value.reference crossing.name) ++ environment) ∧ Grows before start ∧ Grows finish final ∧
      ∀ crossing ∈ crossings, Grows before crossing.before ∧ Grows crossing.afterDepth final := by
  obtain ⟨crossings, start, result, finish, flags, done, ctx, front, back, _, traces⟩ :=
    completed_scoped_route site environment before final value context completed
  exact ⟨crossings, start, result, finish, flags, done, ctx, front, back, traces⟩

end MicroCFTA.InternedFreshOrdinaryProbeChoiceSites
