import MicroCFTA.InternedFreeAbsenceContext
import MicroCFTA.InternedProfileTraceSites
import MicroCFTA.InternedRequestAgreement

/-!
# Actual completed sites along either normalized probe

Each crossed binder executes both normalized callbacks before its cache
request. A route chooses Depth or the actual Unint level at each crossing.
The witness retains each executed depth callback and its lexical context.
It does not equate Unint levels from different executions.
-/
namespace MicroCFTA.InternedProbeChoiceSites
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedNestedMissReadback InternedNestedSpecialization InternedFreeAbsenceContext
open InternedBinderProtocol (Reference)

/-- A source site records probe choices in the order of its resulting lexical initialGrowth. -/
inductive Site : Syntax Symbol Guard → Syntax Symbol Guard → List Bool → Prop where
  | here (expression) : Site expression expression []
  | node {edges symbol guard children child target choices}
      (edge : .mk symbol guard children ∈ edges) (member : child ∈ children)
      (nested : Site child target choices) : Site (.node edges) target choices
  | union {members child target choices} (member : child ∈ members)
      (nested : Site child target choices) : Site (.union members) target choices
  | binder {smart body target choices} (ordinary : Bool) (nested : Site body target choices) :
      Site (.binder smart body) target (choices ++ [ordinary])

/-- One actual crossing retains the depth call that determines its optional Unint argument. -/
structure Crossing (Symbol Guard : Type) [DecidableEq (EdgeKey Symbol Guard)] where
  ordinary : Bool
  body : Syntax Symbol Guard
  names : List Reference
  before : State Symbol Guard
  depth : Value Symbol Guard
  afterDepth : State Symbol Guard
  context : Context before names
  depthDone : callback body (names.map Value.reference) .depth before = .done depth afterDepth

/-- The chosen probe name uses the depth value from this exact source execution. -/
def Crossing.name [DecidableEq (EdgeKey Symbol Guard)] (crossing : Crossing Symbol Guard) : Reference :=
  if crossing.ordinary then .uninterned crossing.depth.depth else .depth

/-- A known later free-name table certifies every earlier complete record. -/
theorem context_from_later (names : List Reference) (before after : State Symbol Guard)
    (context : InternedProfileTraceSites.Context before (names.map Value.reference))
    (heap : InternedFreeNameHeap.Heap after) (growth : Grows before after) : Context before names := by
  refine ⟨context.normal, context.inputs, context.heap, ?_⟩
  intro key entry body depth ordinary present
  exact heap key entry body depth ordinary (growth.nodeRecords key _ present)

/-- A site with no crossed binder inherits the full source context at its actual initialGrowth. -/
theorem zero_site [DecidableEq (EdgeKey Symbol Guard)] {expression target : Syntax Symbol Guard}
    (site : InternedNestedTraceSites.Site expression target 0) (names : List Reference)
    (before final : State Symbol Guard) (value : Value Symbol Guard) (context : Context before names)
    (completed : build expression (names.map Value.reference) before = .done value final) :
    ∃ start result finish, build target (names.map Value.reference) start = .done result finish ∧
      Context start names ∧ Grows before start ∧ Grows finish final := by
  obtain ⟨start, result, finish, done, ctx, initialGrowth, suffix⟩ :=
    InternedProfileTraceSites.completed_site_checked site _ before value final context.profileContext completed
  simp only [List.replicate_zero, List.nil_append] at done ctx
  have targetGrowth : Grows start finish := by
    simpa only [done, Outcome.state] using
      (build_correct target (names.map Value.reference) start ctx.normal.facts.coherent.valid).2
  have finalHeap : InternedFreeNameHeap.Heap final := by
    simpa only [completed, Outcome.state] using (context.build expression).freeNames
  exact ⟨start, result, finish, done,
    context_from_later names start final ctx finalHeap (grows_trans targetGrowth suffix), initialGrowth, suffix⟩

/-- Every selected probe route occurs in the actual completed enclosing execution. -/
theorem completed_site [DecidableEq (EdgeKey Symbol Guard)]
    {expression target : Syntax Symbol Guard} {choices : List Bool} (site : Site expression target choices)
    (names : List Reference) (before final : State Symbol Guard) (value : Value Symbol Guard)
    (context : Context before names)
    (completed : build expression (names.map Value.reference) before = .done value final) :
    ∃ crossings : List (Crossing Symbol Guard), ∃ start result finish,
      crossings.map Crossing.ordinary = choices ∧
      build target ((crossings.map Crossing.name ++ names).map Value.reference) start = .done result finish ∧
      Context start (crossings.map Crossing.name ++ names) ∧ Grows before start ∧ Grows finish final := by
  induction site generalizing names before final value with
  | here expression =>
      exact ⟨[], before, value, final, rfl, by simpa using completed, by simpa using context, grows_refl _, grows_refl _⟩
  | @node edges symbol guard children child target choices edge member nested ih =>
      obtain ⟨childStart, childValue, childEnd, childDone, childContext, initialGrowth, suffix⟩ :=
        zero_site (.node edge member (.here child)) names before final value context completed
      obtain ⟨crossings, start, result, finish, flags, done, ctx, front, back⟩ :=
        ih names childStart childEnd childValue childContext childDone
      exact ⟨crossings, start, result, finish, flags, done, ctx, grows_trans initialGrowth front, grows_trans back suffix⟩
  | @union members child target choices member nested ih =>
      obtain ⟨childStart, childValue, childEnd, childDone, childContext, initialGrowth, suffix⟩ :=
        zero_site (.union member (.here child)) names before final value context completed
      obtain ⟨crossings, start, result, finish, flags, done, ctx, front, back⟩ :=
        ih names childStart childEnd childValue childContext childDone
      exact ⟨crossings, start, result, finish, flags, done, ctx, grows_trans initialGrowth front, grows_trans back suffix⟩
  | @binder smart body target choices ordinary nested ih =>
      rw [build] at completed
      change ((callback body (names.map Value.reference) .depth before).bind fun depth middle =>
        (callback body (names.map Value.reference) (.uninterned depth.depth) middle).bind fun second after =>
          request smart depth second (callback body (names.map Value.reference)) after) = .done value final at completed
      obtain ⟨depth, afterDepth, depthDone, later⟩ := bind_done _ _ _ _ completed
      obtain ⟨second, afterSecond, secondDone, requestDone⟩ := bind_done _ _ _ _ later
      have depthContext : Context afterDepth names := by
        simpa only [depthDone, Outcome.state] using context.callback body .depth (depth_available before)
      have secondContext : Context afterSecond names := by
        simpa only [secondDone, Outcome.state] using
          depthContext.callback body (.uninterned depth.depth) (ordinary_available afterDepth depth.depth)
      have depthGrowth : Grows before afterDepth := by
        simpa only [depthDone, Outcome.state] using
          (InternedRequestAgreement.callback_growing body (names.map Value.reference) .depth before context.normal.facts.coherent.valid).2
      have secondGrowth : Grows afterDepth afterSecond := by
        simpa only [secondDone, Outcome.state] using
          (InternedRequestAgreement.callback_growing body (names.map Value.reference) (.uninterned depth.depth)
            afterDepth depthContext.normal.facts.coherent.valid).2
      have finalGrowth : Grows afterSecond final := by
        simpa only [requestDone, Outcome.state] using
          (request_correct smart depth second (callback body (names.map Value.reference))
            (InternedRequestAgreement.callback_growing body (names.map Value.reference))
            afterSecond secondContext.normal.facts.coherent.valid).2
      let crossing : Crossing Symbol Guard := ⟨ordinary, body, names, before, depth, afterDepth, context, depthDone⟩
      have selected : ∃ selectedStart selectedValue selectedEnd,
          callback body (names.map Value.reference) crossing.name selectedStart = .done selectedValue selectedEnd ∧
          Context selectedStart names ∧ Available selectedStart (.reference crossing.name) ∧
          Grows before selectedStart ∧ Grows selectedEnd final := by
        cases ordinary with
        | false => exact ⟨before, depth, afterDepth, depthDone, context, depth_available before,
            grows_refl _, grows_trans secondGrowth finalGrowth⟩
        | true => exact ⟨afterDepth, second, afterSecond, secondDone, depthContext,
            ordinary_available afterDepth depth.depth, depthGrowth, finalGrowth⟩
      obtain ⟨selectedStart, selectedValue, selectedEnd, selectedDone, selectedContext, argument, initialGrowth, suffix⟩ := selected
      obtain ⟨raw, afterRaw, rawDone, filterDone⟩ := bind_done _ _ _ _ selectedDone
      have localContext := selectedContext.local crossing.name argument
      have afterRawContext : Context afterRaw (crossing.name :: names) := by
        simpa only [List.map_cons, rawDone, Outcome.state] using localContext.build body
      have filterGrowth : Grows afterRaw selectedEnd := by
        simpa only [filterDone, Outcome.state] using
          (work_correct (withoutSelfReference crossing.name raw) afterRaw afterRawContext.normal.facts.coherent.valid).2
      obtain ⟨crossings, start, result, finish, flags, done, ctx, front, back⟩ :=
        ih (crossing.name :: names) selectedStart afterRaw raw localContext (by simpa only [List.map_cons] using rawDone)
      refine ⟨crossings ++ [crossing], start, result, finish, ?_, ?_, ?_, grows_trans initialGrowth front,
        grows_trans back (grows_trans filterGrowth suffix)⟩
      · simp [List.map_append, flags, crossing]
      · simpa only [List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append] using done
      · simpa only [List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append] using ctx

end MicroCFTA.InternedProbeChoiceSites
