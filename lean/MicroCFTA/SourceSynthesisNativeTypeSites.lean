import MicroCFTA.SourceSynthesisRecursiveOrigins
import MicroCFTA.SourceSynthesisLabelProgramBuildRoles
import MicroCFTA.SourceCurrentNativeOriginalPublicationTrace
import MicroCFTA.SourceCurrentNativeMuPublicationCallbacks
import MicroCFTA.SourceCurrentHereditaryConstruction

/-!
# Original synthesis Mu bodies in a mixed heap

Actual original publication order identifies every cached Mu body.
The source restriction checks binder bodies only. Program row guards
outside these bodies remain unrestricted. Earlier actual publications
supply the conditional certificate used by a stored callback winner.

These laws establish an initial constructor certificate. They do not
establish its preservation through arbitrary later native requests or
classify every reached Type value.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeSites
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryFacts (callback build_verified callback_verified)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceEqualityConstraintOrigins (guards childGuards edgeGuards)
open SourceSynthesisRecursiveOrigins (PlainMu ManyPlainMu EdgesPlainMu)
open SourceCurrentHereditaryConstruction (MuStored)
open SourceCurrentNativeOriginalPublicationTrace (events)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentConstrainedCapSourceHistory (Context)

section Generic
variable {Symbol Guard : Type}

private theorem many_member (top : Guard) (children : List (Syntax Symbol Guard))
    (clean : ManyPlainMu top children) (child : Syntax Symbol Guard) (member : child ∈ children) :
    PlainMu top child := by
  induction children with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact clean.1
      · exact ih clean.2 later

private theorem row_child (top : Guard) (rows : List (EdgeSyntax Symbol Guard))
    (clean : EdgesPlainMu top rows) (symbol : Symbol) (guard : Guard)
    (children : List (Syntax Symbol Guard)) (member : .mk symbol guard children ∈ rows)
    (child : Syntax Symbol Guard) (inside : child ∈ children) : PlainMu top child := by
  induction rows with
  | nil => cases member
  | cons first rest ih =>
      cases first with
      | mk name ownGuard ownChildren =>
          rcases List.mem_cons.mp member with same | later
          · cases same
            exact many_member top children clean.1 child inside
          · exact ih clean.2 later

private theorem path_clean [DecidableEq (EdgeKey Symbol Guard)] (top : Guard)
    {root expression : Syntax Symbol Guard} {inputs environment : List (Value Symbol Guard)}
    {crossings : List (InternedFreshOrdinaryActiveOrigins.Crossing Symbol Guard)}
    (path : InternedFreshOrdinaryActiveOrigins.Path root inputs expression environment crossings)
    (clean : PlainMu top root) : PlainMu top expression := by
  induction path with
  | here => exact clean
  | node edge member nested ih => exact ih (row_child top _ clean _ _ _ edge _ member)
  | union member nested ih => exact ih (many_member top _ clean _ member)
  | binder crossing nested ih => exact ih clean.2

/-- Every cached Mu in the actual closed source build has a Top-annotated body. -/
theorem build_mu_bodies [DecidableEq (EdgeKey Symbol Guard)]
    (top : Guard) (expression : Syntax Symbol Guard) (clean : PlainMu top expression)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : build expression [] empty = .done value heap) :
    ∀ key entry body depth ordinary, heap.nodeRecords key = some (.mu entry body depth ordinary) →
      Annotated (fun guard => guard = top) body := by
  obtain ⟨path, sites, writers, earlier⟩ :=
    SourceCurrentNativeOriginalPublicationTrace.build_trace_writers expression [] empty
      SourceCurrentConstrainedCapSourceHistory.empty_context
      (by intro key entry body depth ordinary absent; cases absent) value heap built
  have bodies : ∀ index : Nat, ∀ event : @Publication Symbol Guard _,
      (events path)[index]? = some event → Annotated (fun guard => guard = top) event.body := by
    intro index
    induction index using Nat.strongRecOn with
    | ind index ih =>
      intro event selected
      obtain ⟨crossings, sourcePath, _⟩ := sites index event selected
      have bodyGuards : ∀ guard ∈ guards event.expression, guard = top :=
        (path_clean top sourcePath clean).1
      have captures : ∀ item ∈ event.environment, Annotated (fun guard => guard = top) item := by
        intro item member
        rw [sourcePath.inputs] at member
        rcases List.mem_append.mp member with localValue | absent
        · obtain ⟨crossing, _, rfl⟩ := List.mem_map.mp localValue
          exact .reference _
        · cases absent
      obtain ⟨_, cutContext, bodyContext⟩ := SourceCurrentNativeMuPublicationCallbacks.contexts event
      have argument : Available event.allocated (.reference (.interned event.entry.identity)) :=
        (InternedConstructionProvenance.reserve_available event.key event.cut
          cutContext.base.normal.facts.coherent cutContext.base.normal.facts.cached).2
      have inputs := (bodyContext.local (.interned event.entry.identity) argument).base
      have physical := callback_verified event.expression event.environment (.interned event.entry.identity)
        event.allocated inputs.normal.facts inputs.inputs
      have bodyDone : callback event.expression event.environment (.interned event.entry.identity)
          event.allocated = .done event.body event.afterBody := event.bodyDone
      have growth : Grows event.allocated event.afterBody := by
        simpa only [bodyDone, Outcome.state] using physical.growth
      have stored : MuStored (fun guard => guard = top) event.allocated := by
        intro key entry body depth ordinary present _ _
        obtain ⟨earlierIndex, own, less, ownSelected, _, _, same, _⟩ :=
          earlier index event selected key entry body depth ordinary (growth.nodeRecords key _ present)
        have bodySame : body = own.body := (Value.mu.inj same).2.1
        rw [bodySame]
        exact ih earlierIndex less own ownSelected
      obtain ⟨raw, middle, rawDone, filtered⟩ :=
        SourceCurrentNativeMuPublicationCallbacks.callback_raw event.expression event.environment
          (.interned event.entry.identity) event.allocated event.body event.afterBody event.bodyDone
      have allowed := SourceEqualityConstraintOrigins.allowed (fun guard => guard = top)
        event.expression bodyGuards
      have annotations : ∀ item ∈ .reference (.interned event.entry.identity) :: event.environment,
          Annotated (fun guard => guard = top) item := by
        intro item member
        rcases List.mem_cons.mp member with rfl | member
        · exact .reference _
        · exact captures item member
      have checked := SourceCurrentHereditaryConstruction.build (fun guard => guard = top)
        event.expression _ event.allocated inputs.normal.facts inputs.inputs allowed annotations stored
      have rawAnnotated := checked.result raw middle rawDone
      have rawPhysical := build_verified event.expression _ event.allocated inputs.normal.facts inputs.inputs
      have middleFacts : Facts middle := by simpa only [rawDone, Outcome.state] using rawPhysical.facts
      have middleStored : MuStored (fun guard => guard = top) middle := by
        simpa only [rawDone, Outcome.state] using checked.stored
      have filteredCheck := SourceCurrentHereditaryConstruction.filter_checked (fun guard => guard = top)
        (.interned event.entry.identity) raw middle middleFacts (rawPhysical.result raw middle rawDone)
        rawAnnotated middleStored
      exact filteredCheck.result event.body event.afterBody (by
        simp only [InternedNestedConstruction.work, filtered])
  intro key entry body depth ordinary present
  obtain ⟨index, event, selected, _, _, same, _⟩ := writers key entry body depth ordinary present
  have bodySame : body = event.body := (Value.mu.inj same).2.1
  rw [bodySame]
  exact bodies index event selected
end Generic

section Source
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression Row firstOrderRaw)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisProgramBuildRolesGeneric (mapSyntax mapChildren mapEdges)

mutual
private theorem mapped {Symbol : Type} (literal : String → Symbol) (expression : Expression) :
    guards (mapSyntax literal expression) = guards expression ∧
      (PlainMu top expression → PlainMu top (mapSyntax literal expression)) := by
  cases expression with
  | empty | var => exact ⟨rfl, fun _ => trivial⟩
  | node rows => exact mapped_rows literal rows
  | union members => exact mapped_children literal members
  | binder smart body =>
      have recursive := mapped literal body
      refine ⟨recursive.1, fun clean => ⟨?_, recursive.2 clean.2⟩⟩
      simpa only [recursive.1] using clean.1
termination_by sizeOf expression

private theorem mapped_children {Symbol : Type} (literal : String → Symbol) (expressions : List Expression) :
    childGuards (mapChildren literal expressions) = childGuards expressions ∧
      (ManyPlainMu top expressions → ManyPlainMu top (mapChildren literal expressions)) := by
  cases expressions with
  | nil => exact ⟨rfl, fun _ => trivial⟩
  | cons first rest =>
      have own := mapped literal first
      have tail := mapped_children literal rest
      constructor
      · simp only [mapChildren, childGuards, own.1, tail.1]
      · exact fun clean => ⟨own.2 clean.1, tail.2 clean.2⟩
termination_by sizeOf expressions

private theorem mapped_rows {Symbol : Type} (literal : String → Symbol) (rows : List Row) :
    edgeGuards (mapEdges literal rows) = edgeGuards rows ∧
      (EdgesPlainMu top rows → EdgesPlainMu top (mapEdges literal rows)) := by
  cases rows with
  | nil => exact ⟨rfl, fun _ => trivial⟩
  | cons row rest =>
      cases row with
      | mk name guard children =>
          have own := mapped_children literal children
          have tail := mapped_rows literal rest
          constructor
          · simp only [mapEdges, edgeGuards, own.1, tail.1]
          · exact fun clean => ⟨own.2 clean.1, tail.2 clean.2⟩
termination_by sizeOf rows
end

/-- The actual symbol adapter retains binder guard restrictions without symbol injectivity. -/
theorem mapped_plainMu {Symbol : Type} (literal : String → Symbol) (expression : Expression)
    (clean : PlainMu top expression) : PlainMu top (mapSyntax literal expression) :=
  (mapped literal expression).2 clean

/-- The actual Label build of accepted original input has only Top-annotated cached Mu bodies. -/
theorem firstOrderRaw_mu_bodies
    [DecidableEq (EdgeKey (SourceObservations.Label FullSyntax.Formula) Guard)]
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (accepted : firstOrderRaw lib query signed = .ok expression)
    (value : Value (SourceObservations.Label FullSyntax.Formula) Guard)
    (heap : State (SourceObservations.Label FullSyntax.Formula) Guard)
    (built : build (SourceSynthesisUniverseCallerBoundary.ordinarySymbols expression) [] empty = .done value heap) :
    ∀ key entry body depth ordinary, heap.nodeRecords key = some (.mu entry body depth ordinary) →
      Annotated (fun guard => guard = top) body := by
  apply build_mu_bodies top _
    (mapped_plainMu SourceSynthesisLabelProgramBuildRoles.literal expression
      (SourceSynthesisRecursiveOrigins.firstOrderRaw_plainMu lib query signed expression accepted)) value heap
  simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using built

/-- Original input derives the conditional Mu winner certificate for every predicate containing Top. -/
theorem firstOrderRaw_muStored
    [DecidableEq (EdgeKey (SourceObservations.Label FullSyntax.Formula) Guard)]
    (valid : Guard → Prop) (validTop : valid top)
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (accepted : firstOrderRaw lib query signed = .ok expression)
    (value : Value (SourceObservations.Label FullSyntax.Formula) Guard)
    (heap : State (SourceObservations.Label FullSyntax.Formula) Guard)
    (built : build (SourceSynthesisUniverseCallerBoundary.ordinarySymbols expression) [] empty = .done value heap) :
    MuStored valid heap := by
  intro key entry body depth ordinary present _ _
  exact SourceCurrentHereditaryUnconstrained.annotated_mono
    (fun (guard : Guard) (same : guard = top) => same.symm ▸ validTop)
    (firstOrderRaw_mu_bodies lib query signed expression accepted value heap built
      key entry body depth ordinary present)
end Source

end MicroCFTA.SourceSynthesisNativeTypeSites
