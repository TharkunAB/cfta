import MicroCFTA.MergedPrefixCompletion
import MicroCFTA.SourceSynthesisCurrentUniverseOrigins
import MicroCFTA.SourceSynthesisLabelProgramBuildRoles
import MicroCFTA.SourceSynthesisUniverseNativeInput
import MicroCFTA.SourceCurrentCompletedBuildRootedWriters
import MicroCFTA.SourceSynthesisCurrentUniverseBody
import MicroCFTA.InternedFreshOrdinaryReplay

/-!
# One resident universe owner in the actual current root build

Every stored Mu retains its actual source writer and callback.
The source path identifies the same computed universe at environment [].
Replaying those actual calls in the final heap equates their full values.
The source heap can contain no Mu. The root result can be Empty.
-/
namespace MicroCFTA.SourceSynthesisCurrentUniverseOwnership
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome finish)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryFacts (callback)
open InternedStoredShallowCompletion (BinderFree ManyBinderFree EdgesBinderFree)
open InternedShallowHeap (NoNewMu)
open InternedBinderProtocol (NodeKey Reference)
open SourceSynthesisTypeSyntax (Library Query allTypes allTypesBody)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction (Expression Row)
open SourceSynthesisUniverseOrigins (OverUniverse)
open SourceSynthesisProgramBuildRolesGeneric
  (mapSyntax mapChildren mapEdges mapEdge mapChildren_eq_map mapEdges_eq_map)
open SourceCurrentNativeMuPublication (Publication)
open InternedFreshOrdinarySourceHistory (Reached)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
local notation "SourcePath" => InternedFreshOrdinaryActiveOrigins.Path
local notation "Crossing" => InternedFreshOrdinaryActiveOrigins.Crossing

set_option autoImplicit false

mutual
private theorem mapped_free (expression : Expression) (clean : BinderFree expression) :
    BinderFree (mapSyntax literal expression) := by
  cases expression with
  | empty | var => simp only [mapSyntax, BinderFree]
  | binder => simp only [BinderFree] at clean
  | node rows =>
      simp only [mapSyntax, BinderFree] at clean ⊢
      exact mapped_edges_free rows clean
  | union members =>
      simp only [mapSyntax, BinderFree] at clean ⊢
      exact mapped_many_free members clean
termination_by sizeOf expression

private theorem mapped_many_free (expressions : List Expression) (clean : ManyBinderFree expressions) :
    ManyBinderFree (mapChildren literal expressions) := by
  cases expressions with
  | nil => simp only [mapChildren, ManyBinderFree]
  | cons first rest =>
      simp only [mapChildren, ManyBinderFree] at clean ⊢
      exact ⟨mapped_free first clean.1, mapped_many_free rest clean.2⟩
termination_by sizeOf expressions

private theorem mapped_edges_free (rows : List Row) (clean : EdgesBinderFree rows) :
    EdgesBinderFree (mapEdges literal rows) := by
  cases rows with
  | nil => simp only [mapEdges, EdgesBinderFree]
  | cons row rest =>
      cases row with
      | mk name guard children =>
          simp only [mapEdges, EdgesBinderFree] at clean ⊢
          exact ⟨mapped_many_free children clean.1, mapped_edges_free rest clean.2⟩
termination_by sizeOf rows
end

private theorem many_free_member (children : List (Syntax Symbol Guard))
    (clean : ManyBinderFree children) (child : Syntax Symbol Guard) (member : child ∈ children) :
    BinderFree child := by
  induction children with
  | nil => cases member
  | cons first rest ih =>
      simp only [ManyBinderFree] at clean
      rcases List.mem_cons.mp member with rfl | later
      · exact clean.1
      · exact ih clean.2 later

private theorem row_free_child (rows : List (EdgeSyntax Symbol Guard))
    (clean : EdgesBinderFree rows) (symbol : Symbol) (guard : Guard)
    (children : List (Syntax Symbol Guard)) (member : .mk symbol guard children ∈ rows)
    (child : Syntax Symbol Guard) (inside : child ∈ children) : BinderFree child := by
  induction rows with
  | nil => cases member
  | cons first rest ih =>
      cases first with
      | mk name ownGuard ownChildren =>
          simp only [EdgesBinderFree] at clean
          rcases List.mem_cons.mp member with same | later
          · cases same
            exact many_free_member children clean.1 child inside
          · exact ih clean.2 later

private theorem mapped_node_child (rows : List Row)
    {symbol : Symbol} {guard : Guard} {children : List (Syntax Symbol Guard)}
    {child : Syntax Symbol Guard}
    (edge : .mk symbol guard children ∈ mapEdges literal rows) (member : child ∈ children) :
    ∃ (name : String) (ownGuard : Guard) (sourceChildren : List Expression) (sourceChild : Expression),
      .mk name ownGuard sourceChildren ∈ rows ∧ sourceChild ∈ sourceChildren ∧
      child = mapSyntax literal sourceChild := by
  have mappedMember : .mk symbol guard children ∈ rows.map (mapEdge literal) := by
    simpa only [mapEdges_eq_map] using edge
  obtain ⟨row, included, same⟩ := List.mem_map.mp mappedMember
  cases row with
  | mk name ownGuard sourceChildren =>
      simp only [mapEdge, EdgeSyntax.mk.injEq] at same
      obtain ⟨_symbol, _guard, childrenSame⟩ := same
      rw [← childrenSame] at member
      have childMember : child ∈ sourceChildren.map (mapSyntax literal) := by
        simpa only [mapChildren_eq_map] using member
      obtain ⟨sourceChild, inside, childSame⟩ := List.mem_map.mp childMember
      exact ⟨name, ownGuard, sourceChildren, sourceChild, included, inside, childSame.symm⟩

section Trace
variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem path_free
    {root expression : Syntax Symbol Guard} {inputs environment : List (Value Symbol Guard)}
    {crossings : List (Crossing Symbol Guard)}
    (path : SourcePath root inputs expression environment crossings)
    (clean : BinderFree root) : BinderFree expression := by
  induction path with
  | here => exact clean
  | node edge member nested ih =>
      simp only [BinderFree] at clean
      exact ih (row_free_child _ clean _ _ _ edge _ member)
  | union member nested ih =>
      simp only [BinderFree] at clean
      exact ih (many_free_member _ clean _ member)
  | binder crossing nested ih => simp only [BinderFree] at clean

/-- An ordinary prefix cannot cross a callback before it reaches its universe binder. -/
private theorem mapped_prefix_binder (catalog : List (String × Nat)) (expression : Expression)
    (origin : OverUniverse (allTypes top catalog) expression) :
    ∀ (initial current : List (Value Symbol Guard)) (smart : Bool) (body : Syntax Symbol Guard)
      (crossings : List (Crossing Symbol Guard)),
      SourcePath (mapSyntax literal expression) initial (.binder smart body) current crossings →
      .binder smart body = mapSyntax literal (allTypes top catalog) ∧ current = initial ∧ crossings = [] := by
  induction origin with
  | atom =>
      intro initial current smart body crossings path
      generalize sameRoot : mapSyntax literal (allTypes top catalog) = root at path
      cases path with
      | here => exact ⟨rfl, rfl, rfl⟩
      | node edge member nested => cases sameRoot
      | union member nested => cases sameRoot
      | binder crossing nested =>
          change Syntax.binder true (mapSyntax literal (allTypesBody top catalog)) =
            Syntax.binder crossing.smart crossing.body at sameRoot
          have sameBody := (Syntax.binder.inj sameRoot).2
          have bodyFree : BinderFree crossing.body := sameBody ▸
            mapped_free (allTypesBody top catalog)
              (SourceSynthesisUniverseNativeInput.allTypesBody_binderFree top catalog)
          have impossible : False := by
            simpa only [BinderFree] using path_free nested bodyFree
          exact False.elim impossible
  | node rows children ih =>
      intro initial current smart body crossings path
      cases path with
      | node edge member nested =>
          obtain ⟨name, guard, inputs, child, included, inside, same⟩ :=
            mapped_node_child rows edge member
          rw [same] at nested
          exact ih (.mk name guard inputs) included child inside initial current smart body crossings nested
  | union members children ih =>
      intro initial current smart body crossings path
      cases path with
      | union member nested =>
          have mappedMember := member
          simp only [mapChildren_eq_map] at mappedMember
          obtain ⟨child, included, same⟩ := List.mem_map.mp mappedMember
          rw [← same] at nested
          exact ih child included initial current smart body crossings nested

private theorem current_reached_binder
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    {smart : Bool} {body : Syntax Symbol Guard} {environment : List (Value Symbol Guard)}
    {state : State Symbol Guard}
    (site : Reached (ordinarySymbols whole) [] (.binder smart body) environment state) :
    smart = true ∧
      body = ordinarySymbols (allTypesBody top (SourceSynthesisCurrentContext.constructorCatalog lib query)) ∧
      environment = [] := by
  obtain ⟨crossings, path, _⟩ := site
  have sourcePath : SourcePath (mapSyntax literal whole) [] (.binder smart body) environment crossings := by
    simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using path
  obtain ⟨same, inputs, _⟩ := mapped_prefix_binder
    (SourceSynthesisCurrentContext.constructorCatalog lib query) whole
    (SourceSynthesisCurrentUniverseOrigins.firstOrderRaw_overUniverse lib query signed whole accepted)
    [] environment smart body crossings sourcePath
  change Syntax.binder smart body = Syntax.binder true (mapSyntax literal
    (allTypesBody top (SourceSynthesisCurrentContext.constructorCatalog lib query))) at same
  have fields := Syntax.binder.inj same
  refine ⟨fields.1, ?_, inputs⟩
  simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using fields.2

/-- An observed stored Mu supplies exact replay of the computed current universe. -/
private theorem stored_mu_current_resources
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (heap : State Symbol Guard)
    (built : build (ordinarySymbols whole) [] empty = .done rootValue heap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : heap.nodeRecords key = some (.mu entry body depth ordinary)) :
    heap.nodeRecords (muKey depth ordinary) = some (.mu entry body depth ordinary) ∧
      Available heap (.mu entry body depth ordinary) ∧
      (Value.mu entry body depth ordinary).free = [] ∧
      ∀ later : State Symbol Guard, Grows heap later →
        build (ordinarySymbols ((SourceSynthesisCurrentContext.context lib query).types)) [] later =
          .done (.mu entry body depth ordinary) later := by
  obtain ⟨event, site, keySame, valueSame, missing, _prefix, _depthPath, _ordinaryPath, _bodyPath,
      growth, _issued⟩ :=
    SourceCurrentCompletedBuildRootedWriters.build_writer (ordinarySymbols whole) [] empty
      SourceCurrentConstrainedCapSourceHistory.empty_context
      (by intro key entry body depth ordinary absent; cases absent)
      rootValue heap built key entry body depth ordinary stored
  obtain ⟨smartSame, expressionSame, environmentSame⟩ :=
    current_reached_binder lib query signed whole accepted site
  obtain ⟨_depthContext, cutContext, bodyContext⟩ := SourceCurrentNativeMuPublicationCallbacks.contexts event
  have localAvailable : Available event.allocated (.reference (.interned event.entry.identity)) :=
    (InternedConstructionProvenance.reserve_available event.key event.cut
      cutContext.base.normal.facts.coherent cutContext.base.normal.facts.cached).2
  obtain ⟨actualBody, actualFinal, constructed, kept, closed⟩ :=
    SourceSynthesisCurrentUniverseBody.current_types_callback_cleanup lib query event.entry
      event.allocated bodyContext.base.normal.facts localAvailable event.depth event.ordinary
  have calledBody : callback
      (ordinarySymbols (allTypesBody top (SourceSynthesisCurrentContext.constructorCatalog lib query))) []
      (.interned event.entry.identity) event.allocated = .done event.body event.afterBody := by
    simpa only [Publication.entry, Publication.allocated, Publication.key,
      expressionSame, environmentSame] using event.bodyDone
  have bodySame : actualBody = event.body :=
    (Outcome.done.inj (constructed.symm.trans calledBody)).1
  have keptCandidate : finish true event.candidate = event.candidate := by
    simpa only [bodySame, Publication.candidate] using kept
  have closedCandidate : event.candidate.free = [] := by
    simpa only [bodySame, Publication.candidate] using closed
  obtain ⟨winner, _record, result, prior⟩ := event.winner
  have winnerSame : winner = event.candidate := by
    rcases prior with old | ⟨_absent, same⟩
    · rw [missing] at old; cases old
    · exact same
  have returned : event.result = event.candidate := by
    calc
      event.result = finish true event.candidate := by
        simpa only [smartSame, winnerSame] using result
      _ = event.candidate := keptCandidate
  have binderSame : .binder event.smart event.expression =
      ordinarySymbols ((SourceSynthesisCurrentContext.context lib query).types) := by
    rw [smartSame, expressionSame]
    rfl
  have called : build (ordinarySymbols ((SourceSynthesisCurrentContext.context lib query).types))
      [] event.before = .done (.mu entry body depth ordinary) event.after := by
    have actual := event.build_done
    rw [binderSame, environmentSame, returned, ← valueSame] at actual
    exact actual
  have fields := Value.mu.inj valueSame
  have canonicalKey : key = muKey depth ordinary := by
    simpa only [Publication.key, fields.2.2.1, fields.2.2.2] using keySame
  have canonical : heap.nodeRecords (muKey depth ordinary) = some (.mu entry body depth ordinary) := by
    simpa only [canonicalKey] using stored
  have checked := InternedFreshOrdinaryFacts.build_verified (ordinarySymbols whole) [] empty
    InternedNestedFacts.empty_facts (by intro value member; cases member)
  have heapFacts : InternedNestedFacts.Facts heap := by
    simpa only [built, Outcome.state] using checked.facts
  have available : Available heap (.mu entry body depth ordinary) := heapFacts.cached.nodes key _ stored
  refine ⟨canonical, available, ?_, ?_⟩
  · rw [valueSame]
    exact closedCandidate
  · intro later laterGrowth
    exact InternedFreshOrdinaryReplay.build_replay
      (ordinarySymbols ((SourceSynthesisCurrentContext.context lib query).types)) []
      event.before later (.mu entry body depth ordinary) event.after
      event.context.base.normal.facts.coherent.valid called (grows_trans growth laterGrowth)

end Trace

/-- The actual current source heap has no Mu or one resident replayable universe owner. -/
theorem current_build_single_universe
    [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue heap) :
    (∀ (key : InternedBinderProtocol.NodeKey)
      (entry : Cache.Interned InternedBinderProtocol.NodeKey)
      (body depth ordinary : Value Symbol Guard),
      heap.nodeRecords key ≠ some (.mu entry body depth ordinary)) ∨
    ∃ (entry : Cache.Interned InternedBinderProtocol.NodeKey)
      (body depth ordinary : Value Symbol Guard),
      heap.nodeRecords (muKey depth ordinary) = some (.mu entry body depth ordinary) ∧
      Available heap (.mu entry body depth ordinary) ∧
      (Value.mu entry body depth ordinary).free = [] ∧
      (∀ later : State Symbol Guard, Grows heap later →
        InternedFreshOrdinaryConstruction.build
          (ordinarySymbols ((SourceSynthesisCurrentContext.context lib query).types)) [] later =
            .done (.mu entry body depth ordinary) later) ∧
      (∀ (key : InternedBinderProtocol.NodeKey)
        (other : Cache.Interned InternedBinderProtocol.NodeKey)
        (otherBody otherDepth otherOrdinary : Value Symbol Guard),
        heap.nodeRecords key = some (.mu other otherBody otherDepth otherOrdinary) →
          Value.mu other otherBody otherDepth otherOrdinary = .mu entry body depth ordinary) := by
  classical
  by_cases someMu : ∃ (key : NodeKey) (entry : Interned NodeKey)
      (body depth ordinary : Value Symbol Guard),
      heap.nodeRecords key = some (.mu entry body depth ordinary)
  · obtain ⟨key, entry, body, depth, ordinary, stored⟩ := someMu
    obtain ⟨canonical, available, closed, replay⟩ :=
      stored_mu_current_resources lib query signed whole accepted rootValue heap built
        key entry body depth ordinary stored
    refine .inr ⟨entry, body, depth, ordinary, canonical, available, closed, replay, ?_⟩
    intro key other otherBody otherDepth otherOrdinary present
    obtain ⟨_canonical, _available, _closed, otherReplay⟩ :=
      stored_mu_current_resources lib query signed whole accepted rootValue heap built
        key other otherBody otherDepth otherOrdinary present
    exact (Outcome.done.inj
      ((otherReplay heap (grows_refl heap)).symm.trans (replay heap (grows_refl heap)))).1
  · left
    intro key entry body depth ordinary stored
    exact someMu ⟨key, entry, body, depth, ordinary, stored⟩


/-- Each Mu in the actual current source heap retains its complete labeled rows. -/
theorem current_stored_universe_rows
    [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (heap : State Symbol Guard)
    (built : build (ordinarySymbols whole) [] empty = .done rootValue heap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : heap.nodeRecords key = some (.mu entry body depth ordinary)) :
    ∃ (bodyEntry : Interned NodeKey) (marker : Value Symbol Guard)
      (arrow : EdgeValue Symbol Guard) (rows : List (EdgeValue Symbol Guard)),
      body = .node bodyEntry (canonicalEdges (arrow :: rows)) 0 [.interned entry.identity] ∧
      (∃ (markerEntry : Interned NodeKey) (markerRow : EdgeValue Symbol Guard),
        marker = .node markerEntry [markerRow] 0 [] ∧ markerRow.children = [] ∧
        markerRow.entry.key = ⟨literal "(->)", [], top⟩) ∧
      arrow.children = [marker, .reference (.interned entry.identity), .reference (.interned entry.identity)] ∧
      arrow.entry.key = ⟨literal "->",
        [marker.referenceOf, .ref (.interned entry.identity), .ref (.interned entry.identity)], top⟩ ∧
      Language.All₂ (fun (descriptor : String × Nat) (row : EdgeValue Symbol Guard) =>
        row.children = List.replicate descriptor.2 (.reference (.interned entry.identity)) ∧
        row.entry.key = ⟨literal descriptor.1,
          List.replicate descriptor.2 (.ref (.interned entry.identity)), top⟩)
        (SourceSynthesisUniverseBody.descriptors
          (SourceSynthesisCurrentContext.constructorCatalog lib query)) rows ∧
      marker.free = [] ∧ Available heap marker ∧
      (∀ row ∈ canonicalEdges (arrow :: rows), row.entry.key.constraint = top ∧
        ∀ child ∈ row.children, child = marker ∨ child = .reference (.interned entry.identity)) ∧
      arrow ∈ canonicalEdges (arrow :: rows) := by
  obtain ⟨event, site, _keySame, valueSame, _missing, _prefix, _depthPath, _ordinaryPath,
      _bodyPath, _growth, _issued⟩ :=
    SourceCurrentCompletedBuildRootedWriters.build_writer (ordinarySymbols whole) [] empty
      SourceCurrentConstrainedCapSourceHistory.empty_context
      (by intro key entry body depth ordinary absent; cases absent)
      rootValue heap built key entry body depth ordinary stored
  obtain ⟨_smartSame, expressionSame, environmentSame⟩ :=
    current_reached_binder lib query signed whole accepted site
  have fields := Value.mu.inj valueSame
  have entrySame := fields.1
  have originalBody := fields.2.1
  cases entrySame
  obtain ⟨_depthContext, cutContext, bodyContext⟩ :=
    SourceCurrentNativeMuPublicationCallbacks.contexts event
  have localAvailable : Available event.allocated (.reference (.interned event.entry.identity)) :=
    (InternedConstructionProvenance.reserve_available event.key event.cut
      cutContext.base.normal.facts.coherent cutContext.base.normal.facts.cached).2
  obtain ⟨bodyEntry, marker, arrow, rows, final, called, markerRead,
      arrowChildren, arrowKey, aligned, _finalFacts, _finalAvailable, _resident,
      closed, _markerAvailable, kinds, retained⟩ :=
    SourceSynthesisCurrentUniverseBody.current_types_callback_rows lib query
      (.interned event.entry.identity) event.allocated bodyContext.base.normal.facts localAvailable
  have calledBody : callback
      (ordinarySymbols (allTypesBody top (SourceSynthesisCurrentContext.constructorCatalog lib query))) []
      (.interned event.entry.identity) event.allocated = .done event.body event.afterBody := by
    simpa only [Publication.entry, Publication.allocated, Publication.key,
      expressionSame, environmentSame] using event.bodyDone
  have bodySame := (Outcome.done.inj (called.symm.trans calledBody)).1
  have bodyEq : body =
      .node bodyEntry (canonicalEdges (arrow :: rows)) 0 [.interned event.entry.identity] :=
    originalBody.trans bodySame.symm
  have checked := InternedFreshOrdinaryFacts.build_verified (ordinarySymbols whole) [] empty
    InternedNestedFacts.empty_facts (by intro value member; cases member)
  have heapFacts : InternedNestedFacts.Facts heap := by
    simpa only [built, Outcome.state] using checked.facts
  have muAvailable := heapFacts.cached.nodes key _ stored
  have bodyAvailable : Available heap body :=
    muAvailable.children body (by simp [InternedProbeProvenance.children])
  rw [bodyEq] at bodyAvailable
  have markerAvailable : Available heap marker := by
    apply bodyAvailable.children marker
    change marker ∈ (canonicalEdges (arrow :: rows)).flatMap EdgeValue.children
    exact List.mem_flatMap.mpr ⟨arrow, retained, by simp [arrowChildren]⟩
  exact ⟨bodyEntry, marker, arrow, rows, bodyEq, markerRead, arrowChildren, arrowKey,
    aligned, closed, markerAvailable, kinds, retained⟩

/-- The actual current source build stores only bodies with cached depth zero. -/
theorem current_build_shallow
    [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (heap : State Symbol Guard)
    (built : build (ordinarySymbols whole) [] empty = .done rootValue heap) :
    InternedShallowHeap.Shallow heap := by
  intro key entry body depth ordinary stored
  obtain ⟨bodyEntry, marker, arrow, rows, shape, _⟩ :=
    current_stored_universe_rows lib query signed whole accepted rootValue heap built
      key entry body depth ordinary stored
  simp only [shape, Value.depth]

/-- Actual current source construction supplies preparation for native merging. -/
theorem current_build_prepared
    [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (heap : State Symbol Guard)
    (built : build (ordinarySymbols whole) [] empty = .done rootValue heap) :
    MergedPhysicalWarmup.Prepared heap := by
  have checked := InternedFreshOrdinaryFacts.build_verified (ordinarySymbols whole) [] empty
    InternedNestedFacts.empty_facts (by intro value member; cases member)
  have facts : InternedNestedFacts.Facts heap := by simpa only [built, Outcome.state] using checked.facts
  exact MergedPhysicalWarmup.prepared_of_shallow heap facts
    (current_build_shallow lib query signed whole accepted rootValue heap built)

/-- The same current source heap supplies a stable complete native merge. -/
theorem current_build_merge_complete
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (heap : State Symbol Guard)
    (built : build (ordinarySymbols whole) [] empty = .done rootValue heap)
    (clear : Guard → Bool) :
    ∃ bound result final,
      (∀ fuel, bound ≤ fuel → MergedColdMerge.execute MergedSourceGrouping.groups
        clear top fuel rootValue heap = .done result final) ∧
      MergedColdMerge.Extension heap final ∧ Available final result ∧
      InternedShallowHeap.NoNewMu heap final ∧ InternedShallowHeap.Shallow final ∧
      SourceSynthesisUniversePrefixHeight.height result ≤
        SourceSynthesisUniversePrefixHeight.height rootValue + 1 ∧
      ∀ atom ∈ InternedBoundaryAtoms.atoms result, atom ∈ InternedBoundaryAtoms.atoms rootValue := by
  have checked := InternedFreshOrdinaryFacts.build_verified (ordinarySymbols whole) [] empty
    InternedNestedFacts.empty_facts (by intro value member; cases member)
  have facts : InternedNestedFacts.Facts heap := by simpa only [built, Outcome.state] using checked.facts
  have available := checked.result rootValue heap built
  obtain ⟨bound, result, final, complete, extension, resultAvailable, unchanged, height, atoms⟩ :=
    MergedPrefixCompletion.source_execute_prefix_complete clear top rootValue heap facts
      (current_build_prepared lib query signed whole accepted rootValue heap built) available
  exact ⟨bound, result, final, complete, extension, resultAvailable, unchanged,
    InternedShallowHeap.shallow_preserved heap final
      (current_build_shallow lib query signed whole accepted rootValue heap built) unchanged,
    height, atoms⟩


/-- The same stored writer replays both actual source probes after record growth. -/
theorem current_stored_universe_source_probes
    [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (heap : State Symbol Guard)
    (built : build (ordinarySymbols whole) [] empty = .done rootValue heap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : heap.nodeRecords key = some (.mu entry body depth ordinary)) :
    ∀ (later : State Symbol Guard), Grows heap later →
      callback (ordinarySymbols (allTypesBody top
        (SourceSynthesisCurrentContext.constructorCatalog lib query))) [] .depth later = .done depth later ∧
      callback (ordinarySymbols (allTypesBody top
        (SourceSynthesisCurrentContext.constructorCatalog lib query))) []
        (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) later = .done ordinary later := by
  obtain ⟨event, site, _keySame, valueSame, _missing, _prefix, _depthPath, ordinaryPaths,
      bodyPaths, growth, _issued⟩ :=
    SourceCurrentCompletedBuildRootedWriters.build_writer (ordinarySymbols whole) [] empty
      SourceCurrentConstrainedCapSourceHistory.empty_context
      (by intro key entry body depth ordinary absent; cases absent)
      rootValue heap built key entry body depth ordinary stored
  obtain ⟨_smartSame, expressionSame, environmentSame⟩ :=
    current_reached_binder lib query signed whole accepted site
  have fields := Value.mu.inj valueSame
  have originalDepth := fields.2.2.1
  have originalOrdinary := fields.2.2.2
  obtain ⟨ordinaryPath⟩ := ordinaryPaths
  obtain ⟨bodyPath⟩ := bodyPaths
  have cutGrowth : Grows event.cut event.after :=
    grows_trans (SourceCurrentNativeMuGrowthHistory.reserve_growth event)
      (grows_trans bodyPath.growth (SourceCurrentNativeMuGrowthHistory.publication_growth event))
  have depthGrowth : Grows event.afterDepth event.after := grows_trans ordinaryPath.growth cutGrowth
  obtain ⟨depthContext, _cutContext, _bodyContext⟩ := SourceCurrentNativeMuPublicationCallbacks.contexts event
  intro later laterGrowth
  have afterGrowth : Grows event.after later := grows_trans growth laterGrowth
  have depthReplay := InternedFreshOrdinaryReplay.callback_replays event.expression event.environment .depth
    event.before later event.depth event.afterDepth event.context.base.normal.facts.coherent.valid event.depthDone
    (grows_trans depthGrowth afterGrowth)
  have ordinaryReplay := InternedFreshOrdinaryReplay.callback_replays event.expression event.environment
    (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel event.depth))
    event.afterDepth later event.ordinary event.cut depthContext.base.normal.facts.coherent.valid event.ordinaryDone
    (grows_trans cutGrowth afterGrowth)
  constructor
  · simpa only [expressionSame, environmentSame, originalDepth] using depthReplay
  · simpa only [expressionSame, environmentSame, originalDepth, originalOrdinary] using ordinaryReplay



end MicroCFTA.SourceSynthesisCurrentUniverseOwnership
