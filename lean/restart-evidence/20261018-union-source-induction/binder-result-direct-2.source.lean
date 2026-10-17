import MicroCFTA.SourceCurrentStoredLiveSourceLineage
import MicroCFTA.SourceCurrentNativeMuPublicationCallbacks
import MicroCFTA.SourceCurrentNativeNormalizationFreshness

/-!
# Actual ordinary-body publication reconstruction

The actual publication supplies both filtered callback outputs. A node
source body makes both root filters identities. Its strict syntax children
supply reconstruction alignment. Actual probe and reservation freshness
derive compatibility on live captures, including unused captured aliases.
This theorem does not cover union or binder source roots or older winners.
-/
namespace MicroCFTA.SourceCurrentNativePublicationNodeAlignment
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work)
open InternedNestedProvenance (Values)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryLiveInputs (input liftInput local_inputs)
open InternedStoredSubstitution (Environment Replacements)
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceEqualityRequiredCache (Ready Keeps Ordinary)
open SourceCurrentNativeMuPublication (Publication History)
open SourceCurrentStoredPairedOrdinaryLineage (StrictChild)
open SourceCurrentStoredLiveSourceLineage (Aligned)
open SourceCurrentStoredProbeCompatibility (Compatible)
open InternedBinderProtocol (Reference)

private theorem node_result [DecidableEq (EdgeKey Symbol Guard)]
    (rows : List (EdgeSyntax Symbol Guard)) (inputs : List (Value Symbol Guard))
    (before after : State Symbol Guard)
    (context : InternedFreshOrdinaryContext.Context before inputs) (value : Value Symbol Guard)
    (actual : build (.node rows) inputs before = .done value after) : Ordinary value := by
  cases called : buildEdges rows inputs before with
  | pending key current => simp only [build,called,Outcome.bind] at actual; cases actual
  | done edges middle =>
      have made : run (makeNode edges) middle = (value,after) :=
        Prod.ext (Outcome.done.inj (by simpa only [build,called,Outcome.bind,work] using actual)).1
          (Outcome.done.inj (by simpa only [build,called,Outcome.bind,work] using actual)).2
      have checked := InternedFreshOrdinaryFacts.buildEdges_verified rows inputs before context.normal.facts context.inputs
      have facts : InternedNestedFacts.Facts middle := by simpa only [called,Outcome.state] using checked.facts
      simpa only [made] using SourceEqualityRequiredCache.node_ordinary edges middle facts (checked.result edges middle called)

private theorem ordinary_filter [DecidableEq (EdgeKey Symbol Guard)]
    (own : Reference) (value : Value Symbol Guard) (state : State Symbol Guard) (ordinary : Ordinary value) :
    run (withoutSelfReference own value) state = (value,state) := by
  cases value <;> try exact False.elim ordinary
  all_goals rfl

/-- Strict syntax-child alignment constructs both actual filtered publication reconstructions. -/
theorem publication_node [DecidableEq (EdgeKey Symbol Guard)]
    (event : Publication (Symbol := Symbol) (Guard := Guard))
    (rows : List (EdgeSyntax Symbol Guard)) (node : event.expression = .node rows)
    (children : ∀ child, StrictChild rows child → Aligned child)
    (common : State Symbol Guard) (current : Keeps event.afterBody common)
    (replacement : Value Symbol Guard) (available : Available common replacement) :
    ∃ left middle right reader,
      execute event.body
        (fun name => if name = .interned event.entry.identity then some replacement else none)
        common = .done left middle ∧
      execute event.ordinary
        (fun name => if name = .uninterned (ordinaryLevel event.depth) then some replacement else none)
        middle = .done right reader ∧
      execute event.body
        (fun name => if name = .interned event.entry.identity then some replacement else none)
        reader = .done left reader ∧
      execute event.ordinary
        (fun name => if name = .uninterned (ordinaryLevel event.depth) then some replacement else none)
        reader = .done right reader ∧
      Keeps common middle ∧ Keeps middle reader ∧ Available reader left ∧ Available reader right ∧
      Nonempty (History common middle) ∧ Nonempty (History middle reader) ∧
      SourceCurrentOpenObservationSurvival.Related left right := by
  let inputs : List (Sum (Value Symbol Guard) Unit) := event.environment.map Sum.inl
  let names : Unit → Reference := fun _ => .depth
  let bodyInputs := .inr (.inl ()) :: inputs.map liftInput
  let ordinaryName : Reference := .uninterned (ordinaryLevel event.depth)
  let bodyName : Reference := .interned event.entry.identity
  let ordinaryNames := Sum.elim (fun _ : Unit => ordinaryName) names
  let bodyNames := Sum.elim (fun _ : Unit => bodyName) names
  let ordinaryMap : Environment Symbol Guard := fun name => if name = ordinaryName then some replacement else none
  let bodyMap : Environment Symbol Guard := fun name => if name = bodyName then some replacement else none
  have fixed : inputs.map (input names) = event.environment := by
    simp [inputs,input,List.map_map,Function.comp_def]
  have localMap (own : Reference) :
      bodyInputs.map (input (Sum.elim (fun _ : Unit => own) names)) = .reference own :: event.environment := by
    rw [local_inputs,fixed]
  obtain ⟨rawOrdinary,afterRawOrdinary,rawBody,afterRawBody,ordinaryDone,ordinaryFilter,bodyDone,bodyFilter,
    ordinaryGrowth,bodyGrowth,ordinaryEntry,bodyEntry⟩ := SourceCurrentNativeMuPublicationCallbacks.raw_callbacks event
  have ordinaryArgument : Available event.afterDepth (.reference ordinaryName) :=
    InternedNestedProvenance.ordinary_available _ _
  have cutContext := (SourceCurrentNativeMuPublicationCallbacks.contexts event).2.1
  have bodyArgument : Available event.allocated (.reference bodyName) :=
    (InternedConstructionProvenance.reserve_available event.key event.cut cutContext.base.normal.facts.coherent
      cutContext.base.normal.facts.cached).2
  have ordinaryContext := ordinaryEntry.base.local ordinaryName ordinaryArgument
  have bodyContext := bodyEntry.base.local bodyName bodyArgument
  have ordinaryRoot : Ordinary rawOrdinary := node_result rows _ _ _ ordinaryContext _ (node ▸ ordinaryDone)
  have bodyRoot : Ordinary rawBody := node_result rows _ _ _ bodyContext _ (node ▸ bodyDone)
  have ordinarySame : rawOrdinary = event.ordinary ∧ afterRawOrdinary = event.cut := by
    exact Prod.mk.inj ((ordinary_filter ordinaryName _ _ ordinaryRoot).symm.trans ordinaryFilter)
  have bodySame : rawBody = event.body ∧ afterRawBody = event.afterBody := by
    exact Prod.mk.inj ((ordinary_filter bodyName _ _ bodyRoot).symm.trans bodyFilter)
  have ordinaryFresh : ordinaryName ∉
      (SourceCurrentNativeNormalizationInputs.support (.binder true event.expression) inputs).map (Sum.elim id names) :=
    SourceCurrentNativeNormalizationFreshness.ordinary event.expression inputs names event.before event.afterDepth
      (by simpa only [fixed] using event.context.base) event.depth (by simpa only [fixed] using event.depthDone)
  have bodyFresh : bodyName ∉
      (SourceCurrentNativeNormalizationInputs.support (.binder true event.expression) inputs).map (Sum.elim id names) :=
    SourceCurrentNativeNormalizationFreshness.reserved (.binder true event.expression) inputs names event.cut
      (by simpa only [fixed] using cutContext.base) event.key event.missing
  have baseCompatible : Compatible (.binder true event.expression) inputs names names
      (fun _ => none) (fun _ => none) := ⟨fun _ _ => rfl,fun _ _ => rfl⟩
  have compatible : Compatible event.expression bodyInputs bodyNames ordinaryNames bodyMap ordinaryMap := by
    apply SourceCurrentStoredProbeCompatibility.extend event.expression inputs names names
      (fun _ => none) (fun _ => none) baseCompatible bodyName ordinaryName replacement
    intro label member
    constructor
    · intro same
      exact False.elim (bodyFresh (List.mem_map.mpr ⟨label,member,same⟩))
    · intro same
      exact False.elim (ordinaryFresh (List.mem_map.mpr ⟨label,member,same⟩))
  have ordinaryWarm := InternedFreshOrdinaryReplay.build_replay event.expression _ event.afterDepth common
    rawOrdinary afterRawOrdinary ordinaryContext.normal.facts.coherent.valid ordinaryDone
    (grows_trans ordinaryGrowth current.growth)
  have bodyWarm := InternedFreshOrdinaryReplay.build_replay event.expression _ event.allocated common
    rawBody afterRawBody bodyContext.normal.facts.coherent.valid bodyDone (grows_trans bodyGrowth current.growth)
  have bodyCallback : callback event.expression event.environment bodyName event.allocated =
      .done event.body event.afterBody := event.bodyDone
  have checked := callback_verified event.expression event.environment bodyName event.allocated
    bodyEntry.base.normal.facts bodyContext.inputs
  have captures : Values event.afterBody event.environment := by
    intro value member
    simpa only [bodyCallback,Outcome.state] using checked.available value (bodyEntry.base.inputs value member)
  have bodyAtEnd : Available event.afterBody (.reference bodyName) := by
    simpa only [bodyCallback,Outcome.state] using checked.available (.reference bodyName) bodyArgument
  have ordinaryInputs : Values common (bodyInputs.map (input ordinaryNames)) := by
    rw [localMap]
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact InternedNestedProvenance.ordinary_available _ _
    · exact current.available value (captures value member)
  have bodyInputsAvailable : Values common (bodyInputs.map (input bodyNames)) := by
    rw [localMap]
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact current.available _ bodyAtEnd
    · exact current.available value (captures value member)
  have bodyReplacements : Replacements common bodyMap := by
    intro name value found
    dsimp only [bodyMap] at found
    split at found
    · cases found; exact available
    · cases found
  have ordinaryReplacements : Replacements common ordinaryMap := by
    intro name value found
    dsimp only [ordinaryMap] at found
    split at found
    · cases found; exact available
    · cases found
  have aligned : Aligned event.expression := by
    rw [node]
    exact SourceCurrentStoredLiveSourceLineage.ordinary rows children
  have completed := SourceCurrentStoredLiveSourceLineage.complete event.expression aligned bodyInputs bodyNames ordinaryNames
    bodyMap ordinaryMap compatible event.allocated afterRawBody event.afterDepth afterRawOrdinary common
    (by simpa only [bodyNames,localMap] using bodyContext) (by simpa only [ordinaryNames,localMap] using ordinaryContext)
    rawBody rawOrdinary (by simpa only [bodyNames,localMap] using bodyDone)
    (by simpa only [ordinaryNames,localMap] using ordinaryDone)
    (grows_trans bodyGrowth current.growth) (grows_trans ordinaryGrowth current.growth) current.ready bodyInputsAvailable ordinaryInputs
    bodyReplacements ordinaryReplacements
  simpa only [bodySame.1,ordinarySame.1,bodyMap,ordinaryMap,bodyName,ordinaryName] using completed

end MicroCFTA.SourceCurrentNativePublicationNodeAlignment
