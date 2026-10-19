import MicroCFTA.SourceCurrentStoredLiteralRowLineage

/-!
# Supported child calls of a literal stored-Mu unfold row

The source is the actual stored body. Its indexed original child is
strictly smaller than that body. A changed child retains its actual
lexical call and semantic entry. No bound is placed on the returned child.
Literal rows do not include further epsilon observations through a Mu.
-/
namespace MicroCFTA.SourceCurrentStoredMuUnfoldChildContexts
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Outcome work)
open InternedNestedProvenance (Values)
open InternedFreshOrdinaryConstruction (build buildEdges)
open InternedStoredSubstitution (Environment Replacements leaves input encode encodeEdges)
open InternedFreshOrdinaryStoredSubstitution (execute unfold)
open SourceCurrentStoredSubstitutionCalls (Calls)
open SourceCurrentStoredLiteralRowLineage (RowAt)
open SourceCurrentLiteralRootParts (Row)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceCurrentNativeMuPublication (History Written)
open InternedBinderProtocol (NodeKey Reference)

/-- A literal output child retains its original row and its supported call when reconstruction changes it. -/
def Child [DecidableEq (EdgeKey Symbol Guard)] (source : Value Symbol Guard)
    (before after : State Symbol Guard) (row : EdgeValue Symbol Guard)
    (index : Nat) (child : Value Symbol Guard) : Prop :=
  ∃ original, RowAt source original ∧ row.entry.key.symbol = original.entry.key.symbol ∧
    row.entry.key.constraint = original.entry.key.constraint ∧ row.children.length = original.children.length ∧
    ∃ originalChild, original.children[index]? = some originalChild ∧
      sizeOf originalChild < sizeOf source ∧
      (child = originalChild ∨ ∃ lexical current next,
        SemanticHeap current ∧ Available current originalChild ∧ Replacements current lexical ∧
        execute originalChild lexical current = .done child next ∧
        Grows before current ∧ Extends before.nodes.issued current.nodes.issued ∧
        Grows next after ∧ Extends next.nodes.issued after.nodes.issued)

private theorem literal_source (source : Value Symbol Guard) (row : EdgeValue Symbol Guard)
    (part : Row source row) : RowAt source row := by
  induction part with
  | node member =>
      obtain ⟨index,found⟩ := List.mem_iff_getElem?.mp member
      exact .node found
  | union member _ ih =>
      obtain ⟨index,found⟩ := List.mem_iff_getElem?.mp member
      exact .union found ih

private theorem lift [DecidableEq (EdgeKey Symbol Guard)]
    {source target : Value Symbol Guard} {before current next after : State Symbol Guard}
    {row : EdgeValue Symbol Guard} {index : Nat} {child : Value Symbol Guard}
    (part : Child source current next row index child)
    (anchor : ∀ original, RowAt source original → RowAt target original)
    (earlier : Grows before current) (earlierIssued : Extends before.nodes.issued current.nodes.issued)
    (later : Grows next after) (laterIssued : Extends next.nodes.issued after.nodes.issued) :
    Child target before after row index child := by
  obtain ⟨original,origin,symbol,guard,arity,originalChild,selected,_smaller,calls⟩ := part
  have origin := anchor original origin
  refine ⟨original,origin,symbol,guard,arity,originalChild,selected,
    origin.child_smaller originalChild (List.mem_of_getElem? selected),?_⟩
  rcases calls with same | ⟨lexical,entry,returned,semantic,available,replacements,called,
    first,firstIssued,last,lastIssued⟩
  · exact .inl same
  · exact .inr ⟨lexical,entry,returned,semantic,available,replacements,called,
      grows_trans earlier first,extends_trans earlierIssued firstIssued,
      grows_trans last later,extends_trans lastIssued laterIssued⟩

private theorem closed [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (environment : Environment Symbol Guard) (before : State Symbol Guard) (noFree : value.free = []) :
    execute value environment before = .done value before := by
  unfold execute
  have captured : leaves value = [value] := by
    rw [leaves.eq_def]
    simp only [noFree,List.isEmpty_nil,ite_true]
  rw [captured]
  have encoded : encode [value] [] value = .var 0 := by
    rw [encode.eq_def]
    simp [noFree,InternedStoredSubstitution.slot]
  rw [encoded]
  simpa only [List.map_cons,List.map_nil,build,List.getElem?_cons_zero,Option.getD_some] using
    congrArg (fun result => (Outcome.done result before : Outcome Symbol Guard (Value Symbol Guard)))
      (InternedStoredSubstitutionScope.input_closed value environment noFree)

private theorem calls_effects [DecidableEq (EdgeKey Symbol Guard)]
    {environment : Environment Symbol Guard} {originals outputs : List (Value Symbol Guard)}
    {before after : State Symbol Guard} (actual : Calls environment originals before outputs after)
    (semantic : SemanticHeap before) (available : Values before originals)
    (replacements : Replacements before environment) :
    SemanticHeap after ∧ Grows before after ∧ Extends before.nodes.issued after.nodes.issued ∧
      Values after outputs := by
  induction actual with
  | nil => exact ⟨semantic,grows_refl _,extends_refl _,available⟩
  | cons original originals before middle after output outputs called rest ih =>
      obtain ⟨middleSemantic,first,firstIssued,outputAvailable,middleReplacements⟩ :=
        SourceCurrentStoredLiteralCalls.execute original environment before semantic
          (available original List.mem_cons_self) replacements output middle called
      have remaining : Values middle originals := fun value member =>
        (available value (List.mem_cons_of_mem _ member)).grows before middle first firstIssued
      obtain ⟨afterSemantic,last,lastIssued,outputsAvailable⟩ := ih middleSemantic remaining middleReplacements
      refine ⟨afterSemantic,grows_trans first last,extends_trans firstIssued lastIssued,?_⟩
      intro value member
      rcases List.mem_cons.mp member with rfl | member
      · exact outputAvailable.grows middle after last lastIssued
      · exact outputsAvailable value member

private theorem node_physical [DecidableEq (EdgeKey Symbol Guard)] (entry : Interned NodeKey)
    (originals : List (EdgeValue Symbol Guard)) (level : Nat) (free : List Reference)
    (environment : Environment Symbol Guard) (before : State Symbol Guard) (semantic : SemanticHeap before)
    (available : Available before (.node entry originals level free)) (replacements : Replacements before environment)
    (opened : free.isEmpty = false) (value : Value Symbol Guard) (after : State Symbol Guard)
    (actual : execute (.node entry originals level free) environment before = .done value after)
    (row : EdgeValue Symbol Guard) (part : Row value row) : ∃ index : Nat, (nodeEdges value)[index]? = some row := by
  let captures := leaves (.node entry originals level free)
  let inputs := captures.map (input environment)
  have inputAvailable := InternedStoredSubstitution.inputs_available _ environment before available replacements
  have compiled : encode captures [] (.node entry originals level free) = .node (encodeEdges captures [] originals) := by
    rw [encode.eq_def]
    simp only [Value.free,opened,Bool.false_eq_true,ite_false]
  change build (encode captures [] (.node entry originals level free)) inputs before = .done value after at actual
  rw [compiled,build] at actual
  cases called : buildEdges (encodeEdges captures [] originals) inputs before with
  | pending key stopped => simp only [called,Outcome.bind] at actual; cases actual
  | done edges middle =>
      have made : run (makeNode edges) middle = (value,after) :=
        Prod.ext (Outcome.done.inj (by simpa only [called,Outcome.bind,work] using actual)).1
          (Outcome.done.inj (by simpa only [called,Outcome.bind,work] using actual)).2
      have checked := InternedFreshOrdinaryFacts.buildEdges_verified
        (encodeEdges captures [] originals) inputs before semantic.1.normal.facts inputAvailable
      have facts : InternedNestedFacts.Facts middle := by simpa only [called,Outcome.state] using checked.facts
      have ordinary := SourceEqualityRequiredCache.node_ordinary edges middle facts (checked.result edges middle called)
      rw [made] at ordinary
      cases value with
      | node entry rows level free =>
          cases part with
          | node member => exact List.mem_iff_getElem?.mp member
      | empty | reference | mu => cases part
      | union => cases ordinary

private theorem source_child [DecidableEq (EdgeKey Symbol Guard)] (source : Value Symbol Guard)
    (environment : Environment Symbol Guard) (before : State Symbol Guard) (semantic : SemanticHeap before)
    (available : Available before source) (replacements : Replacements before environment)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (actual : execute source environment before = .done value after)
    (reader : State Symbol Guard) (history : History empty reader) (growth : Grows after reader)
    (row : EdgeValue Symbol Guard) (part : Row value row)
    (excluded : ∀ name replacement, environment name = some replacement → ¬ Row replacement row)
    (index : Nat) (child : Value Symbol Guard) (selected : row.children[index]? = some child) :
    Child source before after row index child := by
  by_cases noFree : source.free = []
  · rw [closed source environment before noFree] at actual
    obtain ⟨same,_⟩ := Outcome.done.inj actual
    have anchor := literal_source source row (same ▸ part)
    exact ⟨row,anchor,rfl,rfl,rfl,child,selected,
      anchor.child_smaller child (List.mem_of_getElem? selected),.inl rfl⟩
  · cases shape : source with
    | empty => exact False.elim (noFree (by rw [shape]; rfl))
    | reference name =>
        have called : execute (.reference name) environment before =
            .done ((environment name).getD (.reference name)) before := by
          simp [execute,leaves,Value.free,encode,InternedStoredSubstitution.slot,build,input]
        rw [shape,called] at actual
        have same := (Outcome.done.inj actual).1
        cases mapped : environment name with
        | none => simp only [mapped,Option.getD_none] at same; rw [←same] at part; cases part
        | some replacement =>
            simp only [mapped,Option.getD_some] at same
            exact False.elim (excluded name replacement mapped (same ▸ part))
    | node entry originals level free =>
        rw [shape] at available actual noFree
        have opened : free.isEmpty = false := by simpa only [Value.free,List.isEmpty_eq_false_iff] using noFree
        obtain ⟨rowIndex,rowSelected⟩ := node_physical entry originals level free environment before semantic available
          replacements opened value after actual row part
        obtain ⟨sourceIndex,original,rows,middle,current,childAfter,next,found,_rebuilt,edgesDone,nodeDone,
          earlier,called,made,later,symbol,guard,arity⟩ :=
          SourceCurrentStoredSubstitutionOrigins.node entry originals level free environment before semantic.1.normal
            available replacements opened value after actual rowIndex row rowSelected
        let captures := leaves (.node entry originals level free)
        let inputs := captures.map (input environment)
        have inputAvailable := InternedStoredSubstitution.inputs_available _ environment before available replacements
        have context : SourceCurrentConstrainedCapSourceHistory.Context before inputs :=
          ⟨SourceRecursiveIntersectionSemanticHeap.context before semantic inputs inputAvailable,semantic.2⟩
        have checked := InternedFreshOrdinaryFacts.buildEdges_verified
          (encodeEdges captures [] (originals.take sourceIndex)) inputs before context.base.normal.facts inputAvailable
        have first : Grows before current := by simpa only [earlier,Outcome.state] using checked.growth
        have firstIssued : Extends before.nodes.issued current.nodes.issued := by
          simpa only [earlier,Outcome.state] using checked.history
        have currentContext : SourceCurrentConstrainedCapSourceHistory.Context current inputs := by
          simpa only [earlier,Outcome.state] using context.edges (encodeEdges captures [] (originals.take sourceIndex))
        have currentSemantic : SemanticHeap current :=
          ⟨⟨currentContext.base.normal,(by intro item member; cases member),currentContext.base.profiles,
            currentContext.base.freeNames⟩,currentContext.depth⟩
        have originalAvailable : Values current original.children := by
          intro item member
          exact (available.children item (List.mem_flatMap.mpr ⟨original,List.mem_of_getElem? found,member⟩)).grows
            before current first firstIssued
        have currentReplacements : Replacements current environment := fun name item mapped =>
          (replacements name item mapped).grows before current first firstIssued
        obtain ⟨originalChild,callBefore,callAfter,childFound,_prefix,childDone,_suffix,
          callSemantic,childAvailable,callReplacements,_returnedSemantic,_returnedAvailable,_returnedReplacements,
          prefixGrowth,prefixIssued,_callGrowth,_callIssued,suffixGrowth,suffixIssued⟩ :=
          SourceCurrentStoredLiteralCalls.indexed called currentSemantic originalAvailable currentReplacements index child selected
        obtain ⟨childSemantic,childrenGrowth,childrenIssued,childrenAvailable⟩ :=
          calls_effects called currentSemantic originalAvailable currentReplacements
        have edgeGrowth : Grows childAfter next := by
          simpa only [made] using (InternedConstructorTemplates.run_correct
            (makeEdge original.entry.key.symbol original.entry.key.constraint row.children)
            childAfter childSemantic.1.normal.facts.coherent.valid).2
        have edgeIssued : Extends childAfter.nodes.issued next.nodes.issued := by
          simpa only [made] using InternedProbeProvenance.run_issued_extends
            (makeEdge original.entry.key.symbol original.entry.key.constraint row.children)
            childAfter childSemantic.1.normal.facts.coherent.valid
        have nextSemantic : SemanticHeap next := by
          simpa only [made] using SourceRecursiveIntersectionSemanticHeap.edge original.entry.key.symbol
            original.entry.key.constraint row.children childAfter childSemantic childrenAvailable
        have inputsNext : Values next inputs := fun item member =>
          (inputAvailable item member).grows before next
            (grows_trans first (grows_trans childrenGrowth edgeGrowth))
            (extends_trans firstIssued (extends_trans childrenIssued edgeIssued))
        have suffixChecked := InternedFreshOrdinaryFacts.buildEdges_verified
          (encodeEdges captures [] (originals.drop (sourceIndex+1))) inputs next nextSemantic.1.normal.facts inputsNext
        have last : Grows next middle := by simpa only [later,Outcome.state] using suffixChecked.growth
        have lastIssued : Extends next.nodes.issued middle.nodes.issued := by
          simpa only [later,Outcome.state] using suffixChecked.history
        have middleContext : SourceCurrentConstrainedCapSourceHistory.Context middle inputs := by
          simpa only [edgesDone,Outcome.state] using context.edges (encodeEdges captures [] originals)
        have madeGrowth : Grows middle after := by
          simpa only [nodeDone] using (InternedConstructorTemplates.run_correct (makeNode rows) middle
            middleContext.base.normal.facts.coherent.valid).2
        have madeIssued : Extends middle.nodes.issued after.nodes.issued := by
          simpa only [nodeDone] using InternedProbeProvenance.run_issued_extends (makeNode rows) middle
            middleContext.base.normal.facts.coherent.valid
        have anchor : RowAt (.node entry originals level free) original := .node found
        exact ⟨original,anchor,symbol,guard,arity,originalChild,childFound,
          anchor.child_smaller originalChild (List.mem_of_getElem? childFound),.inr
          ⟨environment,callBefore,callAfter,callSemantic,childAvailable,callReplacements,childDone,
            grows_trans first prefixGrowth,extends_trans firstIssued prefixIssued,
            grows_trans suffixGrowth (grows_trans edgeGrowth (grows_trans last madeGrowth)),
            extends_trans suffixIssued (extends_trans edgeIssued (extends_trans lastIssued madeIssued))⟩⟩
    | union entry originals level free =>
        rw [shape] at available actual noFree
        have opened : free.isEmpty = false := by simpa only [Value.free,List.isEmpty_eq_false_iff] using noFree
        obtain ⟨values,middle,sourceIndex,original,output,current,next,_calls,_made,found,_selected,literal,
          _earlier,called,_later,currentSemantic,originalAvailable,currentReplacements,
          _nextSemantic,_outputAvailable,_nextReplacements,earlierGrowth,earlierIssued,_calledGrowth,_calledIssued,
          laterGrowth,laterIssued⟩ := SourceCurrentStoredLiteralCalls.union_row entry originals level free environment
            before semantic available replacements opened value after actual row part
        have childPart := source_child original environment current currentSemantic originalAvailable currentReplacements
          output next called reader history (grows_trans laterGrowth growth) row literal excluded index child selected
        exact lift childPart (fun _ origin => .union found origin) earlierGrowth earlierIssued laterGrowth laterIssued
    | mu entry body depth ordinary =>
        rw [shape] at available actual noFree
        obtain ⟨currentDepth,afterDepth,raw,middle,_depthDone,bodyDone,bodySemantic,bodyAvailable,bodyReplacements,
          _rawGrowth,_rawIssued,laterGrowth,laterIssued,literal⟩ := SourceCurrentStoredMuLiteralRows.mu entry body depth ordinary
            environment before semantic available replacements value after actual reader history growth row part
        let localEnvironment := SourceCurrentStoredMuLexicalInputs.shadow (.interned entry.identity)
          (.reference (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel currentDepth))) environment
        have localExcluded : ∀ name replacement, localEnvironment name = some replacement → ¬ Row replacement row := by
          intro name replacement mapped
          dsimp only [localEnvironment,SourceCurrentStoredMuLexicalInputs.shadow] at mapped
          split at mapped
          · cases mapped; intro impossible; cases impossible
          · exact excluded name replacement mapped
        have childPart := source_child body localEnvironment afterDepth bodySemantic bodyAvailable bodyReplacements
          raw middle bodyDone reader history (grows_trans laterGrowth growth) row literal localExcluded index child selected
        have inputs := InternedStoredSubstitution.inputs_available _ environment before available replacements
        have context : SourceCurrentConstrainedCapSourceHistory.Context before
            ((leaves (.mu entry body depth ordinary)).map (input environment)) :=
          ⟨SourceRecursiveIntersectionSemanticHeap.context before semantic _ inputs,semantic.2⟩
        have depthChecked := InternedFreshOrdinaryFacts.callback_verified
          (encode (leaves (.mu entry body depth ordinary)) [.interned entry.identity] body)
          ((leaves (.mu entry body depth ordinary)).map (input environment)) .depth before
          context.base.normal.facts (context.local .depth (InternedNestedProvenance.depth_available before)).base.inputs
        have first : Grows before afterDepth := by simpa only [_depthDone,Outcome.state] using depthChecked.growth
        have firstIssued : Extends before.nodes.issued afterDepth.nodes.issued := by
          simpa only [_depthDone,Outcome.state] using depthChecked.history
        exact lift childPart (fun _ origin => .mu origin) first firstIssued laterGrowth laterIssued
termination_by sizeOf source
decreasing_by
  all_goals simp_wf
  all_goals simp_all only [Value.union.sizeOf_spec,Value.mu.sizeOf_spec]
  all_goals first | omega | exact Nat.lt_trans (List.sizeOf_lt_of_mem (List.mem_of_getElem? found)) (by omega)

/-- An actual selected Mu unfold derives its writer and each literal row child's supported original call. -/
theorem unfold_child [DecidableEq (EdgeKey Symbol Guard)]
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticHeap before)
    (available : Available before (.mu entry body depth ordinary))
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (actual : unfold (.mu entry body depth ordinary) before = .done value after)
    (reader : State Symbol Guard) (history : History empty reader) (growth : Grows after reader)
    (row : EdgeValue Symbol Guard) (literal : Row value row)
    (index : Nat) (child : Value Symbol Guard) (selected : row.children[index]? = some child) :
    Written empty entry.key (.mu entry body depth ordinary) ∧ Child body before after row index child := by
  let environment : Environment Symbol Guard := fun name =>
    if name = .interned entry.identity then some (.mu entry body depth ordinary) else none
  have replacements : Replacements before environment := by
    intro name replacement found
    dsimp only [environment] at found
    split at found
    · cases found; exact available
    · cases found
  have bodyAvailable := available.children body (by simp [children])
  have called : execute body environment before = .done value after := actual
  have effects := SourceCurrentStoredLiteralCalls.execute body environment before semantic bodyAvailable
    replacements value after called
  have present : before.nodeRecords entry.key = some (.mu entry body depth ordinary) := available.resident entry rfl
  have readerCell := growth.nodeRecords entry.key _ (effects.2.1.nodeRecords entry.key _ present)
  have excluded : ∀ name replacement, environment name = some replacement → ¬ Row replacement row := by
    intro name replacement found
    dsimp only [environment] at found
    split at found
    · cases found; intro impossible; cases impossible
    · cases found
  exact ⟨history.from_empty entry.key entry body depth ordinary readerCell,
    source_child body environment before semantic bodyAvailable replacements value after called
      reader history growth row literal excluded index child selected⟩

end MicroCFTA.SourceCurrentStoredMuUnfoldChildContexts
