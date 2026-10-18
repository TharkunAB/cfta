import MicroCFTA.SourceCurrentGeneratedNodeSchedules

/-!
# Historical source rows from actual row calls

A selected raw node row retains its original source index on both sides.
Actual row calls at one reader supply the ordered reconstructed children.
No whole node reconstruction call is required. The result retains full
symbols and guards. It does not assert that either reconstructed row survives.
-/
namespace MicroCFTA.SourceCurrentGeneratedRowSchedules
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work)
open InternedNestedProvenance (Values)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryLiveInputs (input inputProfile)
open InternedStoredSubstitution (Environment Replacements)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedBinderProtocol (Reference)
open InternedEdgeResidency (nodeEdges)
open SourceEqualityRequiredCache (Ready)
open SourceCurrentRetainedMuDirectedCase (Generated Inputs)
open SourceCurrentUsedBinderAliasTransport (Aliases Scope)
open SourceCurrentNativeNormalizationInputs (support inputNames)
open SourceCurrentOpenPreorderSimulation (Mutual)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentStoredMuRetainedAlignment (RowCall)
open SourceCurrentStoredNodeExpansion (RowCalls)
variable {Atom : Type}

private theorem row_call [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard)) (environment : List (Value Symbol Guard))
    (before after reader : State Symbol Guard) (context : InternedFreshOrdinaryContext.Context before environment)
    (outputs : List (EdgeValue Symbol Guard))
    (actual : buildEdges expressions environment before = .done outputs after)
    (growth : Grows after reader) (index : Nat) (symbol : Symbol) (guard : Guard)
    (children : List (Syntax Symbol Guard)) (found : expressions[index]? = some (.mk symbol guard children)) :
    Nonempty (RowCall expressions environment before outputs after reader index symbol guard children) := by
  induction expressions generalizing before outputs index with
  | nil => simp only [List.getElem?_nil] at found; cases found
  | cons expression expressions ih =>
    cases expression with
    | mk ownSymbol ownGuard ownChildren =>
      cases childDone : buildMany ownChildren environment before with
      | pending key state => simp only [buildEdges,childDone,Outcome.bind] at actual; cases actual
      | done values middle =>
        let made := run (makeEdge ownSymbol ownGuard values) middle
        cases tail : buildEdges expressions environment made.2 with
        | pending key state =>
            simp only [buildEdges,childDone,Outcome.bind,work] at actual
            change (buildEdges expressions environment made.2).bind _ = _ at actual
            simp only [tail,Outcome.bind] at actual
            cases actual
        | done remaining last =>
          simp only [buildEdges,childDone,Outcome.bind,work] at actual
          change (buildEdges expressions environment made.2).bind _ = _ at actual
          simp only [tail,Outcome.bind,Outcome.done.injEq] at actual
          obtain ⟨rfl,rfl⟩ := actual
          have childChecked := buildMany_verified ownChildren environment before context.normal.facts context.inputs
          have middleContext : InternedFreshOrdinaryContext.Context middle environment := by
            simpa only [childDone,Outcome.state] using context.many ownChildren
          have childrenAvailable := childChecked.result values middle childDone
          have edgeChecked := InternedNestedFacts.edge_verified ownSymbol ownGuard values middle
            middleContext.normal.facts childrenAvailable
          have nextContext : InternedFreshOrdinaryContext.Context made.2 environment := middleContext.edge ownSymbol ownGuard values childrenAvailable
          have tailChecked := buildEdges_verified expressions environment made.2 nextContext.normal.facts nextContext.inputs
          have nextGrowth : Grows made.2 reader := grows_trans (by simpa only [tail,Outcome.state] using tailChecked.growth) growth
          have middleGrowth : Grows middle reader := grows_trans edgeChecked.growth nextGrowth
          cases index with
          | zero =>
            simp only [List.getElem?_cons_zero,Option.some.injEq,EdgeSyntax.mk.injEq] at found
            obtain ⟨rfl,rfl,rfl⟩ := found
            have fields := MergedPhysicalGroupEdges.makeEdge_fields middle middleContext.normal.facts
              ownSymbol ownGuard values childrenAvailable
            exact ⟨⟨before,middle,made.2,values,made.1,rfl,rfl,(by simp only [List.take_zero,buildEdges]),childDone,rfl,tail,
              context,fields.1,fields.2.1,fields.2.2,
              grows_trans (by simpa only [childDone,Outcome.state] using childChecked.growth) middleGrowth,
              middleGrowth,nextGrowth⟩⟩
          | succ index =>
            obtain ⟨row⟩ := ih made.2 nextContext remaining tail index found
            refine ⟨{row with source := found, selected := row.selected, earlier := ?_, suffix := ?_}⟩
            · simp only [List.take_succ_cons,buildEdges,childDone,Outcome.bind,work]
              exact congrArg (fun result => result.bind (fun rows final => .done (made.1 :: rows) final)) row.earlier
            · simpa only [List.drop_succ_cons,Nat.add_assoc] using row.suffix


private theorem live_aliases (rows : List (EdgeSyntax Symbol Guard))
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (aliases : Aliases (.node rows) inputs firstNames secondNames)
    (symbol : Symbol) (guard : Guard) (children : List (Syntax Symbol Guard))
    (row : EdgeSyntax.mk symbol guard children ∈ rows)
    (live : (InternedProfileSemantics.evaluateMany children (inputs.map inputProfile)).all
      (fun child => !InternedProfileSemantics.isEmpty child) = true)
    (child : Syntax Symbol Guard) (member : child ∈ children) :
    Aliases child inputs firstNames secondNames := by
  have included (label : Sum Reference Atom) (present : label ∈ Scope child inputs) :
      label ∈ Scope (.node rows) inputs := by
    rcases List.mem_cons.mp present with rfl | present
    · exact List.mem_cons_self
    · apply List.mem_cons_of_mem
      unfold support at present ⊢
      rw [InternedFreeNameSemantics.evaluate]
      exact (InternedFreeNameSemantics.evaluateEdges_member rows (inputs.map inputProfile)
        (inputs.map inputNames) label).mpr ⟨symbol,guard,children,row,live,child,member,present⟩
  exact fun a aMember b bMember => aliases a (included a aMember) b (included b bMember)


private theorem source_live [DecidableEq (EdgeKey Symbol Guard)] (children : List (Syntax Symbol Guard))
    (inputs : List (Sum (Value Symbol Guard) Atom)) (names : Atom → Reference)
    (before after : State Symbol Guard)
    (context : InternedFreshOrdinaryContext.Context before (inputs.map (input names)))
    (values : List (Value Symbol Guard))
    (called : buildMany children (inputs.map (input names)) before = .done values after)
    (live : values.any (fun value => value.referenceOf == .empty) = false) :
    (InternedProfileSemantics.evaluateMany children (inputs.map inputProfile)).all
      (fun child => !InternedProfileSemantics.isEmpty child) = true := by
  have checked := buildMany_verified children _ before context.normal.facts context.inputs
  have afterContext : InternedFreshOrdinaryContext.Context after (inputs.map (input names)) := by
    simpa only [called,Outcome.state] using context.many children
  have output := checked.result values after called
  have matched := (InternedFreshOrdinaryProfiles.buildMany_profile children _ before
    context.normal context.inputs context.profiles).result values after called
  have actualLive : values.all (fun value => !InternedProfileSemantics.isEmpty (InternedRootProfile.profile value)) = true := by
    apply List.all_eq_true.mpr
    intro value member
    rw [InternedRootProfileNode.isEmpty_profile value after afterContext.normal.proper (output value member)]
    have absent := List.any_eq_false.mp live value member
    rw [Bool.eq_false_iff.mpr absent]
    rfl
  rw [InternedProfileComposition.children_matched matched] at actualLive
  simpa only [InternedFreshOrdinaryLiveInputs.input_profiles,InternedProfileSemantics.evaluateMany_map,
    List.all_map,Function.comp_def,InternedProfileSemantics.isEmpty_map] using actualLive

private theorem empty_same [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (before after later final : State Symbol Guard)
    (firstContext : InternedFreshOrdinaryContext.Context before (inputs.map (input firstNames)))
    (secondContext : InternedFreshOrdinaryContext.Context later (inputs.map (input secondNames)))
    (first second : Value Symbol Guard)
    (called : build expression (inputs.map (input firstNames)) before = .done first after)
    (other : build expression (inputs.map (input secondNames)) later = .done second final) :
    (first.referenceOf == .empty) = (second.referenceOf == .empty) := by
  rw [InternedRecordDepthSource.source_empty expression _ before firstContext first after called,
    InternedRecordDepthSource.source_empty expression _ later secondContext second final other,
    SourceCurrentNativeNormalizedComparison.instantiated,SourceCurrentNativeNormalizedComparison.instantiated,
    InternedDepthSemantics.isEmpty_map,InternedDepthSemantics.isEmpty_map]

private theorem many_empty [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (before after later final : State Symbol Guard)
    (firstContext : InternedFreshOrdinaryContext.Context before (inputs.map (input firstNames)))
    (secondContext : InternedFreshOrdinaryContext.Context later (inputs.map (input secondNames)))
    (first second : List (Value Symbol Guard))
    (called : buildMany expressions (inputs.map (input firstNames)) before = .done first after)
    (other : buildMany expressions (inputs.map (input secondNames)) later = .done second final) :
    first.any (fun value => value.referenceOf == .empty) = second.any (fun value => value.referenceOf == .empty) := by
  induction expressions generalizing before later first second with
  | nil =>
      simp only [buildMany,Outcome.done.injEq] at called other
      obtain ⟨rfl,rfl⟩ := called
      obtain ⟨rfl,rfl⟩ := other
      rfl
  | cons expression expressions ih =>
      cases one : build expression (inputs.map (input firstNames)) before with
      | pending key state => simp only [buildMany,one,Outcome.bind] at called; cases called
      | done value middle =>
        cases two : build expression (inputs.map (input secondNames)) later with
        | pending key state => simp only [buildMany,two,Outcome.bind] at other; cases other
        | done next nextHeap =>
          cases tail : buildMany expressions (inputs.map (input firstNames)) middle with
          | pending key state => simp only [buildMany,one,tail,Outcome.bind] at called; cases called
          | done values last =>
            cases rest : buildMany expressions (inputs.map (input secondNames)) nextHeap with
            | pending key state => simp only [buildMany,two,rest,Outcome.bind] at other; cases other
            | done results lastHeap =>
              simp only [buildMany,one,tail,Outcome.bind,Outcome.done.injEq] at called
              simp only [buildMany,two,rest,Outcome.bind,Outcome.done.injEq] at other
              obtain ⟨rfl,rfl⟩ := called
              obtain ⟨rfl,rfl⟩ := other
              have middleContext : InternedFreshOrdinaryContext.Context middle (inputs.map (input firstNames)) := by
                simpa only [one,Outcome.state] using firstContext.build expression
              have nextContext : InternedFreshOrdinaryContext.Context nextHeap (inputs.map (input secondNames)) := by
                simpa only [two,Outcome.state] using secondContext.build expression
              simp only [List.any_cons,empty_same expression inputs firstNames secondNames before middle later nextHeap
                firstContext secondContext value next one two,
                ih middle nextHeap middleContext nextContext values results tail rest]

private def SourceCall [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) (inputs : List (Value Symbol Guard))
    (reader : State Symbol Guard) (value : Value Symbol Guard) : Prop :=
  ∃ before after, Context before inputs ∧ build expression inputs before = .done value after ∧
    Grows after reader ∧ build expression inputs reader = .done value reader

private theorem source_children [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard)) (inputs : List (Value Symbol Guard))
    (before after reader : State Symbol Guard) (context : Context before inputs)
    (values : List (Value Symbol Guard)) (called : buildMany expressions inputs before = .done values after)
    (growth : Grows after reader) : All₂ (fun expression value => SourceCall expression inputs reader value) expressions values := by
  induction expressions generalizing before values with
  | nil =>
      simp only [buildMany,Outcome.done.injEq] at called
      obtain ⟨rfl,rfl⟩ := called
      exact .nil
  | cons expression expressions ih =>
      cases one : build expression inputs before with
      | pending key state => simp only [buildMany,one,Outcome.bind] at called; cases called
      | done value middle =>
          cases tail : buildMany expressions inputs middle with
          | pending key state => simp only [buildMany,one,tail,Outcome.bind] at called; cases called
          | done remaining final =>
              simp only [buildMany,one,tail,Outcome.bind,Outcome.done.injEq] at called
              obtain ⟨rfl,rfl⟩ := called
              have middleContext : Context middle inputs := by simpa only [one,Outcome.state] using context.build expression
              have tailGrowth : Grows middle reader := grows_trans
                (by simpa only [tail,Outcome.state] using
                  (buildMany_verified expressions inputs middle middleContext.base.normal.facts middleContext.base.inputs).growth) growth
              exact .cons ⟨before,middle,context,one,tailGrowth,
                InternedFreshOrdinaryReplay.build_replay expression inputs before reader value middle
                  context.base.normal.facts.coherent.valid one tailGrowth⟩
                (ih middle middleContext remaining tail)

private theorem children_generated [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (first second : Environment Symbol Guard) (reader : State Symbol Guard) (ready : Ready reader)
    (aliases : ∀ child ∈ expressions, Aliases child inputs firstNames secondNames)
    (paired : Inputs reader first second (inputs.map (input firstNames)) (inputs.map (input secondNames)))
    (firstReplacements : Replacements reader first) (secondReplacements : Replacements reader second)
    (rawFirst rawSecond left right : List (Value Symbol Guard))
    (firstSource : All₂ (fun expression value => SourceCall expression (inputs.map (input firstNames)) reader value) expressions rawFirst)
    (secondSource : All₂ (fun expression value => SourceCall expression (inputs.map (input secondNames)) reader value) expressions rawSecond)
    (firstAvailable : Values reader rawFirst) (secondAvailable : Values reader rawSecond)
    (firstCalls : All₂ (fun raw value => execute raw first reader = .done value reader) rawFirst left)
    (secondCalls : All₂ (fun raw value => execute raw second reader = .done value reader) rawSecond right) :
    All₂ (Mutual (Generated reader)) left right := by
  induction firstSource generalizing rawSecond left right with
  | nil => cases secondSource; cases firstCalls; cases secondCalls; exact .nil
  | @cons expression raw expressions raws firstSource remaining ih =>
      cases secondSource with
      | @cons _ other _ others secondSource secondRemaining =>
          cases firstCalls with
          | cons firstDone firstRest =>
              cases secondCalls with
              | cons secondDone secondRest =>
                  obtain ⟨before,after,firstContext,firstBuild,firstGrowth,_⟩ := firstSource
                  obtain ⟨later,final,secondContext,secondBuild,secondGrowth,_⟩ := secondSource
                  exact .cons (SourceCurrentGeneratedNodeSchedules.historical_pair expression inputs firstNames secondNames first second reader before later after final
                    ready firstContext secondContext (aliases expression List.mem_cons_self) paired firstReplacements secondReplacements
                    raw other _ _ firstBuild secondBuild firstGrowth secondGrowth
                    (firstAvailable raw List.mem_cons_self) (secondAvailable other List.mem_cons_self) firstDone secondDone)
                    (ih (fun child member => aliases child (List.mem_cons_of_mem _ member)) _ _ _ secondRemaining
                      (fun value member => firstAvailable value (List.mem_cons_of_mem _ member))
                      (fun value member => secondAvailable value (List.mem_cons_of_mem _ member)) firstRest secondRest)

private theorem rows_length [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (before : State Symbol Guard)
    (outputs : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (actual : buildEdges expressions environment before = .done outputs after) :
    expressions.length = outputs.length := by
  induction expressions generalizing before outputs with
  | nil =>
      simp only [buildEdges,Outcome.done.injEq] at actual
      obtain ⟨rfl,rfl⟩ := actual
      rfl
  | cons expression expressions ih =>
      cases expression with
      | mk symbol guard children =>
        cases child : buildMany children environment before with
        | pending key state => simp only [buildEdges,child,Outcome.bind] at actual; cases actual
        | done values middle =>
          let edge := run (makeEdge symbol guard values) middle
          cases rest : buildEdges expressions environment edge.2 with
          | pending key state =>
              simp only [buildEdges,child,Outcome.bind,work] at actual
              change (buildEdges expressions environment edge.2).bind _ = _ at actual
              simp only [rest,Outcome.bind] at actual
              cases actual
          | done tail final =>
              simp only [buildEdges,child,Outcome.bind,work] at actual
              change (buildEdges expressions environment edge.2).bind _ = _ at actual
              simp only [rest,Outcome.bind,Outcome.done.injEq] at actual
              obtain ⟨rfl,rfl⟩ := actual
              simp only [List.length_cons,ih edge.2 tail rest]

private theorem node_parts [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (before after : State Symbol Guard)
    (value : Value Symbol Guard) (actual : build (.node expressions) environment before = .done value after) :
    ∃ rows middle, buildEdges expressions environment before = .done rows middle ∧
      run (makeNode rows) middle = (value,after) := by
  cases called : buildEdges expressions environment before with
  | pending key state => simp only [build,called,Outcome.bind] at actual; cases actual
  | done rows middle =>
      have same := Outcome.done.inj (by simpa only [build,called,Outcome.bind,work] using actual)
      exact ⟨rows,middle,rfl,Prod.ext same.1 same.2⟩


private theorem physical_children (reader : State Symbol Guard) (value : Value Symbol Guard)
    (available : Available reader value) (row : EdgeValue Symbol Guard) (selected : row ∈ nodeEdges value) :
    Values reader row.children := by
  intro child member
  cases value with
  | empty | reference | union | mu => cases selected
  | node entry rows level free =>
      exact available.children child (List.mem_flatMap.mpr ⟨row,selected,member⟩)

/-- Actual row calls retain the same historical source index, full fields, and ordered child generators. -/
theorem node [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (first second : Environment Symbol Guard) (reader before after later final : State Symbol Guard)
    (ready : Ready reader)
    (firstContext : Context before (inputs.map (input firstNames)))
    (secondContext : Context later (inputs.map (input secondNames)))
    (aliases : Aliases (.node expressions) inputs firstNames secondNames)
    (paired : Inputs reader first second (inputs.map (input firstNames)) (inputs.map (input secondNames)))
    (firstReplacements : Replacements reader first) (secondReplacements : Replacements reader second)
    (rawFirst rawSecond : Value Symbol Guard)
    (firstBuild : build (.node expressions) (inputs.map (input firstNames)) before = .done rawFirst after)
    (secondBuild : build (.node expressions) (inputs.map (input secondNames)) later = .done rawSecond final)
    (firstGrowth : Grows after reader) (secondGrowth : Grows final reader)
    (firstAvailable : Available reader rawFirst) (secondAvailable : Available reader rawSecond)
    (row firstOutput : EdgeValue Symbol Guard) (selected : row ∈ nodeEdges rawFirst)
    (firstCalls : RowCalls first reader row firstOutput)
    (oppositeCalls : ∀ original ∈ nodeEdges rawSecond, ∃ output, RowCalls second reader original output) :
    ∃ firstRows firstAfter secondRows secondAfter index symbol guard children,
      ∃ (firstRow : RowCall expressions (inputs.map (input firstNames)) before firstRows firstAfter reader index symbol guard children)
        (secondRow : RowCall expressions (inputs.map (input secondNames)) later secondRows secondAfter reader index symbol guard children),
      buildEdges expressions (inputs.map (input firstNames)) before = .done firstRows firstAfter ∧
      run (makeNode firstRows) firstAfter = (rawFirst,after) ∧
      buildEdges expressions (inputs.map (input secondNames)) later = .done secondRows secondAfter ∧
      run (makeNode secondRows) secondAfter = (rawSecond,final) ∧
      firstRow.output = row ∧ secondRow.output ∈ nodeEdges rawSecond ∧
      buildMany children (inputs.map (input firstNames)) reader = .done firstRow.values reader ∧
      buildMany children (inputs.map (input secondNames)) reader = .done secondRow.values reader ∧
      ∃ secondOutput,
        RowCalls second reader secondRow.output secondOutput ∧
        firstOutput.entry.key.symbol = secondOutput.entry.key.symbol ∧
        firstOutput.entry.key.constraint = secondOutput.entry.key.constraint ∧
        All₂ (Mutual (Generated reader)) firstOutput.children secondOutput.children := by
  obtain ⟨firstRows,firstAfter,firstRowsDone,firstMade⟩ := node_parts expressions _ before after rawFirst firstBuild
  obtain ⟨secondRows,secondAfter,secondRowsDone,secondMade⟩ := node_parts expressions _ later final rawSecond secondBuild
  have firstChecked := buildEdges_verified expressions _ before firstContext.base.normal.facts firstContext.base.inputs
  have secondChecked := buildEdges_verified expressions _ later secondContext.base.normal.facts secondContext.base.inputs
  have firstFacts : InternedNestedFacts.Facts firstAfter := by simpa only [firstRowsDone,Outcome.state] using firstChecked.facts
  have secondFacts : InternedNestedFacts.Facts secondAfter := by simpa only [secondRowsDone,Outcome.state] using secondChecked.facts
  have firstEdges := firstChecked.result firstRows firstAfter firstRowsDone
  have secondEdges := secondChecked.result secondRows secondAfter secondRowsDone
  have firstPhysical := EqualityLeafProjectionPhysical.makeNode_edges firstRows firstAfter firstFacts.coherent firstFacts.linked firstEdges
  have secondPhysical := EqualityLeafProjectionPhysical.makeNode_edges secondRows secondAfter secondFacts.coherent secondFacts.linked secondEdges
  rw [firstMade] at firstPhysical
  rw [secondMade] at secondPhysical
  have selectedRaw := selected
  rw [firstPhysical] at selectedRaw
  obtain ⟨member,alive⟩ := (EqualityLeafProjectionPhysical.normalized_member firstAfter firstFacts.coherent firstRows firstEdges row).mp selectedRaw
  obtain ⟨index,found⟩ := List.mem_iff_getElem?.mp member
  have bounded : index < expressions.length := by
    rw [rows_length expressions _ before firstRows firstAfter firstRowsDone]
    exact (List.getElem?_eq_some_iff.mp found).1
  let expression := expressions[index]
  have source : expressions[index]? = some expression := List.getElem?_eq_getElem bounded
  cases shape : expression with
  | mk symbol guard children =>
    rw [shape] at source
    have firstRowsGrowth : Grows firstAfter reader := grows_trans
      (by simpa only [firstMade] using (run_correct (makeNode firstRows) firstAfter firstFacts.coherent.valid).2) firstGrowth
    have secondRowsGrowth : Grows secondAfter reader := grows_trans
      (by simpa only [secondMade] using (run_correct (makeNode secondRows) secondAfter secondFacts.coherent.valid).2) secondGrowth
    obtain ⟨firstRow⟩ := row_call expressions _ before firstAfter reader firstContext.base firstRows firstRowsDone firstRowsGrowth
      index symbol guard children source
    obtain ⟨secondRow⟩ := row_call expressions _ later secondAfter reader secondContext.base secondRows secondRowsDone secondRowsGrowth
      index symbol guard children source
    have same : firstRow.output = row := Option.some.inj (firstRow.selected.symm.trans found)
    have firstAlive : firstRow.values.any (fun value => value.referenceOf == .empty) = false := by
      rw [←firstRow.children_eq,same]
      simpa only [EqualityLeafProjectionPhysical.dead] using alive
    have secondAlive := (many_empty children inputs firstNames secondNames firstRow.current firstRow.middle
      secondRow.current secondRow.middle firstRow.context secondRow.context firstRow.values secondRow.values
      firstRow.called secondRow.called).symm.trans firstAlive
    have secondMember : secondRow.output ∈ nodeEdges rawSecond := by
      rw [secondPhysical]
      apply (EqualityLeafProjectionPhysical.normalized_member secondAfter secondFacts.coherent secondRows secondEdges secondRow.output).mpr
      refine ⟨List.mem_of_getElem? secondRow.selected,?_⟩
      simpa only [EqualityLeafProjectionPhysical.dead,secondRow.children_eq] using secondAlive
    have firstValues : Values reader firstRow.values := by
      rw [←firstRow.children_eq,same]
      exact physical_children reader rawFirst firstAvailable row selected
    have secondValues : Values reader secondRow.values := by
      rw [←secondRow.children_eq]
      exact physical_children reader rawSecond secondAvailable secondRow.output secondMember
    have firstChildContext : Context firstRow.current (inputs.map (input firstNames)) := by
      simpa only [firstRow.earlier,Outcome.state] using firstContext.edges (expressions.take index)
    have secondChildContext : Context secondRow.current (inputs.map (input secondNames)) := by
      simpa only [secondRow.earlier,Outcome.state] using secondContext.edges (expressions.take index)
    have firstSources := source_children children _ firstRow.current firstRow.middle reader firstChildContext firstRow.values
      firstRow.called firstRow.middle_growth
    have secondSources := source_children children _ secondRow.current secondRow.middle reader secondChildContext secondRow.values
      secondRow.called secondRow.middle_growth
    have live := source_live children inputs firstNames firstRow.current firstRow.middle firstRow.context firstRow.values
      firstRow.called firstAlive
    have childAliases := live_aliases expressions inputs firstNames secondNames aliases symbol guard children
      (List.mem_of_getElem? source) live
    obtain ⟨secondOutput,secondCalls⟩ := oppositeCalls secondRow.output secondMember
    have rawSymbol : row.entry.key.symbol = secondRow.output.entry.key.symbol :=
      (same ▸ firstRow.symbol_eq).trans secondRow.symbol_eq.symm
    have rawGuard : row.entry.key.constraint = secondRow.output.entry.key.constraint :=
      (same ▸ firstRow.guard_eq).trans secondRow.guard_eq.symm
    have symbolEq := firstCalls.2.2.1.trans (rawSymbol.trans secondCalls.2.2.1.symm)
    have guardEq := firstCalls.2.2.2.1.trans (rawGuard.trans secondCalls.2.2.2.1.symm)
    have firstWarm := SourceCurrentStoredCallsReplay.replay firstCalls.1 reader ready.semantic.1.normal.facts.coherent.valid (grows_refl _)
    have secondWarm := SourceCurrentStoredCallsReplay.replay secondCalls.1 reader ready.semantic.1.normal.facts.coherent.valid (grows_refl _)
    have generated := children_generated children inputs firstNames secondNames first second reader ready childAliases paired
      firstReplacements secondReplacements firstRow.values secondRow.values firstOutput.children secondOutput.children
      firstSources secondSources firstValues secondValues
      (by simpa only [←same,firstRow.children_eq] using firstWarm)
      (by simpa only [secondRow.children_eq] using secondWarm)
    exact ⟨firstRows,firstAfter,secondRows,secondAfter,index,symbol,guard,children,firstRow,secondRow,
      firstRowsDone,firstMade,secondRowsDone,secondMade,same,secondMember,
      InternedFreshOrdinaryReplay.buildMany_replays children _ firstRow.current reader firstRow.values firstRow.middle
        firstRow.context.normal.facts.coherent.valid firstRow.called firstRow.middle_growth,
      InternedFreshOrdinaryReplay.buildMany_replays children _ secondRow.current reader secondRow.values secondRow.middle
        secondRow.context.normal.facts.coherent.valid secondRow.called secondRow.middle_growth,
      secondOutput,secondCalls,symbolEq,guardEq,generated⟩

end MicroCFTA.SourceCurrentGeneratedRowSchedules
