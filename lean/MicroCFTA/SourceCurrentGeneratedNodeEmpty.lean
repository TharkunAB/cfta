import MicroCFTA.SourceCurrentGeneratedNodeSchedules

/-!
# Physical Empty from strict source child fusion

Historical node builds and actual stored reconstructions supply every
ordered child call. Empty agreement for the strict source children keeps
both reconstructed row sets live at the same source positions. The proof
assumes no parent output relation and no lexical availability at the reader.
-/
namespace MicroCFTA.SourceCurrentGeneratedNodeEmpty
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedNestedProvenance (Values)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryLiveInputs (input inputProfile)
open InternedStoredSubstitution (Environment Replacements leaves encode)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedBinderProtocol (Reference)
open InternedEdgeResidency (nodeEdges)
open SourceEqualityRequiredCache (Ready Ordinary)
open SourceCurrentRetainedMuDirectedCase (Generated Inputs)
open SourceCurrentUsedBinderAliasTransport (Aliases Scope)
open SourceCurrentNativeNormalizationInputs (support inputNames)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentStoredNodeExpansion (RowCalls)
variable {Atom : Type}

/-- Actual reconstruction of one source expression preserves Empty across paired lexical inputs. -/
def Fusion [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) : Prop :=
  ∀ {Atom : Type} (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) (first second : Environment Symbol Guard)
    (reader before after later final : State Symbol Guard) (_ready : Ready reader)
    (_firstContext : Context before (inputs.map (input firstNames)))
    (_secondContext : Context later (inputs.map (input secondNames)))
    (_aliases : Aliases expression inputs firstNames secondNames)
    (_paired : Inputs reader first second (inputs.map (input firstNames)) (inputs.map (input secondNames)))
    (_firstReplacements : Replacements reader first) (_secondReplacements : Replacements reader second)
    (rawFirst rawSecond left right : Value Symbol Guard)
    (_firstBuild : build expression (inputs.map (input firstNames)) before = .done rawFirst after)
    (_secondBuild : build expression (inputs.map (input secondNames)) later = .done rawSecond final)
    (_firstGrowth : Grows after reader) (_secondGrowth : Grows final reader)
    (_firstAvailable : Available reader rawFirst) (_secondAvailable : Available reader rawSecond)
    (_firstDone : execute rawFirst first reader = .done left reader)
    (_secondDone : execute rawSecond second reader = .done right reader),
    (left.referenceOf == .empty) = (right.referenceOf == .empty)

private theorem reverse_inputs [DecidableEq (EdgeKey Symbol Guard)] {reader : State Symbol Guard}
    {first second : Environment Symbol Guard} {left right : List (Value Symbol Guard)}
    (paired : Inputs reader first second left right) : Inputs reader second first right left := by
  refine Inputs.rec (motive_1 := fun _ _ _ => True)
    (motive_2 := fun first second left right _ => Inputs reader second first right left)
    (fun _ => True.intro) ?_ (fun first second => .nil second first) ?_ ?_ paired
  · intros
    trivial
  · intro first second a b left right forward backward tail _ _ ih
    exact .reference backward forward ih
  · intro first second left right value agree tail ih
    exact .fixed value (fun name member => (agree name member).symm) ih


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

private theorem children_fusion [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (ih : ∀ child ∈ expressions, Fusion child)
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
    All₂ (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty)) left right := by
  induction firstSource generalizing rawSecond left right with
  | nil => cases secondSource; cases firstCalls; cases secondCalls; exact .nil
  | @cons expression raw expressions raws firstSource remaining induct =>
      cases secondSource with
      | @cons _ other _ others secondSource secondRemaining =>
          cases firstCalls with
          | cons firstDone firstRest =>
              cases secondCalls with
              | cons secondDone secondRest =>
                  obtain ⟨before,after,firstContext,firstBuild,firstGrowth,_⟩ := firstSource
                  obtain ⟨later,final,secondContext,secondBuild,secondGrowth,_⟩ := secondSource
                  refine .cons (ih expression List.mem_cons_self inputs firstNames secondNames first second
                    reader before after later final ready firstContext secondContext
                    (aliases expression List.mem_cons_self) paired firstReplacements secondReplacements
                    raw other _ _ firstBuild secondBuild firstGrowth secondGrowth
                    (firstAvailable raw List.mem_cons_self) (secondAvailable other List.mem_cons_self) firstDone secondDone) ?_
                  exact induct (fun child member => ih child (List.mem_cons_of_mem _ member))
                    (fun child member => aliases child (List.mem_cons_of_mem _ member)) _ _ _ secondRemaining
                    (fun value member => firstAvailable value (List.mem_cons_of_mem _ member))
                    (fun value member => secondAvailable value (List.mem_cons_of_mem _ member)) firstRest secondRest

private theorem node_parts [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (inputs : List (Value Symbol Guard)) (before after : State Symbol Guard) (value : Value Symbol Guard)
    (actual : build (.node expressions) inputs before = .done value after) :
    ∃ rows middle, buildEdges expressions inputs before = .done rows middle ∧
      run (makeNode rows) middle = (value,after) := by
  cases built : buildEdges expressions inputs before with
  | pending key state => simp only [build,built,Outcome.bind] at actual; cases actual
  | done rows middle =>
      have same := Outcome.done.inj (by simpa only [build,built,Outcome.bind,InternedNestedConstruction.work] using actual)
      exact ⟨rows,middle,rfl,Prod.ext same.1 same.2⟩

private theorem raw_ordinary [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (inputs : List (Value Symbol Guard)) (before after : State Symbol Guard)
    (context : Context before inputs) (value : Value Symbol Guard)
    (actual : build (.node expressions) inputs before = .done value after) : Ordinary value := by
  obtain ⟨rows,middle,called,made⟩ := node_parts expressions inputs before after value actual
  have checked := buildEdges_verified expressions inputs before context.base.normal.facts context.base.inputs
  have facts : InternedNestedFacts.Facts middle := by simpa only [called,Outcome.state] using checked.facts
  have ordinary := SourceEqualityRequiredCache.node_ordinary rows middle facts (checked.result rows middle called)
  simpa only [made] using ordinary

private theorem stored_ordinary [DecidableEq (EdgeKey Symbol Guard)] (raw result : Value Symbol Guard)
    (environment : Environment Symbol Guard) (reader : State Symbol Guard) (ready : Ready reader)
    (ordinary : Ordinary raw) (available : Available reader raw) (replacements : Replacements reader environment)
    (called : execute raw environment reader = .done result reader) : Ordinary result := by
  cases raw with
  | empty =>
      have same := (Outcome.done.inj ((SourceCurrentStoredUnionObservations.closed .empty environment reader rfl).symm.trans called)).1
      subst result
      trivial
  | node entry rows level free =>
      obtain ⟨_,_,plain,_⟩ := SourceCurrentStoredNodeExpansion.node_warm entry rows level free environment reader
        ready.semantic.1.normal available replacements result called
      exact plain
  | reference | union | mu => cases ordinary

private theorem physical_children (reader : State Symbol Guard) (value : Value Symbol Guard)
    (available : Available reader value) (row : EdgeValue Symbol Guard) (selected : row ∈ nodeEdges value) :
    Values reader row.children := by
  cases value with
  | empty | reference | union | mu => cases selected
  | node entry rows level free =>
      intro child member
      exact available.children child (List.mem_flatMap.mpr ⟨row,selected,member⟩)

private theorem literal_row (value : Value Symbol Guard) (row : EdgeValue Symbol Guard)
    (ordinary : Ordinary value) : SourceCurrentLiteralRootParts.Row value row ↔ row ∈ nodeEdges value := by
  cases value with
  | empty =>
      constructor
      · intro impossible; cases impossible
      · intro impossible; cases impossible
  | node => exact SourceCurrentLiteralRootParts.row_node _ _ _ _ _
  | reference | union | mu => cases ordinary

private theorem no_atom (value : Value Symbol Guard) (ordinary : Ordinary value) :
    ∀ atom, ¬ SourceCurrentLiteralRootParts.Literal value atom := by
  cases value with
  | empty | node => intro atom impossible; cases impossible
  | reference | union | mu => cases ordinary

private theorem row_unique [DecidableEq (EdgeKey Symbol Guard)] (reader : State Symbol Guard)
    (ready : Ready reader) (environment : Environment Symbol Guard) (raw first second : EdgeValue Symbol Guard)
    (left : RowCalls environment reader raw first) (right : RowCalls environment reader raw second) : first = second := by
  have same := SourceCurrentStoredCallsReplay.same left.1 right.1 reader
    ready.semantic.1.normal.facts.coherent.valid ready.semantic.1.normal.facts.coherent.valid (grows_refl _) (grows_refl _)
  have made := left.2.1
  rw [same] at made
  exact congrArg Prod.fst (made.symm.trans right.2.1)

private theorem any_empty {first second : List (Value Symbol Guard)}
    (paired : All₂ (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty)) first second) :
    first.any (fun value => value.referenceOf == .empty) = second.any (fun value => value.referenceOf == .empty) := by
  induction paired with
  | nil => rfl
  | cons head tail ih => simp only [List.any_cons,head,ih]

/-- A surviving reconstructed row has an actual opposite survivor with equal ordered Empty tests. -/
theorem row [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (ih : ∀ symbol guard children, EdgeSyntax.mk symbol guard children ∈ expressions → ∀ child ∈ children, Fusion child)
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (first second : Environment Symbol Guard) (reader before after later final : State Symbol Guard)
    (ready : Ready reader)
    (firstContext : Context before (inputs.map (input firstNames)))
    (secondContext : Context later (inputs.map (input secondNames)))
    (aliases : Aliases (.node expressions) inputs firstNames secondNames)
    (paired : Inputs reader first second (inputs.map (input firstNames)) (inputs.map (input secondNames)))
    (firstReplacements : Replacements reader first) (secondReplacements : Replacements reader second)
    (rawFirst rawSecond left right : Value Symbol Guard)
    (firstBuild : build (.node expressions) (inputs.map (input firstNames)) before = .done rawFirst after)
    (secondBuild : build (.node expressions) (inputs.map (input secondNames)) later = .done rawSecond final)
    (firstGrowth : Grows after reader) (secondGrowth : Grows final reader)
    (firstAvailable : Available reader rawFirst) (secondAvailable : Available reader rawSecond)
    (firstDone : execute rawFirst first reader = .done left reader)
    (secondDone : execute rawSecond second reader = .done right reader)
    (row : EdgeValue Symbol Guard) (selected : row ∈ nodeEdges left) :
    ∃ other ∈ nodeEdges right,
      row.entry.key.symbol = other.entry.key.symbol ∧ row.entry.key.constraint = other.entry.key.constraint ∧
      All₂ (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty)) row.children other.children := by
  have firstPlain := raw_ordinary expressions _ before after firstContext rawFirst firstBuild
  have secondPlain := raw_ordinary expressions _ later final secondContext rawSecond secondBuild
  have leftPlain := stored_ordinary rawFirst left first reader ready firstPlain firstAvailable firstReplacements firstDone
  have rightPlain := stored_ordinary rawSecond right second reader ready secondPlain secondAvailable secondReplacements secondDone
  have firstParts := SourceCurrentStoredLiteralExecutionParts.parts rawFirst left first reader ready firstAvailable firstReplacements firstDone
  obtain ⟨raw,rawPart,actual,alive⟩ := ((firstParts.2 row).mp ((literal_row left row leftPlain).mpr selected)).resolve_left
    (by rintro ⟨atom,part,_,_,_⟩; exact no_atom rawFirst firstPlain atom part)
  have rawMember := (literal_row rawFirst raw firstPlain).mp rawPart
  obtain ⟨firstRows,firstAfter,secondRows,secondAfter,index,symbol,guard,children,firstRow,secondRow,
      firstRowsDone,firstMade,secondRowsDone,secondMade,same,secondMember,_,_,firstOutput,secondOutput,
      firstCalls,secondCalls,_⟩ := SourceCurrentGeneratedNodeSchedules.node expressions inputs firstNames secondNames
    first second reader before after later final ready firstContext secondContext aliases paired firstReplacements
    secondReplacements rawFirst rawSecond left right firstBuild secondBuild firstGrowth secondGrowth
    firstAvailable secondAvailable firstDone secondDone raw rawMember
  have sourceMember := List.mem_of_getElem? firstRow.source
  have firstAlive : firstRow.values.any (fun value => value.referenceOf == .empty) = false := by
    have live := InternedLiveEdges.resident_live reader ready.semantic.1.normal.live rawFirst firstAvailable.resident
    cases rawFirst with
    | node entry rows level free =>
        have rowLive := live raw rawMember
        simpa only [←firstRow.children_eq,same] using rowLive
    | empty | reference | union | mu => cases rawMember
  have childAliases := live_aliases expressions inputs firstNames secondNames aliases symbol guard children sourceMember
    (source_live children inputs firstNames firstRow.current firstRow.middle firstRow.context firstRow.values firstRow.called firstAlive)
  have firstChildContext : Context firstRow.current (inputs.map (input firstNames)) := by
    simpa only [firstRow.earlier,Outcome.state] using firstContext.edges (expressions.take index)
  have secondChildContext : Context secondRow.current (inputs.map (input secondNames)) := by
    simpa only [secondRow.earlier,Outcome.state] using secondContext.edges (expressions.take index)
  have firstSources := source_children children _ firstRow.current firstRow.middle reader firstChildContext firstRow.values
    firstRow.called firstRow.middle_growth
  have secondSources := source_children children _ secondRow.current secondRow.middle reader secondChildContext secondRow.values
    secondRow.called secondRow.middle_growth
  have firstValues : Values reader firstRow.values := by
    rw [←firstRow.children_eq,same]
    exact physical_children reader rawFirst firstAvailable raw rawMember
  have secondValues : Values reader secondRow.values := by
    rw [←secondRow.children_eq]
    exact physical_children reader rawSecond secondAvailable secondRow.output secondMember
  have firstWarm := SourceCurrentStoredCallsReplay.replay firstCalls.1 reader ready.semantic.1.normal.facts.coherent.valid (grows_refl _)
  have secondWarm := SourceCurrentStoredCallsReplay.replay secondCalls.1 reader ready.semantic.1.normal.facts.coherent.valid (grows_refl _)
  have pairedOutputs := children_fusion children (ih symbol guard children sourceMember) inputs firstNames secondNames
    first second reader ready childAliases paired firstReplacements secondReplacements
    firstRow.values secondRow.values firstOutput.children secondOutput.children firstSources secondSources firstValues secondValues
    (by simpa only [←same,firstRow.children_eq] using firstWarm)
    (by simpa only [secondRow.children_eq] using secondWarm)
  have equal := row_unique reader ready first raw row firstOutput actual firstCalls
  subst firstOutput
  have rightAlive : (!(secondOutput.children.any (fun value => value.referenceOf == .empty))) = true := by
    rw [←any_empty pairedOutputs]
    exact alive
  have secondParts := SourceCurrentStoredLiteralExecutionParts.parts rawSecond right second reader ready secondAvailable secondReplacements secondDone
  have survives := (secondParts.2 secondOutput).mpr (.inr ⟨secondRow.output,
    (literal_row rawSecond secondRow.output secondPlain).mpr secondMember,secondCalls,rightAlive⟩)
  refine ⟨secondOutput,(literal_row right secondOutput rightPlain).mp survives,?_,?_,pairedOutputs⟩
  · exact actual.2.2.1.trans (same ▸ firstRow.symbol_eq) |>.trans (secondRow.symbol_eq.symm.trans secondCalls.2.2.1.symm)
  · exact actual.2.2.2.1.trans (same ▸ firstRow.guard_eq) |>.trans (secondRow.guard_eq.symm.trans secondCalls.2.2.2.1.symm)

private theorem ordinary_empty (reader : State Symbol Guard) (ready : Ready reader)
    (value : Value Symbol Guard) (ordinary : Ordinary value) (available : Available reader value) :
    value.referenceOf = .empty ↔ ∀ row, row ∉ nodeEdges value := by
  cases value with
  | empty =>
      constructor
      · intro _ row impossible; cases impossible
      · intro _; rfl
  | node entry rows level free =>
      constructor
      · intro impossible; cases impossible
      · intro absent
        have nonempty := InternedNonemptyRecords.resident_nonempty reader ready.semantic.1.normal.proper _ available.resident
        cases rows with
        | nil => exact False.elim (nonempty rfl)
        | cons row rows => exact False.elim (absent row List.mem_cons_self)
  | reference | union | mu => cases ordinary

/-- Strict source child fusion derives physical Empty fusion for the complete actual node calls. -/
theorem node [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (ih : ∀ symbol guard children, EdgeSyntax.mk symbol guard children ∈ expressions → ∀ child ∈ children, Fusion child) :
    Fusion (.node expressions) := by
  intro Atom inputs firstNames secondNames first second reader before after later final ready firstContext secondContext
    aliases paired firstReplacements secondReplacements rawFirst rawSecond left right firstBuild secondBuild firstGrowth secondGrowth
    firstAvailable secondAvailable firstDone secondDone
  have firstPlain := raw_ordinary expressions _ before after firstContext rawFirst firstBuild
  have secondPlain := raw_ordinary expressions _ later final secondContext rawSecond secondBuild
  have leftPlain := stored_ordinary rawFirst left first reader ready firstPlain firstAvailable firstReplacements firstDone
  have rightPlain := stored_ordinary rawSecond right second reader ready secondPlain secondAvailable secondReplacements secondDone
  have leftAvailable := (build_verified (encode (leaves rawFirst) [] rawFirst)
    ((leaves rawFirst).map (InternedStoredSubstitution.input first)) reader ready.semantic.1.normal.facts
    (InternedStoredSubstitution.inputs_available rawFirst first reader firstAvailable firstReplacements)).result left reader firstDone
  have rightAvailable := (build_verified (encode (leaves rawSecond) [] rawSecond)
    ((leaves rawSecond).map (InternedStoredSubstitution.input second)) reader ready.semantic.1.normal.facts
    (InternedStoredSubstitution.inputs_available rawSecond second reader secondAvailable secondReplacements)).result right reader secondDone
  have equivalent : left.referenceOf = .empty ↔ right.referenceOf = .empty := by
    rw [ordinary_empty reader ready left leftPlain leftAvailable,ordinary_empty reader ready right rightPlain rightAvailable]
    constructor
    · intro absent other present
      obtain ⟨original,member,_,_,_⟩ := row expressions ih inputs secondNames firstNames second first
        reader later final before after ready secondContext firstContext (fun a ha b hb => (aliases a ha b hb).symm)
        (reverse_inputs paired) secondReplacements firstReplacements rawSecond rawFirst right left
        secondBuild firstBuild secondGrowth firstGrowth secondAvailable firstAvailable secondDone firstDone other present
      exact absent original member
    · intro absent original present
      obtain ⟨other,member,_,_,_⟩ := row expressions ih inputs firstNames secondNames first second
        reader before after later final ready firstContext secondContext aliases paired firstReplacements secondReplacements
        rawFirst rawSecond left right firstBuild secondBuild firstGrowth secondGrowth firstAvailable secondAvailable
        firstDone secondDone original present
      exact absent other member
  exact Bool.eq_iff_iff.mpr (by simpa only [beq_iff_eq] using equivalent)

end MicroCFTA.SourceCurrentGeneratedNodeEmpty
