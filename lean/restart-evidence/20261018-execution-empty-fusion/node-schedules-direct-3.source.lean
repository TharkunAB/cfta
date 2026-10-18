import MicroCFTA.SourceCurrentGeneratedNodeCases

/-!
# Historical node schedules at a retained reader

A surviving raw row retains its children at the reader. Its actual source
history supplies each child context and its exact warm replay. Live source
support gives fresh filter names without reader availability for unused
lexical inputs. Actual parent reconstruction supplies every stored child call.
The result does not assert survival of the opposite stored row.
-/
namespace MicroCFTA.SourceCurrentGeneratedNodeSchedules
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


private theorem fresh_free (reader : State Symbol Guard) (ready : Ready reader)
    (value : Value Symbol Guard) (available : Available reader value) :
    Reference.interned reader.nodes.next ∉ value.free := by
  intro member
  obtain ⟨key,issued⟩ := available.issued _ member
  exact Nat.lt_irrefl _ (ready.semantic.1.normal.facts.coherent.valid.2.1 _ _ issued)

private theorem filter_absent [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (value : Value Symbol Guard)
    (reader : State Symbol Guard) (ready : Ready reader) (available : Available reader value)
    (absent : name ∉ value.free) : run (withoutSelfReference name value) reader = (value,reader) := by
  cases value with
  | empty | reference | node | mu => rfl
  | union entry members level free =>
      rw [withoutSelfReference_absent name entry members level free]
      · rfl
      · intro member
        exact absent ((InternedNormalizationFree.unionMembers_free reader ready.semantic.1.normal.facts.coherent
          (.union entry members level free) available name).mpr
            ⟨.reference name,member,by simp only [Value.free,List.mem_singleton]⟩)


private theorem fresh_scope [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (names : Atom → Reference) (before after reader : State Symbol Guard)
    (context : Context before (inputs.map (input names))) (raw : Value Symbol Guard)
    (called : build expression (inputs.map (input names)) before = .done raw after)
    (ready : Ready reader) (available : Available reader raw) :
    Reference.interned reader.nodes.next ∉ (Scope expression inputs).map (Sum.elim id names) := by
  intro member
  simp only [Scope,List.map_cons,Sum.elim_inl,id_eq,List.mem_cons,reduceCtorEq,false_or] at member
  exact fresh_free reader ready raw available
    ((SourceCurrentNativeNormalizationInputs.actual_free expression inputs names before after context.base raw called _).mpr member)

private theorem generate [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) (first second : Environment Symbol Guard)
    (reader before later after final : State Symbol Guard) (ready : Ready reader)
    (firstContext : Context before (inputs.map (input firstNames)))
    (secondContext : Context later (inputs.map (input secondNames)))
    (aliases : Aliases expression inputs firstNames secondNames)
    (paired : Inputs reader first second (inputs.map (input firstNames)) (inputs.map (input secondNames)))
    (firstReplacements : Replacements reader first) (secondReplacements : Replacements reader second)
    (rawFirst rawSecond left right : Value Symbol Guard)
    (firstBuild : build expression (inputs.map (input firstNames)) before = .done rawFirst after)
    (secondBuild : build expression (inputs.map (input secondNames)) later = .done rawSecond final)
    (firstGrowth : Grows after reader) (secondGrowth : Grows final reader)
    (firstAvailable : Available reader rawFirst) (secondAvailable : Available reader rawSecond)
    (firstDone : execute rawFirst first reader = .done left reader)
    (secondDone : execute rawSecond second reader = .done right reader) : Generated reader left right := by
  have firstFilter := filter_absent (.interned reader.nodes.next) rawFirst reader ready firstAvailable
    (fresh_free reader ready rawFirst firstAvailable)
  have secondFilter := filter_absent (.interned reader.nodes.next) rawSecond reader ready secondAvailable
    (fresh_free reader ready rawSecond secondAvailable)
  have firstFresh := fresh_scope expression inputs firstNames before after reader firstContext rawFirst firstBuild ready firstAvailable
  have secondFresh := fresh_scope expression inputs secondNames later final reader secondContext rawSecond secondBuild ready secondAvailable
  have firstChecked := build_verified expression _ before firstContext.base.normal.facts firstContext.base.inputs
  have secondChecked := build_verified expression _ later secondContext.base.normal.facts secondContext.base.inputs
  have firstFacts : InternedNestedFacts.Facts after := by simpa only [firstBuild,Outcome.state] using firstChecked.facts
  have secondFacts : InternedNestedFacts.Facts final := by simpa only [secondBuild,Outcome.state] using secondChecked.facts
  have firstRawAvailable := firstChecked.result rawFirst after firstBuild
  have secondRawAvailable := secondChecked.result rawSecond final secondBuild
  have firstAbsent : .interned reader.nodes.next ∉ rawFirst.free := fresh_free reader ready rawFirst firstAvailable
  have secondAbsent : .interned reader.nodes.next ∉ rawSecond.free := fresh_free reader ready rawSecond secondAvailable
  have historicalFirst : run (withoutSelfReference (.interned reader.nodes.next) rawFirst) after = (rawFirst,after) := by
    cases rawFirst with
    | empty | reference | node | mu => rfl
    | union entry members level free =>
        rw [withoutSelfReference_absent]
        · rfl
        · intro member
          exact firstAbsent ((InternedNormalizationFree.unionMembers_free after firstFacts.coherent
            (.union entry members level free) firstRawAvailable _).mpr
              ⟨.reference (.interned reader.nodes.next),member,by simp only [Value.free,List.mem_singleton]⟩)
  have historicalSecond : run (withoutSelfReference (.interned reader.nodes.next) rawSecond) final = (rawSecond,final) := by
    cases rawSecond with
    | empty | reference | node | mu => rfl
    | union entry members level free =>
        rw [withoutSelfReference_absent]
        · rfl
        · intro member
          exact secondAbsent ((InternedNormalizationFree.unionMembers_free final secondFacts.coherent
            (.union entry members level free) secondRawAvailable _).mpr
              ⟨.reference (.interned reader.nodes.next),member,by simp only [Value.free,List.mem_singleton]⟩)
  have tests : ∀ label ∈ Scope expression inputs,
      Sum.elim id firstNames label = .interned reader.nodes.next ↔
        Sum.elim id secondNames label = .interned reader.nodes.next := by
    intro label member
    exact iff_of_false (fun same => firstFresh (List.mem_map.mpr ⟨label,member,same⟩))
      (fun same => secondFresh (List.mem_map.mpr ⟨label,member,same⟩))
  exact Generated.filtered expression inputs firstNames secondNames
    (.interned reader.nodes.next) (.interned reader.nodes.next) first second
    before later after final after final rawFirst rawSecond rawFirst rawSecond left right ready
    firstContext secondContext aliases tests paired firstReplacements secondReplacements firstAvailable secondAvailable
    firstBuild secondBuild historicalFirst historicalSecond firstGrowth secondGrowth firstGrowth secondGrowth
    (InternedFreshOrdinaryReplay.build_replay expression _ before reader rawFirst after
      firstContext.base.normal.facts.coherent.valid firstBuild firstGrowth)
    (InternedFreshOrdinaryReplay.build_replay expression _ later reader rawSecond final
      secondContext.base.normal.facts.coherent.valid secondBuild secondGrowth)
    firstFilter secondFilter firstDone secondDone

/-- Historical raw calls derive both child generators without reader-wide lexical availability. -/
theorem historical_pair [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) (first second : Environment Symbol Guard)
    (reader before later after final : State Symbol Guard) (ready : Ready reader)
    (firstContext : Context before (inputs.map (input firstNames)))
    (secondContext : Context later (inputs.map (input secondNames)))
    (aliases : Aliases expression inputs firstNames secondNames)
    (paired : Inputs reader first second (inputs.map (input firstNames)) (inputs.map (input secondNames)))
    (firstReplacements : Replacements reader first) (secondReplacements : Replacements reader second)
    (rawFirst rawSecond left right : Value Symbol Guard)
    (firstBuild : build expression (inputs.map (input firstNames)) before = .done rawFirst after)
    (secondBuild : build expression (inputs.map (input secondNames)) later = .done rawSecond final)
    (firstGrowth : Grows after reader) (secondGrowth : Grows final reader)
    (firstAvailable : Available reader rawFirst) (secondAvailable : Available reader rawSecond)
    (firstDone : execute rawFirst first reader = .done left reader)
    (secondDone : execute rawSecond second reader = .done right reader) :
    Mutual (Generated reader) left right :=
  ⟨generate expression inputs firstNames secondNames first second reader before later after final ready
    firstContext secondContext aliases paired firstReplacements secondReplacements rawFirst rawSecond left right
    firstBuild secondBuild firstGrowth secondGrowth firstAvailable secondAvailable firstDone secondDone,
   generate expression inputs secondNames firstNames second first reader later before final after ready
    secondContext firstContext (fun a ha b hb => (aliases a ha b hb).symm) (reverse_inputs paired)
    secondReplacements firstReplacements rawSecond rawFirst right left secondBuild firstBuild
    secondGrowth firstGrowth secondAvailable firstAvailable secondDone firstDone⟩

variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem row_call (expressions : List (EdgeSyntax Symbol Guard)) (environment : List (Value Symbol Guard))
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


private theorem source_live (children : List (Syntax Symbol Guard))
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

private theorem empty_same (expression : Syntax Symbol Guard)
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

private theorem many_empty (expressions : List (Syntax Symbol Guard))
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

private def SourceCall (expression : Syntax Symbol Guard) (inputs : List (Value Symbol Guard))
    (reader : State Symbol Guard) (value : Value Symbol Guard) : Prop :=
  ∃ before after, Context before inputs ∧ build expression inputs before = .done value after ∧
    Grows after reader ∧ build expression inputs reader = .done value reader

private theorem source_children (expressions : List (Syntax Symbol Guard)) (inputs : List (Value Symbol Guard))
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

private theorem children_generated (expressions : List (Syntax Symbol Guard))
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
                  exact .cons (historical_pair expression inputs firstNames secondNames first second reader before later after final
                    ready firstContext secondContext (aliases expression List.mem_cons_self) paired firstReplacements secondReplacements
                    raw other _ _ firstBuild secondBuild firstGrowth secondGrowth
                    (firstAvailable raw List.mem_cons_self) (secondAvailable other List.mem_cons_self) firstDone secondDone)
                    (ih (fun child member => aliases child (List.mem_cons_of_mem _ member)) _ _ _ secondRemaining
                      (fun value member => firstAvailable value (List.mem_cons_of_mem _ member))
                      (fun value member => secondAvailable value (List.mem_cons_of_mem _ member)) firstRest secondRest)

end MicroCFTA.SourceCurrentGeneratedNodeSchedules
