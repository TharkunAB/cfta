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
open SourceCurrentNativeNormalizationInputs (support)
open SourceCurrentOpenPreorderSimulation (Mutual)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentStoredMuRetainedAlignment (RowCall)
open SourceCurrentStoredNodeExpansion (RowCalls)

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
          have middleContext : Context middle environment := by
            simpa only [childDone,Outcome.state] using context.many ownChildren
          have childrenAvailable := childChecked.result values middle childDone
          have edgeChecked := InternedNestedFacts.edge_verified ownSymbol ownGuard values middle
            middleContext.normal.facts childrenAvailable
          have nextContext : Context made.2 environment := middleContext.edge ownSymbol ownGuard values childrenAvailable
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


end MicroCFTA.SourceCurrentGeneratedNodeSchedules
