import MicroCFTA.SourceCurrentBoundedFilteredFusion
import MicroCFTA.SourceCurrentGeneratedNodeSchedules

/-!
# Rank-bounded filtered node Empty fusion from strict children

Actual historical source rows retain their indexes and child calls.
Actual stored rows retain their ordered reconstructed children.
Bounded child fusion derives opposite row survival and parent Empty agreement.
Each selected original raw child inherits its surviving raw parent depth bound.
Dead source rows do not invoke the child hypothesis.
The lexical slot relation compares physical Empty tests only.
-/
namespace MicroCFTA.SourceCurrentBoundedFilteredNodeFusion
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work)
open InternedNestedProvenance (Values)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryLiveInputs (input inputProfile)
open InternedStoredSubstitution (Environment Replacements leaves encode)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedBinderProtocol (Reference)
open InternedEdgeResidency (nodeEdges)
open SourceEqualityRequiredCache (Ready Ordinary)
open SourceCurrentReaderReplacementSlots (Paired Slot)
open SourceCurrentBoundedFilteredFusion (Fusion)
open SourceCurrentStoredMuRetainedAlignment (RowCall)
open SourceCurrentUsedBinderAliasTransport (Aliases Scope)
open SourceCurrentNativeNormalizationInputs (support inputNames)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentStoredNodeExpansion (RowCalls)
variable {Atom : Type}

private theorem reverse_inputs {first second : Environment Symbol Guard}
    {left right : List (Value Symbol Guard)}
    (paired : Paired (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty)) first second left right) :
    Paired (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty)) second first right left := by
  induction paired with
  | nil => exact .nil
  | @cons left right lefts rights slot _ ih =>
      refine .cons ?_ ih
      cases left <;> cases right
      all_goals try {cases slot}
      case reference.reference a b => exact slot.symm
      all_goals obtain ⟨same,agree⟩ := slot
      all_goals cases same
      all_goals exact ⟨rfl,fun name member => (agree name member).symm⟩

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

private theorem children_fusion [DecidableEq (EdgeKey Symbol Guard)] (bound : Nat) (expressions : List (Syntax Symbol Guard))
    (ih : ∀ child ∈ expressions, Fusion bound child)
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (first second : Environment Symbol Guard) (reader : State Symbol Guard) (ready : Ready reader)
    (aliases : ∀ child ∈ expressions, Aliases child inputs firstNames secondNames)
    (paired : Paired (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty)) first second (inputs.map (input firstNames)) (inputs.map (input secondNames)))
    (firstReplacements : Replacements reader first) (secondReplacements : Replacements reader second)
    (rawFirst rawSecond left right : List (Value Symbol Guard))
    (firstSource : All₂ (fun expression value => SourceCall expression (inputs.map (input firstNames)) reader value) expressions rawFirst)
    (secondSource : All₂ (fun expression value => SourceCall expression (inputs.map (input secondNames)) reader value) expressions rawSecond)
    (firstAvailable : Values reader rawFirst) (secondAvailable : Values reader rawSecond)
    (firstCalls : All₂ (fun raw value => execute raw first reader = .done value reader) rawFirst left)
    (secondCalls : All₂ (fun raw value => execute raw second reader = .done value reader) rawSecond right)
    (firstDepth : ∀ value ∈ rawFirst, value.depth ≤ bound)
    (secondDepth : ∀ value ∈ rawSecond, value.depth ≤ bound) :
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
                  have firstRawAvailable := firstAvailable raw List.mem_cons_self
                  have secondRawAvailable := secondAvailable other List.mem_cons_self
                  have firstFresh := fresh_scope expression inputs firstNames before after reader firstContext raw firstBuild ready firstRawAvailable
                  have secondFresh := fresh_scope expression inputs secondNames later final reader secondContext other secondBuild ready secondRawAvailable
                  have tests : ∀ label ∈ Scope expression inputs,
                      Sum.elim id firstNames label = .interned reader.nodes.next ↔
                        Sum.elim id secondNames label = .interned reader.nodes.next := by
                    intro label member
                    exact iff_of_false (fun same => firstFresh (List.mem_map.mpr ⟨label,member,same⟩))
                      (fun same => secondFresh (List.mem_map.mpr ⟨label,member,same⟩))
                  refine .cons (ih expression List.mem_cons_self reader ready inputs firstNames secondNames
                    (.interned reader.nodes.next) (.interned reader.nodes.next) first second before later after final
                    raw other raw other _ _ (firstDepth raw List.mem_cons_self) (secondDepth other List.mem_cons_self)
                    firstContext secondContext (aliases expression List.mem_cons_self) tests
                    paired firstReplacements secondReplacements firstRawAvailable secondRawAvailable firstBuild secondBuild
                    firstGrowth secondGrowth
                    (filter_absent (.interned reader.nodes.next) raw reader ready firstRawAvailable (fresh_free reader ready raw firstRawAvailable))
                    (filter_absent (.interned reader.nodes.next) other reader ready secondRawAvailable (fresh_free reader ready other secondRawAvailable))
                    firstDone secondDone) ?_
                  exact induct (fun child member => ih child (List.mem_cons_of_mem _ member))
                    (fun child member => aliases child (List.mem_cons_of_mem _ member)) _ _ _ secondRemaining
                    (fun value member => firstAvailable value (List.mem_cons_of_mem _ member))
                    (fun value member => secondAvailable value (List.mem_cons_of_mem _ member)) firstRest secondRest
                    (fun value member => firstDepth value (List.mem_cons_of_mem _ member))
                    (fun value member => secondDepth value (List.mem_cons_of_mem _ member))

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

private theorem physical_depth (reader : State Symbol Guard) (ready : Ready reader)
    (value : Value Symbol Guard) (available : Available reader value)
    (row : EdgeValue Symbol Guard) (selected : row ∈ nodeEdges value) :
    ∀ child ∈ row.children, child.depth ≤ value.depth := by
  cases value with
  | empty | reference | union | mu => cases selected
  | node entry rows level free =>
      intro child member
      exact InternedUnionSeparation.child_depth reader ready.semantic.1.normal.facts.coherent
        (.node entry rows level free) child available (List.mem_flatMap.mpr ⟨row, selected, member⟩)

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

/-- Actual parent calls derive both indexed raw rows and both stored child schedules. -/
private theorem schedules [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (first second : Environment Symbol Guard) (reader before after later final : State Symbol Guard)
    (ready : Ready reader)
    (firstContext : Context before (inputs.map (input firstNames)))
    (secondContext : Context later (inputs.map (input secondNames)))
    (firstReplacements : Replacements reader first) (secondReplacements : Replacements reader second)
    (rawFirst rawSecond left right : Value Symbol Guard)
    (firstBuild : build (.node expressions) (inputs.map (input firstNames)) before = .done rawFirst after)
    (secondBuild : build (.node expressions) (inputs.map (input secondNames)) later = .done rawSecond final)
    (firstGrowth : Grows after reader) (secondGrowth : Grows final reader)
    (firstAvailable : Available reader rawFirst) (secondAvailable : Available reader rawSecond)
    (firstDone : execute rawFirst first reader = .done left reader)
    (secondDone : execute rawSecond second reader = .done right reader)
    (row : EdgeValue Symbol Guard) (selected : row ∈ nodeEdges rawFirst) :
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
      ∃ firstOutput secondOutput,
        RowCalls first reader row firstOutput ∧ RowCalls second reader secondRow.output secondOutput := by
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
    obtain ⟨firstOutput,firstCalls⟩ := SourceCurrentStoredLiteralExecutionParts.row rawFirst left first reader ready
      firstAvailable firstReplacements firstDone row ((literal_row rawFirst row (raw_ordinary expressions _ before after firstContext rawFirst firstBuild)).mpr selected)
    obtain ⟨secondOutput,secondCalls⟩ := SourceCurrentStoredLiteralExecutionParts.row rawSecond right second reader ready
      secondAvailable secondReplacements secondDone secondRow.output ((literal_row rawSecond secondRow.output (raw_ordinary expressions _ later final secondContext rawSecond secondBuild)).mpr secondMember)
    exact ⟨firstRows,firstAfter,secondRows,secondAfter,index,symbol,guard,children,firstRow,secondRow,
      firstRowsDone,firstMade,secondRowsDone,secondMade,same,secondMember,
      InternedFreshOrdinaryReplay.buildMany_replays children _ firstRow.current reader firstRow.values firstRow.middle
        firstRow.context.normal.facts.coherent.valid firstRow.called firstRow.middle_growth,
      InternedFreshOrdinaryReplay.buildMany_replays children _ secondRow.current reader secondRow.values secondRow.middle
        secondRow.context.normal.facts.coherent.valid secondRow.called secondRow.middle_growth,
      firstOutput,secondOutput,firstCalls,secondCalls⟩

/-- A surviving reconstructed row has an actual opposite survivor with equal ordered Empty tests. -/
theorem row [DecidableEq (EdgeKey Symbol Guard)] (bound : Nat) (expressions : List (EdgeSyntax Symbol Guard))
    (ih : ∀ symbol guard children, EdgeSyntax.mk symbol guard children ∈ expressions → ∀ child ∈ children, Fusion bound child)
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (first second : Environment Symbol Guard) (reader before after later final : State Symbol Guard)
    (ready : Ready reader)
    (firstContext : Context before (inputs.map (input firstNames)))
    (secondContext : Context later (inputs.map (input secondNames)))
    (aliases : Aliases (.node expressions) inputs firstNames secondNames)
    (paired : Paired (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty)) first second (inputs.map (input firstNames)) (inputs.map (input secondNames)))
    (firstReplacements : Replacements reader first) (secondReplacements : Replacements reader second)
    (rawFirst rawSecond left right : Value Symbol Guard)
    (firstDepth : rawFirst.depth ≤ bound) (secondDepth : rawSecond.depth ≤ bound)
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
      firstCalls,secondCalls⟩ := schedules expressions inputs firstNames secondNames
    first second reader before after later final ready firstContext secondContext firstReplacements
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
  have firstDepths : ∀ value ∈ firstRow.values, value.depth ≤ bound := by
    intro value member
    apply Nat.le_trans (physical_depth reader ready rawFirst firstAvailable raw rawMember value ?_) firstDepth
    simpa only [←same,firstRow.children_eq] using member
  have secondDepths : ∀ value ∈ secondRow.values, value.depth ≤ bound := by
    intro value member
    apply Nat.le_trans (physical_depth reader ready rawSecond secondAvailable secondRow.output secondMember value ?_) secondDepth
    simpa only [secondRow.children_eq] using member
  have pairedOutputs := children_fusion bound children (ih symbol guard children sourceMember) inputs firstNames secondNames
    first second reader ready childAliases paired firstReplacements secondReplacements
    firstRow.values secondRow.values firstOutput.children secondOutput.children firstSources secondSources firstValues secondValues
    (by simpa only [←same,firstRow.children_eq] using firstWarm)
    (by simpa only [secondRow.children_eq] using secondWarm) firstDepths secondDepths
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
private theorem raw_node [DecidableEq (EdgeKey Symbol Guard)] (bound : Nat) (expressions : List (EdgeSyntax Symbol Guard))
    (ih : ∀ symbol guard children, EdgeSyntax.mk symbol guard children ∈ expressions → ∀ child ∈ children, Fusion bound child) :
    ∀ {Atom : Type} (inputs : List (Sum (Value Symbol Guard) Atom))
      (firstNames secondNames : Atom → Reference) (first second : Environment Symbol Guard)
      (reader before after later final : State Symbol Guard) (_ready : Ready reader)
      (_firstContext : Context before (inputs.map (input firstNames)))
      (_secondContext : Context later (inputs.map (input secondNames)))
      (_aliases : Aliases (.node expressions) inputs firstNames secondNames)
      (_paired : Paired (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty)) first second
        (inputs.map (input firstNames)) (inputs.map (input secondNames)))
      (_firstReplacements : Replacements reader first) (_secondReplacements : Replacements reader second)
      (rawFirst rawSecond left right : Value Symbol Guard)
      (_firstDepth : rawFirst.depth ≤ bound) (_secondDepth : rawSecond.depth ≤ bound)
      (_firstBuild : build (.node expressions) (inputs.map (input firstNames)) before = .done rawFirst after)
      (_secondBuild : build (.node expressions) (inputs.map (input secondNames)) later = .done rawSecond final)
      (_firstGrowth : Grows after reader) (_secondGrowth : Grows final reader)
      (_firstAvailable : Available reader rawFirst) (_secondAvailable : Available reader rawSecond)
      (_firstDone : execute rawFirst first reader = .done left reader)
      (_secondDone : execute rawSecond second reader = .done right reader),
      (left.referenceOf == .empty) = (right.referenceOf == .empty) := by
  intro Atom inputs firstNames secondNames first second reader before after later final ready firstContext secondContext
    aliases paired firstReplacements secondReplacements rawFirst rawSecond left right firstDepth secondDepth firstBuild secondBuild firstGrowth secondGrowth
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
      obtain ⟨original,member,_,_,_⟩  := row bound expressions ih inputs secondNames firstNames second first
        reader later final before after ready secondContext firstContext (fun a ha b hb => (aliases a ha b hb).symm)
        (reverse_inputs paired) secondReplacements firstReplacements rawSecond rawFirst right left secondDepth firstDepth
        secondBuild firstBuild secondGrowth firstGrowth secondAvailable firstAvailable secondDone firstDone other present
      exact absent original member
    · intro absent original present
      obtain ⟨other,member,_,_,_⟩  := row bound expressions ih inputs firstNames secondNames first second
        reader before after later final ready firstContext secondContext aliases paired firstReplacements secondReplacements
        rawFirst rawSecond left right firstDepth secondDepth firstBuild secondBuild firstGrowth secondGrowth firstAvailable secondAvailable
        firstDone secondDone original present
      exact absent other member
  exact Bool.eq_iff_iff.mpr (by simpa only [beq_iff_eq] using equivalent)

/-- Strict child fusion derives the complete filtered source-node law from actual calls. -/
theorem node [DecidableEq (EdgeKey Symbol Guard)] (bound : Nat) (expressions : List (EdgeSyntax Symbol Guard))
    (ih : ∀ symbol guard children, EdgeSyntax.mk symbol guard children ∈ expressions → ∀ child ∈ children, Fusion bound child) :
    Fusion bound (.node expressions) := by
  intro Atom reader ready inputs firstNames secondNames firstOwn secondOwn first second before later after final
    rawFirst rawSecond filteredFirst filteredSecond left right firstDepth secondDepth firstContext secondContext aliases _tests paired
    firstReplacements secondReplacements firstAvailable secondAvailable firstBuild secondBuild firstGrowth secondGrowth
    firstFilter secondFilter firstDone secondDone
  have firstOrdinary := raw_ordinary expressions _ before after firstContext rawFirst firstBuild
  have secondOrdinary := raw_ordinary expressions _ later final secondContext rawSecond secondBuild
  have filter_identity (own : Reference) (raw filtered : Value Symbol Guard) (plain : Ordinary raw)
      (actual : run (withoutSelfReference own raw) reader = (filtered,reader)) : raw = filtered := by
    cases raw with
    | empty | node => exact congrArg Prod.fst actual
    | reference | union | mu => cases plain
  obtain rfl := filter_identity firstOwn rawFirst filteredFirst firstOrdinary firstFilter
  obtain rfl := filter_identity secondOwn rawSecond filteredSecond secondOrdinary secondFilter
  exact raw_node bound expressions ih inputs firstNames secondNames first second reader before after later final ready
    firstContext secondContext aliases paired firstReplacements secondReplacements rawFirst rawSecond left right firstDepth secondDepth
    firstBuild secondBuild firstGrowth secondGrowth firstAvailable secondAvailable firstDone secondDone

end MicroCFTA.SourceCurrentBoundedFilteredNodeFusion
