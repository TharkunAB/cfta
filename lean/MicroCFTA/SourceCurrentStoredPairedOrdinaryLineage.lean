import MicroCFTA.SourceCurrentStoredMuBinderChildLineage
import MicroCFTA.SourceCurrentStoredReconstruction
import MicroCFTA.SourceCurrentStoredCallsReplay
import MicroCFTA.SourceCurrentOrdinaryObservationEmpty
import MicroCFTA.SourceCurrentOpenObservationSurvival
import MicroCFTA.InternedFreshOrdinaryDependencies

/-!
# Ordinary source reconstruction with paired lexical inputs

Paired inputs can contain different bare references at any lexical index.
The resolved references agree. Opaque captures retain the same value and
compatible replacement maps. Strict source-child induction retains full
row fields and ordered children through both normalization stages.
The binder-result and chronological writer cases remain separate.
-/
namespace MicroCFTA.SourceCurrentStoredPairedOrdinaryLineage
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work)
open InternedNestedProvenance (Values Edges)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryContext
open InternedStoredSubstitution (Environment Replacements leaves input encode)
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceEqualityRequiredCache (Ready Keeps Ordinary)
open SourceCurrentOpenObservationSurvival (Related)
open SourceCurrentOpenObservations (Same RowMatch ReferenceOrigin)
open SourceCurrentStoredNodeExpansion (RowCalls Expansion)
open SourceCurrentStoredSubstitutionCalls (Calls)
open SourceCurrentRowPlanReplay (rowRun)
open MergedFreshOrdinaryGraph (Origin)
open InternedBinderProtocol (Reference)
open Language

open SourceCurrentStoredMuBinderChildLineage (Paired)

/-- Every paired input list has one fixed-capture and varying-reference presentation. -/
theorem symbolic_inputs (first second : Environment Symbol Guard)
    (leftInputs rightInputs : List (Value Symbol Guard)) (paired : Paired first second leftInputs rightInputs) :
    ∃ inputs : List (Sum (Value Symbol Guard) (Reference × Reference)),
      inputs.map (InternedFreshOrdinaryLiveInputs.input Prod.fst) = leftInputs ∧
      inputs.map (InternedFreshOrdinaryLiveInputs.input Prod.snd) = rightInputs := by
  induction paired with
  | nil => exact ⟨[],rfl,rfl⟩
  | @cons left right lefts rights slot tail ih =>
      obtain ⟨inputs,firstInputs,secondInputs⟩ := ih
      cases left <;> cases right
      all_goals try {cases slot}
      case reference.reference a b =>
        exact ⟨.inr (a,b) :: inputs,by simpa [InternedFreshOrdinaryLiveInputs.input] using firstInputs,
          by simpa [InternedFreshOrdinaryLiveInputs.input] using secondInputs⟩
      all_goals obtain ⟨same,agree⟩ := slot
      all_goals cases same
      all_goals exact ⟨.inl _ :: inputs,
        by simpa only [List.map_cons,InternedFreshOrdinaryLiveInputs.input] using congrArg (List.cons _) firstInputs,
        by simpa only [List.map_cons,InternedFreshOrdinaryLiveInputs.input] using congrArg (List.cons _) secondInputs⟩

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Actual raw calls and warm reconstructions agree under finite paired lexical inputs. -/
def Aligned (expression : Syntax Symbol Guard) : Prop :=
  ∀ (leftInputs rightInputs : List (Value Symbol Guard))
    (first second : Environment Symbol Guard), Paired first second leftInputs rightInputs →
  ∀ (common : State Symbol Guard), Ready common →
    Values common leftInputs → Values common rightInputs →
    Replacements common first → Replacements common second →
  ∀ rawFirst rawSecond,
    build expression leftInputs common = .done rawFirst common →
    build expression rightInputs common = .done rawSecond common →
  ∀ result other,
    execute rawFirst first common = .done result common →
    execute rawSecond second common = .done other common → Related result other

/-- An induction index retains its actual source row, child occurrence, and strict syntax-size witness. -/
def StrictChild (expressions : List (EdgeSyntax Symbol Guard)) (child : Syntax Symbol Guard) : Prop :=
  ∃ symbol guard originals, EdgeSyntax.mk symbol guard originals ∈ expressions ∧ child ∈ originals ∧
    sizeOf child < sizeOf (.node expressions : Syntax Symbol Guard)

private theorem related_refl (value : Value Symbol Guard) : Related value value :=
  ⟨Iff.rfl, fun depth view => Same.refl depth view [value]⟩

/-- Paired lexical variables give equal reconstructed values without an output-relation premise. -/
theorem reference (index : Nat) : Aligned (Symbol := Symbol) (Guard := Guard) (.var index) := by
  intro leftInputs rightInputs first second paired common ready firstAvailable secondAvailable
    firstReplacements secondReplacements rawFirst rawSecond firstRaw secondRaw result other firstDone secondDone
  have same := SourceCurrentStoredMuBinderChildLineage.reference first second leftInputs rightInputs paired
    common ready.semantic.1.normal.facts.coherent firstAvailable index
  simp only [firstRaw,secondRaw,Outcome.bind,firstDone,secondDone] at same
  have values := (Outcome.done.inj same).1
  rw [values]
  exact related_refl _

private theorem pair_left {α β : Type} {relation : α → β → Prop} {first : List α} {second : List β}
    (paired : All₂ relation first second) (value : α) (member : value ∈ first) :
    ∃ output ∈ second, relation value output := by
  induction paired with
  | nil => cases member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨_,List.mem_cons_self,head⟩
      · obtain ⟨output,included,matched⟩ := ih later
        exact ⟨output,List.mem_cons_of_mem _ included,matched⟩

private theorem pair_right {α β : Type} {relation : α → β → Prop} {first : List α} {second : List β}
    (paired : All₂ relation first second) (value : β) (member : value ∈ second) :
    ∃ original ∈ first, relation original value := by
  induction paired with
  | nil => cases member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨_,List.mem_cons_self,head⟩
      · obtain ⟨original,included,matched⟩ := ih later
        exact ⟨original,List.mem_cons_of_mem _ included,matched⟩

private theorem pair_reverse {α β : Type} {relation : α → β → Prop} {first : List α} {second : List β}
    (paired : All₂ relation first second) : All₂ (fun b a => relation a b) second first := by
  induction paired with
  | nil => exact .nil
  | cons head tail ih => exact .cons head ih

private theorem source_children (expressions : List (Syntax Symbol Guard))
    (inputs : List (Value Symbol Guard)) (common : State Symbol Guard) (valid : Valid common)
    (outputs : List (Value Symbol Guard))
    (actual : buildMany expressions inputs common = .done outputs common) :
    All₂ (fun expression output => build expression inputs common = .done output common) expressions outputs := by
  induction expressions generalizing outputs with
  | nil =>
      simp only [buildMany,Outcome.done.injEq] at actual
      obtain ⟨rfl,_⟩ := actual
      exact .nil
  | cons expression rest ih =>
      cases called : build expression inputs common with
      | pending key state => simp only [buildMany,called,Outcome.bind] at actual; cases actual
      | done output middle =>
          cases tail : buildMany rest inputs middle with
          | pending key state => simp only [buildMany,called,tail,Outcome.bind] at actual; cases actual
          | done remaining final =>
              simp only [buildMany,called,tail,Outcome.bind,Outcome.done.injEq] at actual
              obtain ⟨rfl,sameHeap⟩ := actual
              rw [sameHeap] at tail
              have middleValid : Valid middle := by
                simpa only [called,Outcome.state] using
                  (InternedFreshOrdinaryGrowth.build_correct expression inputs common valid).1
              have growth : Grows middle common := by
                simpa only [tail,Outcome.state] using
                  (InternedFreshOrdinaryGrowth.buildMany_correct rest inputs middle middleValid).2
              have head := InternedFreshOrdinaryReplay.build_replay expression inputs common common output middle valid called growth
              have rest := InternedFreshOrdinaryReplay.buildMany_replays rest inputs middle common remaining common
                middleValid tail (grows_refl _)
              exact .cons head (ih remaining rest)

private theorem raw_row (symbol : Symbol) (guard : Guard) (expressions : List (Syntax Symbol Guard))
    (inputs : List (Value Symbol Guard)) (common : State Symbol Guard) (context : Context common inputs)
    (output : EdgeValue Symbol Guard)
    (actual : rowRun (.mk symbol guard expressions) inputs common = .done output common) :
    buildMany expressions inputs common = .done output.children common ∧
      output.entry.key.symbol = symbol ∧ output.entry.key.constraint = guard := by
  cases called : buildMany expressions inputs common with
  | pending key state => simp only [rowRun,called,Outcome.bind] at actual; cases actual
  | done values middle =>
      have made : run (makeEdge symbol guard values) middle = (output,common) :=
        Prod.ext (Outcome.done.inj (by simpa only [rowRun,called,Outcome.bind,work] using actual)).1
          (Outcome.done.inj (by simpa only [rowRun,called,Outcome.bind,work] using actual)).2
      have checked := InternedFreshOrdinaryFacts.buildMany_verified expressions inputs common context.normal.facts context.inputs
      have middleFacts : InternedNestedFacts.Facts middle := by simpa only [called,Outcome.state] using checked.facts
      have available := checked.result values middle called
      have fields := MergedPhysicalGroupEdges.makeEdge_fields middle middleFacts symbol guard values available
      rw [made] at fields
      have growth : Grows middle common := by
        simpa only [made] using (run_correct (makeEdge symbol guard values) middle middleFacts.coherent.valid).2
      have repeated := InternedFreshOrdinaryReplay.buildMany_replays expressions inputs common common values middle
        context.normal.facts.coherent.valid called growth
      rw [← fields.2.2] at repeated
      exact ⟨by simpa only [called] using repeated,fields.1,fields.2.1⟩

private theorem children_aligned (expressions : List (Syntax Symbol Guard))
    (cases : ∀ expression ∈ expressions, Aligned expression)
    (leftInputs rightInputs : List (Value Symbol Guard))
    (first second : Environment Symbol Guard) (paired : Paired first second leftInputs rightInputs)
    (common : State Symbol Guard) (ready : Ready common)
    (firstInputs : Values common leftInputs)
    (secondInputs : Values common rightInputs)
    (firstReplacements : Replacements common first) (secondReplacements : Replacements common second)
    (rawFirst rawSecond left right : List (Value Symbol Guard))
    (firstRaw : buildMany expressions leftInputs common = .done rawFirst common)
    (secondRaw : buildMany expressions rightInputs common = .done rawSecond common)
    (firstDone : Calls first rawFirst common left common) (secondDone : Calls second rawSecond common right common) :
    All₂ Related left right := by
  have firstSource := source_children expressions _ common ready.semantic.1.normal.facts.coherent.valid rawFirst firstRaw
  have secondSource := source_children expressions _ common ready.semantic.1.normal.facts.coherent.valid rawSecond secondRaw
  have firstWarm := SourceCurrentStoredCallsReplay.replay firstDone common ready.semantic.1.normal.facts.coherent.valid (grows_refl _)
  have secondWarm := SourceCurrentStoredCallsReplay.replay secondDone common ready.semantic.1.normal.facts.coherent.valid (grows_refl _)
  clear firstRaw secondRaw firstDone secondDone
  induction firstSource generalizing rawSecond left right with
  | nil => cases secondSource; cases firstWarm; cases secondWarm; exact .nil
  | @cons expression raw expressions raws firstRaw remaining ih =>
      cases secondSource with
      | cons secondRaw secondRemaining =>
          cases firstWarm with
          | cons firstDone firstRest =>
              cases secondWarm with
              | cons secondDone secondRest =>
                  exact .cons (cases expression List.mem_cons_self leftInputs rightInputs first second paired
                    common ready firstInputs secondInputs firstReplacements secondReplacements _ _ firstRaw secondRaw
                    _ _ firstDone secondDone)
                    (ih (fun expression member => cases expression (List.mem_cons_of_mem _ member))
                      _ _ _ secondRemaining firstRest secondRest)

private theorem raw_parts (expressions : List (EdgeSyntax Symbol Guard)) (inputs : List (Value Symbol Guard))
    (common : State Symbol Guard) (context : Context common inputs) (result : Value Symbol Guard)
    (actual : build (.node expressions) inputs common = .done result common) :
    ∃ rows, All₂ (fun expression row => rowRun expression inputs common = .done row common) expressions rows ∧
      Edges common rows ∧ run (makeNode rows) common = (result,common) := by
  cases called : buildEdges expressions inputs common with
  | pending key state => simp only [build,called,Outcome.bind] at actual; cases actual
  | done rows middle =>
      have made : run (makeNode rows) middle = (result,common) :=
        Prod.ext (Outcome.done.inj (by simpa only [build,called,Outcome.bind,work] using actual)).1
          (Outcome.done.inj (by simpa only [build,called,Outcome.bind,work] using actual)).2
      have checked := InternedFreshOrdinaryFacts.buildEdges_verified expressions inputs common context.normal.facts context.inputs
      have middleFacts : InternedNestedFacts.Facts middle := by simpa only [called,Outcome.state] using checked.facts
      have growth : Grows middle common := by
        simpa only [made] using (run_correct (makeNode rows) middle middleFacts.coherent.valid).2
      have resident : Edges common rows := by
        intro row member
        exact growth.edgeRecords _ _ (checked.result rows middle called row member)
      have repeated := InternedConstructorTemplates.replay (makeNode rows) middle common middleFacts.coherent.valid
        (by rw [made]; exact grows_refl _)
      rw [made] at repeated
      exact ⟨rows,SourceCurrentRowPlanReplay.rows expressions inputs common rows middle common
        context.normal.facts.coherent.valid called growth,resident,repeated⟩

private theorem empty_same (expression : Syntax Symbol Guard) (leftInputs rightInputs : List (Value Symbol Guard))
    (firstMap secondMap : Environment Symbol Guard) (paired : Paired firstMap secondMap leftInputs rightInputs)
    (common : State Symbol Guard) (firstContext : Context common leftInputs)
    (secondContext : Context common rightInputs) (first second : Value Symbol Guard)
    (called : build expression leftInputs common = .done first common)
    (other : build expression rightInputs common = .done second common) :
    (first.referenceOf == .empty) = (second.referenceOf == .empty) := by
  rw [InternedRecordDepthSource.source_empty expression _ common firstContext first common called,
    InternedRecordDepthSource.source_empty expression _ common secondContext second common other]
  obtain ⟨inputs,leftInputsSame,rightInputsSame⟩ := symbolic_inputs firstMap secondMap leftInputs rightInputs paired
  rw [← leftInputsSame,← rightInputsSame,
    SourceCurrentNativeNormalizedComparison.instantiated,SourceCurrentNativeNormalizedComparison.instantiated,
    InternedDepthSemantics.isEmpty_map,InternedDepthSemantics.isEmpty_map]

private theorem raw_empty (expressions : List (Syntax Symbol Guard))
    (leftInputs rightInputs : List (Value Symbol Guard))
    (firstMap secondMap : Environment Symbol Guard) (paired : Paired firstMap secondMap leftInputs rightInputs)
    (common : State Symbol Guard)
    (firstContext : Context common leftInputs)
    (secondContext : Context common rightInputs)
    (first second : List (Value Symbol Guard))
    (called : buildMany expressions leftInputs common = .done first common)
    (other : buildMany expressions rightInputs common = .done second common) :
    first.any (fun value => value.referenceOf == .empty) = second.any (fun value => value.referenceOf == .empty) := by
  have left := source_children expressions _ common firstContext.normal.facts.coherent.valid first called
  have right := source_children expressions _ common secondContext.normal.facts.coherent.valid second other
  clear called other
  induction left generalizing second with
  | nil => cases right; rfl
  | cons called tail ih =>
      cases right with
      | cons other remaining =>
          simp only [List.any_cons,
            empty_same _ leftInputs rightInputs firstMap secondMap paired common firstContext secondContext _ _ called other,
            ih _ remaining]

private theorem related_empty {first second : List (Value Symbol Guard)} (paired : All₂ Related first second) :
    first.any (fun value => value.referenceOf == .empty) = second.any (fun value => value.referenceOf == .empty) := by
  induction paired with
  | nil => rfl
  | @cons first second rest remaining pair tail ih =>
      have head : (first.referenceOf == .empty) = (second.referenceOf == .empty) := by
        by_cases empty : first.referenceOf = .empty
        · simp only [empty,pair.1.mp empty,beq_self_eq_true]
        · have other : second.referenceOf ≠ .empty := fun found => empty (pair.1.mpr found)
          simp only [beq_eq_false_iff_ne.mpr empty,beq_eq_false_iff_ne.mpr other]
      simp only [List.any_cons,head,ih]

private theorem normalized_rows (common : State Symbol Guard) (facts : InternedNestedFacts.Facts common)
    (rows : List (EdgeValue Symbol Guard)) (resident : Edges common rows) (value : Value Symbol Guard)
    (made : run (makeNode rows) common = (value,common)) (row : EdgeValue Symbol Guard) :
    row ∈ nodeEdges value ↔ row ∈ surviving rows := by
  have exactRows := EqualityLeafProjectionPhysical.makeNode_edges rows common facts.coherent facts.linked resident
  rw [made] at exactRows
  rw [exactRows]
  exact ⟨canonicalEdges_member _ row,InternedEdgeResidency.canonicalEdges_retains common facts.coherent _ row
    (fun edge member => resident edge (List.mem_filter.mp member).1)⟩

private theorem ordinary_expansion (value output : Value Symbol Guard) (environment : Environment Symbol Guard)
    (common : State Symbol Guard) (ready : Ready common) (available : Available common value)
    (replacements : Replacements common environment) (ordinary : Ordinary value)
    (actual : execute value environment common = .done output common) :
    Expansion environment (nodeEdges value) common output := by
  cases value with
  | empty =>
      have done := SourceCurrentStoredUnionObservations.closed (.empty : Value Symbol Guard) environment common rfl
      have same := (Outcome.done.inj (done.symm.trans actual)).1
      subst output
      exact ⟨[],.nil,trivial,fun view row =>
        iff_of_false (MergedFreshOrdinaryGraph.origin_empty view row) List.not_mem_nil⟩
  | node entry rows level free =>
      exact SourceCurrentStoredNodeExpansion.node_warm entry rows level free environment common
        ready.semantic.1.normal available replacements output actual
  | reference | union | mu => cases ordinary

private theorem no_reference (view : State Symbol Guard) (value : Value Symbol Guard)
    (ordinary : Ordinary value) (name : Reference) : ¬ ReferenceOrigin view [value] name := by
  have different : ∀ name, value ≠ .reference name := by
    cases value <;> simp_all [SourceEqualityRequiredCache.Ordinary]
  have terminal : MergedFreshOrdinaryGraph.successors view value = [] := by
    cases value <;> simp_all [SourceEqualityRequiredCache.Ordinary,MergedFreshOrdinaryGraph.successors]
  rw [SourceCurrentOpenObservations.reference_expand view value different,terminal,
    SourceCurrentOpenObservations.reference_seeds]
  rintro ⟨_,impossible,_⟩
  cases impossible

private theorem expansions_related (common : State Symbol Guard) (ready : Ready common)
    (first second : Environment Symbol Guard) (firstRows secondRows : List (EdgeValue Symbol Guard))
    (left right : Value Symbol Guard) (leftAvailable : Available common left) (rightAvailable : Available common right)
    (firstExpansion : Expansion first firstRows common left) (secondExpansion : Expansion second secondRows common right)
    (forward : ∀ row ∈ firstRows, ∃ other ∈ secondRows,
      ∀ a b, RowCalls first common row a → RowCalls second common other b → RowMatch Related a b)
    (backward : ∀ row ∈ secondRows, ∃ other ∈ firstRows,
      ∀ a b, RowCalls first common other a → RowCalls second common row b → RowMatch Related a b) :
    Related left right := by
  obtain ⟨firstOutputs,firstPaired,firstOrdinary,firstOrigins⟩ := firstExpansion
  obtain ⟨secondOutputs,secondPaired,secondOrdinary,secondOrigins⟩ := secondExpansion
  have observations (depth : Nat) (view : State Symbol Guard) : Same depth view [left] [right] := by
    have references : ∀ name, ReferenceOrigin view [left] name ↔ ReferenceOrigin view [right] name :=
      fun name => iff_of_false (no_reference view left firstOrdinary name) (no_reference view right secondOrdinary name)
    cases depth with
    | zero => exact references
    | succ depth =>
        refine ⟨references,?_,?_⟩
        · intro row origin
          have retained := (firstOrigins view row).mp origin
          obtain ⟨original,included,called⟩ := pair_right firstPaired row (List.mem_filter.mp retained).1
          obtain ⟨other,present,align⟩ := forward original included
          obtain ⟨rebuilt,member,otherCall⟩ := pair_left secondPaired other present
          have matched := align row rebuilt called otherCall
          refine ⟨rebuilt,(secondOrigins view rebuilt).mpr (List.mem_filter.mpr ⟨member,?_⟩),
            matched.1,matched.2.1,All₂.imp (fun _ _ related => related.2 depth view) matched.2.2⟩
          change (!(rebuilt.children.any (fun child => child.referenceOf == .empty))) = true
          rw [← related_empty matched.2.2]
          exact (List.mem_filter.mp retained).2
        · intro row origin
          have retained := (secondOrigins view row).mp origin
          obtain ⟨original,included,called⟩ := pair_right secondPaired row (List.mem_filter.mp retained).1
          obtain ⟨other,present,align⟩ := backward original included
          obtain ⟨rebuilt,member,otherCall⟩ := pair_left firstPaired other present
          have matched := align rebuilt row otherCall called
          have reversed : All₂ (fun a b => Same depth view [a] [b]) row.children rebuilt.children :=
            All₂.imp (fun _ _ pair => (pair.2 depth view).symm) (pair_reverse matched.2.2)
          refine ⟨rebuilt,(firstOrigins view rebuilt).mpr (List.mem_filter.mpr ⟨member,?_⟩),
            matched.1.symm,matched.2.1.symm,reversed⟩
          change (!(rebuilt.children.any (fun child => child.referenceOf == .empty))) = true
          rw [related_empty matched.2.2]
          exact (List.mem_filter.mp retained).2
  refine ⟨?_,observations⟩
  have empty := SourceCurrentOrdinaryObservationEmpty.ordinary_empty_iff common common ready.semantic.1.normal
    left [right] firstOrdinary (by intro value member; simpa only [List.mem_singleton.mp member] using secondOrdinary)
    leftAvailable (by intro value member; simpa only [List.mem_singleton.mp member] using rightAvailable)
    (observations 1 common)
  simpa only [List.mem_singleton,forall_eq] using empty

/-- Strict child induction suffices for the full ordinary-node source case, including closed shortcuts. -/
theorem ordinary (expressions : List (EdgeSyntax Symbol Guard))
    (children : ∀ child, StrictChild expressions child → Aligned child) :
    Aligned (.node expressions) := by
  intro leftInputs rightInputs first second paired common ready firstInputs secondInputs
    firstReplacements secondReplacements rawFirst rawSecond firstRaw secondRaw result other firstDone secondDone
  have firstContext : Context common leftInputs :=
    ⟨ready.semantic.1.normal,firstInputs,ready.semantic.1.profiles,ready.semantic.1.freeNames⟩
  have secondContext : Context common rightInputs :=
    ⟨ready.semantic.1.normal,secondInputs,ready.semantic.1.profiles,ready.semantic.1.freeNames⟩
  obtain ⟨firstRows,firstSource,firstResident,firstMade⟩ := raw_parts expressions _ common firstContext rawFirst firstRaw
  obtain ⟨secondRows,secondSource,secondResident,secondMade⟩ := raw_parts expressions _ common secondContext rawSecond secondRaw
  have firstAvailable := (InternedFreshOrdinaryFacts.build_verified (.node expressions) _ common
    firstContext.normal.facts firstInputs).result rawFirst common firstRaw
  have secondAvailable := (InternedFreshOrdinaryFacts.build_verified (.node expressions) _ common
    secondContext.normal.facts secondInputs).result rawSecond common secondRaw
  have firstOrdinary : Ordinary rawFirst := by
    simpa only [firstMade] using SourceEqualityRequiredCache.node_ordinary firstRows common firstContext.normal.facts firstResident
  have secondOrdinary : Ordinary rawSecond := by
    simpa only [secondMade] using SourceEqualityRequiredCache.node_ordinary secondRows common secondContext.normal.facts secondResident
  have firstOutput := (InternedFreshOrdinaryFacts.build_verified (encode (leaves rawFirst) [] rawFirst) _ common
    ready.semantic.1.normal.facts (InternedStoredSubstitution.inputs_available rawFirst first common firstAvailable firstReplacements)).result
    result common firstDone
  have secondOutput := (InternedFreshOrdinaryFacts.build_verified (encode (leaves rawSecond) [] rawSecond) _ common
    ready.semantic.1.normal.facts (InternedStoredSubstitution.inputs_available rawSecond second common secondAvailable secondReplacements)).result
    other common secondDone
  have align (expression : EdgeSyntax Symbol Guard) (member : expression ∈ expressions)
      (left right : EdgeValue Symbol Guard)
      (leftRaw : rowRun expression leftInputs common = .done left common)
      (rightRaw : rowRun expression rightInputs common = .done right common) :
      left.children.any (fun value => value.referenceOf == .empty) =
        right.children.any (fun value => value.referenceOf == .empty) ∧
      ∀ a b, RowCalls first common left a → RowCalls second common right b → RowMatch Related a b := by
    cases expression with
    | mk symbol guard originals =>
        obtain ⟨leftChildren,leftSymbol,leftGuard⟩ := raw_row symbol guard originals _ common firstContext left leftRaw
        obtain ⟨rightChildren,rightSymbol,rightGuard⟩ := raw_row symbol guard originals _ common secondContext right rightRaw
        refine ⟨raw_empty originals leftInputs rightInputs first second paired common firstContext secondContext _ _ leftChildren rightChildren,?_⟩
        intro a b firstCall secondCall
        refine ⟨firstCall.2.2.1.trans (leftSymbol.trans (rightSymbol.symm.trans secondCall.2.2.1.symm)),
          firstCall.2.2.2.1.trans (leftGuard.trans (rightGuard.symm.trans secondCall.2.2.2.1.symm)),?_⟩
        apply children_aligned originals (fun child present => children child ⟨symbol,guard,originals,member,present,?_⟩)
          leftInputs rightInputs first second
          paired common ready firstInputs secondInputs firstReplacements secondReplacements _ _ _ _
          leftChildren rightChildren firstCall.1 secondCall.1
        have firstLt := List.sizeOf_lt_of_mem present
        have rowLt := List.sizeOf_lt_of_mem member
        simp only [Syntax.node.sizeOf_spec,EdgeSyntax.mk.sizeOf_spec] at *
        omega
  apply expansions_related common ready first second _ _ result other firstOutput secondOutput
    (ordinary_expansion rawFirst result first common ready firstAvailable firstReplacements firstOrdinary firstDone)
    (ordinary_expansion rawSecond other second common ready secondAvailable secondReplacements secondOrdinary secondDone)
  · intro row member
    have retained := (normalized_rows common ready.semantic.1.normal.facts firstRows firstResident rawFirst firstMade row).mp member
    obtain ⟨source,included,called⟩ := pair_right firstSource row (List.mem_filter.mp retained).1
    obtain ⟨next,present,otherCall⟩ := pair_left secondSource source included
    have aligned := align source included row next called otherCall
    refine ⟨next,(normalized_rows common ready.semantic.1.normal.facts secondRows secondResident rawSecond secondMade next).mpr
      (List.mem_filter.mpr ⟨present,?_⟩),aligned.2⟩
    change (!(next.children.any (fun value => value.referenceOf == .empty))) = true
    rw [← aligned.1]
    exact (List.mem_filter.mp retained).2
  · intro row member
    have retained := (normalized_rows common ready.semantic.1.normal.facts secondRows secondResident rawSecond secondMade row).mp member
    obtain ⟨source,included,called⟩ := pair_right secondSource row (List.mem_filter.mp retained).1
    obtain ⟨next,present,otherCall⟩ := pair_left firstSource source included
    have aligned := align source included next row otherCall called
    refine ⟨next,(normalized_rows common ready.semantic.1.normal.facts firstRows firstResident rawFirst firstMade next).mpr
      (List.mem_filter.mpr ⟨present,?_⟩),aligned.2⟩
    change (!(next.children.any (fun value => value.referenceOf == .empty))) = true
    rw [aligned.1]
    exact (List.mem_filter.mp retained).2

/-- Initial ready data constructs both ordinary reconstructions from actual past raw calls and strict child induction. -/
theorem node_complete (expressions : List (EdgeSyntax Symbol Guard))
    (children : ∀ child, StrictChild expressions child → Aligned child)
    (leftInputs rightInputs : List (Value Symbol Guard))
    (first second : Environment Symbol Guard) (paired : Paired first second leftInputs rightInputs)
    (before after later final common : State Symbol Guard)
    (firstContext : Context before leftInputs)
    (secondContext : Context later rightInputs)
    (rawFirst rawSecond : Value Symbol Guard)
    (firstRaw : build (.node expressions) leftInputs before = .done rawFirst after)
    (secondRaw : build (.node expressions) rightInputs later = .done rawSecond final)
    (firstGrowth : Grows after common) (secondGrowth : Grows final common)
    (ready : Ready common)
    (firstInputs : Values common leftInputs)
    (secondInputs : Values common rightInputs)
    (firstReplacements : Replacements common first) (secondReplacements : Replacements common second) :
    ∃ left middle right reader,
      execute rawFirst first common = .done left middle ∧ execute rawSecond second middle = .done right reader ∧
      execute rawFirst first reader = .done left reader ∧ execute rawSecond second reader = .done right reader ∧
      Keeps common middle ∧ Keeps middle reader ∧ Available reader left ∧ Available reader right ∧
      Nonempty (SourceCurrentNativeMuPublication.History common middle) ∧
      Nonempty (SourceCurrentNativeMuPublication.History middle reader) ∧ Related left right := by
  have firstWarm := InternedFreshOrdinaryReplay.build_replay (.node expressions) _ before common rawFirst after
    firstContext.normal.facts.coherent.valid firstRaw firstGrowth
  have secondWarm := InternedFreshOrdinaryReplay.build_replay (.node expressions) _ later common rawSecond final
    secondContext.normal.facts.coherent.valid secondRaw secondGrowth
  have firstAvailable := (InternedFreshOrdinaryFacts.build_verified (.node expressions) _ common
    ready.semantic.1.normal.facts firstInputs).result rawFirst common firstWarm
  have secondAvailable := (InternedFreshOrdinaryFacts.build_verified (.node expressions) _ common
    ready.semantic.1.normal.facts secondInputs).result rawSecond common secondWarm
  obtain ⟨left,middle,firstDone,firstKept,leftAvailable,firstHistory⟩ :=
    SourceCurrentStoredReconstruction.execute rawFirst first common ready firstAvailable firstReplacements
  obtain ⟨right,reader,secondDone,secondKept,rightAvailable,secondHistory⟩ :=
    SourceCurrentStoredReconstruction.execute rawSecond second middle firstKept.ready
      (firstKept.available rawSecond secondAvailable)
      (fun name value found => firstKept.available value (secondReplacements name value found))
  have firstReplay := InternedFreshOrdinaryReplay.build_replay (encode (leaves rawFirst) [] rawFirst)
    ((leaves rawFirst).map (input first)) common reader left middle ready.semantic.1.normal.facts.coherent.valid
    firstDone secondKept.growth
  have secondReplay := InternedFreshOrdinaryReplay.build_replay (encode (leaves rawSecond) [] rawSecond)
    ((leaves rawSecond).map (input second)) middle reader right reader firstKept.ready.semantic.1.normal.facts.coherent.valid
    secondDone (grows_refl _)
  have growth := grows_trans firstKept.growth secondKept.growth
  have firstSource := InternedFreshOrdinaryReplay.build_replay (.node expressions) _ before reader rawFirst after
    firstContext.normal.facts.coherent.valid firstRaw (grows_trans firstGrowth growth)
  have secondSource := InternedFreshOrdinaryReplay.build_replay (.node expressions) _ later reader rawSecond final
    secondContext.normal.facts.coherent.valid secondRaw (grows_trans secondGrowth growth)
  have aligned := ordinary expressions children leftInputs rightInputs first second paired reader secondKept.ready
    (fun value member => secondKept.available value (firstKept.available value (firstInputs value member)))
    (fun value member => secondKept.available value (firstKept.available value (secondInputs value member)))
    (fun name value found => secondKept.available value (firstKept.available value (firstReplacements name value found)))
    (fun name value found => secondKept.available value (firstKept.available value (secondReplacements name value found)))
    rawFirst rawSecond firstSource secondSource left right firstReplay secondReplay
  exact ⟨left,middle,right,reader,firstDone,secondDone,firstReplay,secondReplay,firstKept,secondKept,
    secondKept.available left leftAvailable,rightAvailable,firstHistory,secondHistory,aligned⟩

end MicroCFTA.SourceCurrentStoredPairedOrdinaryLineage
