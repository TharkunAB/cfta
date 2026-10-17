import MicroCFTA.SourceCurrentStoredProbeCompatibility
import MicroCFTA.SourceCurrentStoredPairedOrdinaryLineage
import MicroCFTA.SourceCurrentStoredReconstruction
import MicroCFTA.SourceCurrentStoredCallsReplay
import MicroCFTA.SourceCurrentOrdinaryObservationEmpty
import MicroCFTA.SourceCurrentOpenObservationSurvival
import MicroCFTA.InternedFreshOrdinaryDependencies

/-!
# Reconstruction from live source compatibility

Only surviving source rows constrain the lexical replacement maps.
Actual source profiles derive row liveness before strict child induction.
Dead rows do not require compatible captures. Both stored calls are built
from initial Ready data. Binder and selected-writer induction remain open.
-/
namespace MicroCFTA.SourceCurrentStoredLiveSourceLineage
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

open SourceCurrentStoredProbeCompatibility (Compatible)
open SourceCurrentStoredPairedOrdinaryLineage (StrictChild)
open InternedFreshOrdinaryLiveInputs (inputProfile)

private theorem empty_same (expression : Syntax Symbol Guard)
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (common : State Symbol Guard)
    (firstContext : Context common (inputs.map (InternedFreshOrdinaryLiveInputs.input firstNames)))
    (secondContext : Context common (inputs.map (InternedFreshOrdinaryLiveInputs.input secondNames)))
    (first second : Value Symbol Guard)
    (called : build expression _ common = .done first common)
    (other : build expression _ common = .done second common) :
    (first.referenceOf == .empty) = (second.referenceOf == .empty) := by
  rw [InternedRecordDepthSource.source_empty expression _ common firstContext first common called,
    InternedRecordDepthSource.source_empty expression _ common secondContext second common other,
    SourceCurrentNativeNormalizedComparison.instantiated,SourceCurrentNativeNormalizedComparison.instantiated,
    InternedDepthSemantics.isEmpty_map,InternedDepthSemantics.isEmpty_map]

private theorem raw_empty (expressions : List (Syntax Symbol Guard))
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (common : State Symbol Guard)
    (firstContext : Context common (inputs.map (InternedFreshOrdinaryLiveInputs.input firstNames)))
    (secondContext : Context common (inputs.map (InternedFreshOrdinaryLiveInputs.input secondNames)))
    (first second : List (Value Symbol Guard))
    (called : buildMany expressions _ common = .done first common)
    (other : buildMany expressions _ common = .done second common) :
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
            empty_same _ inputs firstNames secondNames common firstContext secondContext _ _ called other,
            ih _ remaining]

private theorem source_live (expressions : List (Syntax Symbol Guard))
    (inputs : List (Sum (Value Symbol Guard) Atom)) (names : Atom → Reference)
    (common : State Symbol Guard) (context : Context common (inputs.map (InternedFreshOrdinaryLiveInputs.input names)))
    (values : List (Value Symbol Guard)) (called : buildMany expressions _ common = .done values common)
    (live : values.any (fun value => value.referenceOf == .empty) = false) :
    (InternedProfileSemantics.evaluateMany expressions (inputs.map inputProfile)).all
      (fun child => !InternedProfileSemantics.isEmpty child) = true := by
  have available := (InternedFreshOrdinaryFacts.buildMany_verified expressions _ common
    context.normal.facts context.inputs).result values common called
  have matched := (InternedFreshOrdinaryProfiles.buildMany_profile expressions _ common
    context.normal context.inputs context.profiles).result values common called
  have actualLive : values.all (fun value => !InternedProfileSemantics.isEmpty (InternedRootProfile.profile value)) = true := by
    apply List.all_eq_true.mpr
    intro value member
    rw [InternedRootProfileNode.isEmpty_profile value common context.normal.proper (available value member)]
    have absent := List.any_eq_false.mp live value member
    simpa only [Bool.not_eq_true] using Bool.eq_false_iff.mpr absent
  rw [InternedProfileComposition.children_matched matched] at actualLive
  simpa only [InternedFreshOrdinaryLiveInputs.input_profiles,InternedProfileSemantics.evaluateMany_map,
    List.all_map,Function.comp_def,InternedProfileSemantics.isEmpty_map] using actualLive

private theorem child_compatible (rows : List (EdgeSyntax Symbol Guard))
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (first second : Environment Symbol Guard) (compatible : Compatible (.node rows) inputs firstNames secondNames first second)
    (symbol : Symbol) (guard : Guard) (children : List (Syntax Symbol Guard))
    (row : EdgeSyntax.mk symbol guard children ∈ rows)
    (live : (InternedProfileSemantics.evaluateMany children (inputs.map inputProfile)).all
      (fun child => !InternedProfileSemantics.isEmpty child) = true)
    (child : Syntax Symbol Guard) (member : child ∈ children) :
    Compatible child inputs firstNames secondNames first second := by
  have included (label : Sum Reference Atom) (present : label ∈ SourceCurrentNativeNormalizationInputs.support child inputs) :
      label ∈ SourceCurrentNativeNormalizationInputs.support (.node rows) inputs :=
    InternedFreeNameSemantics.evaluateEdges_member rows (inputs.map inputProfile)
      (inputs.map SourceCurrentNativeNormalizationInputs.inputNames) label |>.mpr
        ⟨symbol,guard,children,row,live,child,member,present⟩
  exact ⟨fun name present => compatible.1 name (included _ present),
    fun atom present => compatible.2 atom (included _ present)⟩

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
  intro Atom inputs firstNames secondNames first second compatible common ready firstInputs secondInputs
    firstReplacements secondReplacements rawFirst rawSecond firstRaw secondRaw result other firstDone secondDone
  have firstContext : Context common (inputs.map (InternedFreshOrdinaryLiveInputs.input firstNames)) :=
    ⟨ready.semantic.1.normal,firstInputs,ready.semantic.1.profiles,ready.semantic.1.freeNames⟩
  have secondContext : Context common (inputs.map (InternedFreshOrdinaryLiveInputs.input secondNames)) :=
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
      (leftRaw : rowRun expression (inputs.map (InternedFreshOrdinaryLiveInputs.input firstNames)) common = .done left common)
      (rightRaw : rowRun expression (inputs.map (InternedFreshOrdinaryLiveInputs.input secondNames)) common = .done right common) :
      left.children.any (fun value => value.referenceOf == .empty) =
        right.children.any (fun value => value.referenceOf == .empty) ∧
      left.children.any (fun value => value.referenceOf == .empty) = false →
      ∀ a b, RowCalls first common left a → RowCalls second common right b → RowMatch Related a b := by
    cases expression with
    | mk symbol guard originals =>
        obtain ⟨leftChildren,leftSymbol,leftGuard⟩ := raw_row symbol guard originals _ common firstContext left leftRaw
        obtain ⟨rightChildren,rightSymbol,rightGuard⟩ := raw_row symbol guard originals _ common secondContext right rightRaw
        refine ⟨raw_empty originals inputs firstNames secondNames common firstContext secondContext _ _ leftChildren rightChildren,?_⟩
        intro live a b firstCall secondCall
        have liveSource := source_live originals inputs firstNames common firstContext left.children leftChildren live
        refine ⟨firstCall.2.2.1.trans (leftSymbol.trans (rightSymbol.symm.trans secondCall.2.2.1.symm)),
          firstCall.2.2.2.1.trans (leftGuard.trans (rightGuard.symm.trans secondCall.2.2.2.1.symm)),?_⟩
        apply children_aligned originals (fun child present => children child ⟨symbol,guard,originals,member,present,?_⟩)
          inputs firstNames secondNames first second
          (fun child present => child_compatible expressions inputs firstNames secondNames first second compatible
            symbol guard originals member liveSource child present) common ready firstInputs secondInputs firstReplacements secondReplacements _ _ _ _
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
      (List.mem_filter.mpr ⟨present,?_⟩),aligned.2 (by simpa only [Bool.not_eq_true] using (List.mem_filter.mp retained).2)⟩
    change (!(next.children.any (fun value => value.referenceOf == .empty))) = true
    rw [← aligned.1]
    exact (List.mem_filter.mp retained).2
  · intro row member
    have retained := (normalized_rows common ready.semantic.1.normal.facts secondRows secondResident rawSecond secondMade row).mp member
    obtain ⟨source,included,called⟩ := pair_right secondSource row (List.mem_filter.mp retained).1
    obtain ⟨next,present,otherCall⟩ := pair_left firstSource source included
    have aligned := align source included next row otherCall called
    refine ⟨next,(normalized_rows common ready.semantic.1.normal.facts firstRows firstResident rawFirst firstMade next).mpr
      (List.mem_filter.mpr ⟨present,?_⟩),aligned.2 (by
        rw [aligned.1]
        simpa only [Bool.not_eq_true] using (List.mem_filter.mp retained).2)⟩
    change (!(next.children.any (fun value => value.referenceOf == .empty))) = true
    rw [aligned.1]
    exact (List.mem_filter.mp retained).2

/-- Initial Ready data constructs both calls and their histories from a proved live source induction case. -/
theorem complete (expression : Syntax Symbol Guard) (aligned : Aligned expression)
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (first second : Environment Symbol Guard)
    (compatible : Compatible expression inputs firstNames secondNames first second)
    (before after later final common : State Symbol Guard)
    (firstContext : Context before (inputs.map (InternedFreshOrdinaryLiveInputs.input firstNames)))
    (secondContext : Context later (inputs.map (InternedFreshOrdinaryLiveInputs.input secondNames)))
    (rawFirst rawSecond : Value Symbol Guard)
    (firstRaw : build expression (inputs.map (InternedFreshOrdinaryLiveInputs.input firstNames)) before = .done rawFirst after)
    (secondRaw : build expression (inputs.map (InternedFreshOrdinaryLiveInputs.input secondNames)) later = .done rawSecond final)
    (firstGrowth : Grows after common) (secondGrowth : Grows final common)
    (ready : Ready common)
    (firstInputs : Values common (inputs.map (InternedFreshOrdinaryLiveInputs.input firstNames)))
    (secondInputs : Values common (inputs.map (InternedFreshOrdinaryLiveInputs.input secondNames)))
    (firstReplacements : Replacements common first) (secondReplacements : Replacements common second) :
    ∃ left middle right reader,
      execute rawFirst first common = .done left middle ∧ execute rawSecond second middle = .done right reader ∧
      execute rawFirst first reader = .done left reader ∧ execute rawSecond second reader = .done right reader ∧
      Keeps common middle ∧ Keeps middle reader ∧ Available reader left ∧ Available reader right ∧
      Nonempty (SourceCurrentNativeMuPublication.History common middle) ∧
      Nonempty (SourceCurrentNativeMuPublication.History middle reader) ∧ Related left right := by
  have firstWarm := InternedFreshOrdinaryReplay.build_replay expression _ before common rawFirst after
    firstContext.normal.facts.coherent.valid firstRaw firstGrowth
  have secondWarm := InternedFreshOrdinaryReplay.build_replay expression _ later common rawSecond final
    secondContext.normal.facts.coherent.valid secondRaw secondGrowth
  have firstAvailable := (InternedFreshOrdinaryFacts.build_verified expression _ common
    ready.semantic.1.normal.facts firstInputs).result rawFirst common firstWarm
  have secondAvailable := (InternedFreshOrdinaryFacts.build_verified expression _ common
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
  have firstSource := InternedFreshOrdinaryReplay.build_replay expression _ before reader rawFirst after
    firstContext.normal.facts.coherent.valid firstRaw (grows_trans firstGrowth growth)
  have secondSource := InternedFreshOrdinaryReplay.build_replay expression _ later reader rawSecond final
    secondContext.normal.facts.coherent.valid secondRaw (grows_trans secondGrowth growth)
  have related := aligned Atom inputs firstNames secondNames first second compatible reader secondKept.ready
    (fun value member => secondKept.available value (firstKept.available value (firstInputs value member)))
    (fun value member => secondKept.available value (firstKept.available value (secondInputs value member)))
    (fun name value found => secondKept.available value (firstKept.available value (firstReplacements name value found)))
    (fun name value found => secondKept.available value (firstKept.available value (secondReplacements name value found)))
    rawFirst rawSecond firstSource secondSource left right firstReplay secondReplay
  exact ⟨left,middle,right,reader,firstDone,secondDone,firstReplay,secondReplay,firstKept,secondKept,
    secondKept.available left leftAvailable,rightAvailable,firstHistory,secondHistory,related⟩

end MicroCFTA.SourceCurrentStoredLiveSourceLineage
