import MicroCFTA.SourceCurrentStoredMuRetainedAlignment
import MicroCFTA.SourceCurrentStoredReconstruction
import MicroCFTA.SourceCurrentStoredCallsReplay
import MicroCFTA.SourceCurrentOrdinaryObservationEmpty
import MicroCFTA.SourceCurrentOpenObservationSurvival
import MicroCFTA.InternedFreshOrdinaryDependencies

/-!
# Active reference and ordinary-source reconstruction steps

The reference case substitutes the same value for both callback names.
The ordinary case uses an induction hypothesis only for strict syntax
children. It retains full row fields and ordered child observations through
both raw and stored normalization. Initial ready data constructs both
stored calls. The nested binder and chronological writer cases remain open.
-/
namespace MicroCFTA.SourceCurrentStoredMuActiveChildLineage
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

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- The two own names resolve equally, and both outer maps agree on every captured free name. -/
def Compatible (captures : List (Value Symbol Guard)) (firstName secondName : Reference)
    (first second : Environment Symbol Guard) : Prop :=
  (first firstName).getD (.reference firstName) = (second secondName).getD (.reference secondName) ∧
    ∀ capture ∈ captures, ∀ name ∈ capture.free, first name = second name

/-- A source induction case compares its actual raw calls and actual warm reconstructions. -/
def Aligned (expression : Syntax Symbol Guard) : Prop :=
  ∀ (captures : List (Value Symbol Guard)) (firstName secondName : Reference)
    (first second : Environment Symbol Guard), Compatible captures firstName secondName first second →
  ∀ (common : State Symbol Guard), Ready common →
    Values common (.reference firstName :: captures) → Values common (.reference secondName :: captures) →
    Replacements common first → Replacements common second →
  ∀ rawFirst rawSecond,
    build expression (.reference firstName :: captures) common = .done rawFirst common →
    build expression (.reference secondName :: captures) common = .done rawSecond common →
  ∀ result other,
    execute rawFirst first common = .done result common →
    execute rawSecond second common = .done other common → Related result other

private theorem related_refl (value : Value Symbol Guard) : Related value value :=
  ⟨Iff.rfl, fun depth view => Same.refl depth view [value]⟩

private theorem reference_execute (name : Reference) (environment : Environment Symbol Guard)
    (state : State Symbol Guard) :
    execute (.reference name) environment state = .done ((environment name).getD (.reference name)) state := by
  simp [execute, leaves, Value.free, encode, InternedStoredSubstitution.slot, build, input]

/-- Active lexical references and fixed captures discharge the source base case without an output relation. -/
theorem reference (index : Nat) : Aligned (Symbol := Symbol) (Guard := Guard) (.var index) := by
  intro captures firstName secondName first second compatible common ready firstAvailable secondAvailable
    firstReplacements secondReplacements rawFirst rawSecond firstRaw secondRaw result other firstDone secondDone
  cases index with
  | zero =>
      simp only [build,List.getElem?_cons_zero,Option.getD_some,Outcome.done.injEq] at firstRaw secondRaw
      obtain ⟨rfl,_⟩ := firstRaw
      obtain ⟨rfl,_⟩ := secondRaw
      have same := (Outcome.done.inj ((reference_execute firstName first common).symm.trans firstDone)).1
      have otherSame := (Outcome.done.inj ((reference_execute secondName second common).symm.trans secondDone)).1
      rw [← same,← otherSame,compatible.1]
      exact related_refl _
  | succ index =>
      simp only [build,List.getElem?_cons_succ,Outcome.done.injEq] at firstRaw secondRaw
      obtain ⟨rfl,_⟩ := firstRaw
      obtain ⟨rfl,_⟩ := secondRaw
      have available : Available common (captures[index]?.getD .empty) := by
        cases found : captures[index]? with
        | none => simpa only [found,Option.getD_none] using InternedProbeProvenance.empty_available common
        | some value =>
            simpa only [found,Option.getD_some] using firstAvailable value
              (List.mem_cons_of_mem _ (List.mem_of_getElem? found))
      have agree : ∀ name ∈ (captures[index]?.getD .empty).free, first name = second name := by
        cases found : captures[index]? with
        | none => simp only [Option.getD_none,Value.free,List.not_mem_nil]; intros; contradiction
        | some value =>
            simpa only [found,Option.getD_some] using compatible.2 value (List.mem_of_getElem? found)
      have changed := InternedFreshOrdinaryStoredSubstitution.execute_congr _ first second common
        ready.semantic.1.normal.facts.coherent available agree
      have same := (Outcome.done.inj (firstDone.symm.trans (changed.trans secondDone))).1
      rw [same]
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
    (captures : List (Value Symbol Guard)) (firstName secondName : Reference)
    (first second : Environment Symbol Guard) (compatible : Compatible captures firstName secondName first second)
    (common : State Symbol Guard) (ready : Ready common)
    (firstInputs : Values common (.reference firstName :: captures))
    (secondInputs : Values common (.reference secondName :: captures))
    (firstReplacements : Replacements common first) (secondReplacements : Replacements common second)
    (rawFirst rawSecond left right : List (Value Symbol Guard))
    (firstRaw : buildMany expressions (.reference firstName :: captures) common = .done rawFirst common)
    (secondRaw : buildMany expressions (.reference secondName :: captures) common = .done rawSecond common)
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
                  exact .cons (cases expression List.mem_cons_self captures firstName secondName first second compatible
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

end MicroCFTA.SourceCurrentStoredMuActiveChildLineage
