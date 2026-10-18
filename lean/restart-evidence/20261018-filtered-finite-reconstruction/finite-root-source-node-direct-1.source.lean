import MicroCFTA.SourceCurrentFiniteRootReconstruction
import MicroCFTA.SourceCurrentFiniteObservationExecution
import MicroCFTA.SourceCurrentPublicationNodeRowSurvival

/-!
# Literal node matching from indexed source children

Actual source calls pair surviving rows at the same original source index.
Each ordered child pair retains its actual source calls at the execution
heap. Strict child hypotheses derive finite agreement after stored calls.
The result keeps full row symbols and guards. Nested used source binders
remain permitted by the indexed child hypothesis. No parent comparison
or parent root match is assumed.
-/
namespace MicroCFTA.SourceCurrentFiniteRootSourceNode
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedNestedProvenance (Values Edges)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryContext
open InternedStoredSubstitution (Environment Replacements)
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceEqualityRequiredCache (Ready Ordinary)
open SourceCurrentReaderFiniteOrdinaryStep (RelatedAt)
open SourceCurrentReaderReplacementSlots (Paired)
open SourceCurrentFiniteObservationExecution (AlignedAt)
open SourceCurrentFiniteRootReconstruction (Executions)
open SourceCurrentUsedBinderRootAlternatives (RootMatch)
open SourceCurrentStoredMuRetainedAlignment (RowCall)
open SourceCurrentLiteralRootParts (Literal Row)
open SourceCurrentOpenObservations (RowMatch)
open InternedBinderProtocol (Reference)

variable [DecidableEq (EdgeKey Symbol Guard)]

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

private theorem children_executions (expressions : List (Syntax Symbol Guard))
    (depth : Nat) (view common : State Symbol Guard)
    (cases : ∀ expression ∈ expressions, AlignedAt depth view common expression)
    (leftInputs rightInputs : List (Value Symbol Guard)) (first second : Environment Symbol Guard)
    (paired : Paired (RelatedAt depth view) first second leftInputs rightInputs)
    (ready : Ready common) (firstInputs : Values common leftInputs) (secondInputs : Values common rightInputs)
    (firstReplacements : Replacements common first) (secondReplacements : Replacements common second)
    (rawFirst rawSecond : List (Value Symbol Guard))
    (firstRaw : buildMany expressions leftInputs common = .done rawFirst common)
    (secondRaw : buildMany expressions rightInputs common = .done rawSecond common) :
    All₂ (Executions depth view common first second) rawFirst rawSecond := by
  have firstSource := source_children expressions leftInputs common ready.semantic.1.normal.facts.coherent.valid rawFirst firstRaw
  have secondSource := source_children expressions rightInputs common ready.semantic.1.normal.facts.coherent.valid rawSecond secondRaw
  clear firstRaw secondRaw
  induction firstSource generalizing rawSecond with
  | nil => cases secondSource; exact .nil
  | @cons expression raw expressions raws firstRaw remaining ih =>
      cases secondSource with
      | cons secondRaw secondRemaining =>
          refine .cons ?_ (ih (fun child member => cases child (List.mem_cons_of_mem _ member)) _ secondRemaining)
          intro left right firstDone secondDone
          exact cases expression List.mem_cons_self leftInputs rightInputs first second paired ready
            firstInputs secondInputs firstReplacements secondReplacements _ _ firstRaw secondRaw
            left right firstDone secondDone

private theorem source_ordinary (expressions : List (EdgeSyntax Symbol Guard))
    (inputs : List (Value Symbol Guard)) (before after : State Symbol Guard) (context : Context before inputs)
    (value : Value Symbol Guard) (actual : build (.node expressions) inputs before = .done value after) :
    Ordinary value := by
  cases called : buildEdges expressions inputs before with
  | pending key middle => simp only [build,called,Outcome.bind] at actual; cases actual
  | done rows middle =>
      have made := Outcome.done.inj (by simpa only [build,called,Outcome.bind,InternedNestedConstruction.work] using actual)
      have checked := InternedFreshOrdinaryFacts.buildEdges_verified expressions inputs before context.normal.facts context.inputs
      have facts : InternedNestedFacts.Facts middle := by simpa only [called,Outcome.state] using checked.facts
      have plain := SourceEqualityRequiredCache.node_ordinary rows middle facts (checked.result rows middle called)
      rw [made.1] at plain
      exact plain

private theorem no_literal (value : Value Symbol Guard) (plain : Ordinary value)
    (atom : Value Symbol Guard) (found : Literal value atom) : False := by
  cases value <;> try cases plain <;> cases found

private theorem ordinary_row (value : Value Symbol Guard) (plain : Ordinary value) (row : EdgeValue Symbol Guard) :
    Row value row ↔ row ∈ InternedEdgeResidency.nodeEdges value := by
  cases value <;> try cases plain
  case empty => exact ⟨by intro impossible; cases impossible,by intro impossible; cases impossible⟩
  case node entry rows depth free => exact SourceCurrentLiteralRootParts.row_node entry rows depth free row

private theorem row_match (expressions : List (EdgeSyntax Symbol Guard)) (depth : Nat)
    (view common : State Symbol Guard) (leftInputs rightInputs : List (Value Symbol Guard))
    (first second : Environment Symbol Guard) (paired : Paired (RelatedAt depth view) first second leftInputs rightInputs)
    (ready : Ready common) (firstInputs : Values common leftInputs) (secondInputs : Values common rightInputs)
    (firstReplacements : Replacements common first) (secondReplacements : Replacements common second)
    (before later firstAfter secondAfter : State Symbol Guard)
    (firstRows secondRows : List (EdgeValue Symbol Guard)) (index : Nat) (symbol : Symbol) (guard : Guard)
    (children : List (Syntax Symbol Guard))
    (left : RowCall expressions leftInputs before firstRows firstAfter common index symbol guard children)
    (right : RowCall expressions rightInputs later secondRows secondAfter common index symbol guard children)
    (cases : ∀ child ∈ children, AlignedAt depth view common child) :
    RowMatch (Executions depth view common first second) left.output right.output := by
  have firstWarm := InternedFreshOrdinaryReplay.buildMany_replays children leftInputs left.current common left.values left.middle
    left.context.normal.facts.coherent.valid left.called left.middle_growth
  have secondWarm := InternedFreshOrdinaryReplay.buildMany_replays children rightInputs right.current common right.values right.middle
    right.context.normal.facts.coherent.valid right.called right.middle_growth
  refine ⟨left.symbol_eq.trans right.symbol_eq.symm,left.guard_eq.trans right.guard_eq.symm,?_⟩
  rw [left.children_eq,right.children_eq]
  exact children_executions children depth view common cases leftInputs rightInputs first second paired
    ready firstInputs secondInputs firstReplacements secondReplacements left.values right.values firstWarm secondWarm

/-- Actual node source calls derive literal root matching from indexed strict child execution cases. -/
theorem node (expressions : List (EdgeSyntax Symbol Guard)) (captures : List (Value Symbol Guard))
    (firstName secondName : Reference) (depth : Nat) (view common : State Symbol Guard)
    (children : ∀ index symbol guard originals, expressions[index]? = some (.mk symbol guard originals) →
      ∀ childIndex child, originals[childIndex]? = some child →
        sizeOf child < sizeOf (.node expressions : Syntax Symbol Guard) → AlignedAt depth view common child)
    (first second : Environment Symbol Guard)
    (paired : Paired (RelatedAt depth view) first second (.reference firstName :: captures) (.reference secondName :: captures))
    (ready : Ready common)
    (firstInputs : Values common (.reference firstName :: captures)) (secondInputs : Values common (.reference secondName :: captures))
    (firstReplacements : Replacements common first) (secondReplacements : Replacements common second)
    (before after later final : State Symbol Guard)
    (firstContext : Context before (.reference firstName :: captures))
    (secondContext : Context later (.reference secondName :: captures))
    (firstValue secondValue : Value Symbol Guard)
    (called : build (.node expressions) (.reference firstName :: captures) before = .done firstValue after)
    (other : build (.node expressions) (.reference secondName :: captures) later = .done secondValue final)
    (firstGrowth : Grows after common) (secondGrowth : Grows final common)
    (references : Reference → Reference → Prop) :
    RootMatch references (Executions depth view common first second) firstValue secondValue := by
  have firstPlain := source_ordinary expressions _ before after firstContext firstValue called
  have secondPlain := source_ordinary expressions _ later final secondContext secondValue other
  have childCases (index symbol guard originals) (source : expressions[index]? = some (.mk symbol guard originals))
      (child : Syntax Symbol Guard) (member : child ∈ originals) : AlignedAt depth view common child := by
    obtain ⟨childIndex,found⟩ := List.mem_iff_getElem?.mp member
    apply children index symbol guard originals source childIndex child found
    have small := List.sizeOf_lt_of_mem member
    have rowSmall := List.sizeOf_lt_of_mem (List.mem_of_getElem? source)
    simp only [Syntax.node.sizeOf_spec,EdgeSyntax.mk.sizeOf_spec] at *
    omega
  refine ⟨fun atom found => False.elim (no_literal _ firstPlain atom found),
    fun atom found => False.elim (no_literal _ secondPlain atom found),?_,?_⟩
  · intro row found
    obtain ⟨lefts,leftAfter,rights,rightAfter,index,symbol,guard,originals,left,right,
      _,_,_,_,same,member,_,_,_,_,_⟩ := SourceCurrentPublicationNodeRowSurvival.node expressions captures
      secondName firstName later final before after common secondContext firstContext secondValue firstValue
      other called secondGrowth firstGrowth row ((ordinary_row firstValue firstPlain row).mp found)
    refine ⟨left.output,(ordinary_row secondValue secondPlain left.output).mpr member,?_⟩
    rw [←same]
    exact row_match expressions depth view common _ _ first second paired ready firstInputs secondInputs
      firstReplacements secondReplacements before later rightAfter leftAfter rights lefts index symbol guard originals
      right left (childCases index symbol guard originals right.source)
  · intro row found
    obtain ⟨lefts,leftAfter,rights,rightAfter,index,symbol,guard,originals,left,right,
      _,_,_,_,same,member,_,_,_,_,_⟩ := SourceCurrentPublicationNodeRowSurvival.node expressions captures
      firstName secondName before after later final common firstContext secondContext firstValue secondValue
      called other firstGrowth secondGrowth row ((ordinary_row secondValue secondPlain row).mp found)
    refine ⟨left.output,(ordinary_row firstValue firstPlain left.output).mpr member,?_⟩
    rw [←same]
    exact row_match expressions depth view common _ _ first second paired ready firstInputs secondInputs
      firstReplacements secondReplacements before later leftAfter rightAfter lefts rights index symbol guard originals
      left right (childCases index symbol guard originals left.source)

end MicroCFTA.SourceCurrentFiniteRootSourceNode
