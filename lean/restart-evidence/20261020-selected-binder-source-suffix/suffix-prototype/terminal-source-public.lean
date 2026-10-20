import MicroCFTA.SourceCurrentBuildStructuralRowOrigins
import MicroCFTA.InternedFreshOrdinarySourceHistory

/-!
# Actual source-row terminal suffixes

The same source row reaches its actual nonunion terminal call. Source-union
prefixes retain its rooted entry. The selected member return, actual suffix
calls and final union work derive physical and issued growth to the whole
return heap.
-/
namespace MicroCFTA.SourceCurrentSourceRowTerminalSuffix
open Cache InternedConstructorTemplates
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryFacts (buildMany_verified)
open InternedFreshOrdinarySourceHistory (Reached)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentBuildStructuralRowOrigins (SourceRow)

/-- A source row retains its actual nonunion terminal receipt and derived whole-call suffix. -/
theorem terminal_source [DecidableEq (EdgeKey Symbol Guard)]
    {root expression : Syntax Symbol Guard} {initial inputs : List (Value Symbol Guard)}
    {before : State Symbol Guard} {raw : Value Symbol Guard} {after : State Symbol Guard}
    {fullRow : EdgeValue Symbol Guard}
    (context : Context before inputs)
    (reached : Reached root initial expression inputs before)
    (source : SourceRow expression inputs before raw after fullRow) :
    ∃ terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter,
      SourceRow terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter fullRow ∧
      (∀ members, terminalExpression ≠ Syntax.union members) ∧
      Context terminalBefore terminalInputs ∧
      Reached root initial terminalExpression terminalInputs terminalBefore ∧
      sizeOf terminalExpression ≤ sizeOf expression ∧
      Grows terminalAfter after ∧ Extends terminalAfter.nodes.issued after.nodes.issued := by
  have descend {currentExpression : Syntax Symbol Guard} {currentInputs : List (Value Symbol Guard)}
      {start : State Symbol Guard} {value : Value Symbol Guard} {stop : State Symbol Guard}
      {row : EdgeValue Symbol Guard}
      (part : SourceRow currentExpression currentInputs start value stop row) :
      Context start currentInputs → Reached root initial currentExpression currentInputs start →
      ∃ terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter,
        SourceRow terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter row ∧
        (∀ members, terminalExpression ≠ Syntax.union members) ∧
        Context terminalBefore terminalInputs ∧
        Reached root initial terminalExpression terminalInputs terminalBefore ∧
        sizeOf terminalExpression ≤ sizeOf currentExpression ∧
        Grows terminalAfter stop ∧ Extends terminalAfter.nodes.issued stop.nodes.issued := by
    induction part with
    | @capture currentInputs state value row slot found inside =>
      intro currentContext currentReached
      refine ⟨.var slot,currentInputs,state,value,state,.capture found inside,?_,
        currentContext,currentReached,Nat.le_refl _,grows_refl _,extends_refl _⟩
      intro members impossible
      cases impossible
    | @node expressions currentInputs start value stop rows middle symbol guard children row
        sourceIndex outputIndex built made canonical call same =>
      intro currentContext currentReached
      refine ⟨.node expressions,currentInputs,start,value,stop,.node built made canonical call same,?_,
        currentContext,currentReached,Nat.le_refl _,grows_refl _,extends_refl _⟩
      intro members impossible
      cases impossible
    | @union expressions currentInputs start value stop values middle member memberValue current next row
        index built made syntaxSelected valueSelected earlier memberContext called suffix nested ih =>
      intro currentContext currentReached
      have earlierFacts := buildMany_verified (expressions.take index) currentInputs start
        currentContext.base.normal.facts currentContext.base.inputs
      have earlierGrowth : Grows start current := by
        simpa only [earlier,Outcome.state] using earlierFacts.growth
      have memberReached : Reached root initial member currentInputs current :=
        (currentReached.union (List.mem_of_getElem? syntaxSelected)).grows earlierGrowth
      obtain ⟨terminalExpression,terminalInputs,terminalBefore,terminalRaw,terminalAfter,
        terminalSource,nonunion,terminalContext,terminalReached,terminalBound,terminalGrowth,terminalIssued⟩ :=
        ih memberContext memberReached
      have returnContext : Context next currentInputs := by
        simpa only [called,Outcome.state] using memberContext.build member
      have suffixFacts := buildMany_verified (expressions.drop (index + 1)) currentInputs next
        returnContext.base.normal.facts returnContext.base.inputs
      have suffixGrowth : Grows next middle := by
        simpa only [suffix,Outcome.state] using suffixFacts.growth
      have suffixIssued : Extends next.nodes.issued middle.nodes.issued := by
        simpa only [suffix,Outcome.state] using suffixFacts.history
      have middleValid : Valid middle := by
        simpa only [suffix,Outcome.state] using suffixFacts.facts.coherent.valid
      have unionGrowth : Grows middle stop := by
        simpa only [made] using (InternedConstructorTemplates.run_correct (makeUnion values) middle middleValid).2
      have unionIssued : Extends middle.nodes.issued stop.nodes.issued := by
        simpa only [made] using InternedProbeProvenance.run_issued_extends (makeUnion values) middle middleValid
      have memberBound : sizeOf member ≤ sizeOf (Syntax.union expressions) := by
        have small := List.sizeOf_lt_of_mem (List.mem_of_getElem? syntaxSelected)
        simp only [Syntax.union.sizeOf_spec]
        omega
      exact ⟨terminalExpression,terminalInputs,terminalBefore,terminalRaw,terminalAfter,
        terminalSource,nonunion,terminalContext,terminalReached,Nat.le_trans terminalBound memberBound,
        grows_trans terminalGrowth (grows_trans suffixGrowth unionGrowth),
        extends_trans terminalIssued (extends_trans suffixIssued unionIssued)⟩
    | @binder smart body currentInputs start value stop depth afterDepth ordinary cut entry stored row
        depthDone ordinaryDone requested present returned inside =>
      intro currentContext currentReached
      refine ⟨.binder smart body,currentInputs,start,value,stop,
        .binder depthDone ordinaryDone requested present returned inside,?_,currentContext,currentReached,
        Nat.le_refl _,grows_refl _,extends_refl _⟩
      intro members impossible
      cases impossible
  exact descend source context reached

end MicroCFTA.SourceCurrentSourceRowTerminalSuffix

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.SourceCurrentSourceRowTerminalSuffix.terminal_source
#print MicroCFTA.SourceCurrentSourceRowTerminalSuffix.terminal_source
#print axioms MicroCFTA.SourceCurrentSourceRowTerminalSuffix.terminal_source
