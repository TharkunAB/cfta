import MicroCFTA.SourceCurrentSourceRowTerminalSuffix
import MicroCFTA.SourceCurrentSourceCaptureOriginalSlots

/-!
# Actual node or binder terminals of original source rows

The original empty capture list excludes a row-bearing variable terminal.
The same indexed source-union suffix retains the terminal call, full row,
source context, rooted entry and physical and issued intervals.
-/
namespace MicroCFTA.SourceCurrentNativeOriginalRowTerminals
open Cache InternedConstructorTemplates
open InternedNestedConstruction (Syntax Outcome work request)
open InternedFreshOrdinaryConstruction (build ordinaryLevel)
open InternedFreshOrdinaryFacts (callback)
open InternedFreshOrdinarySourceHistory (Reached)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentBuildStructuralRowOrigins (SourceRow)
variable {Symbol Guard : Type}

private theorem source_done [DecidableEq (EdgeKey Symbol Guard)]
    {expression : Syntax Symbol Guard} {inputs : List (Value Symbol Guard)}
    {before : State Symbol Guard} {raw : Value Symbol Guard} {after : State Symbol Guard}
    {row : EdgeValue Symbol Guard} (source : SourceRow expression inputs before raw after row) :
    build expression inputs before = .done raw after := by
  cases source with
  | capture found _ => simp only [build,found,Option.getD_some]
  | node built made _ _ _ => simp only [build,built,Outcome.bind,work,made]
  | union built made _ _ _ _ _ _ _ => simp only [build,built,Outcome.bind,work,made]
  | @binder smart expression inputs before raw after depth afterDepth ordinary cut entry body row
      depthDone ordinaryDone requested _ _ _ =>
    simp only [build]
    change ((callback expression inputs .depth before).bind fun depth afterDepth =>
      (callback expression inputs (.uninterned (ordinaryLevel depth)) afterDepth).bind
        fun ordinary cut => request smart depth ordinary (callback expression inputs) cut) = .done raw after
    simpa only [depthDone,ordinaryDone,Outcome.bind] using requested

/-- An original source row retains the same actual node or binder terminal and whole-call suffix. -/
theorem terminal [DecidableEq (EdgeKey Symbol Guard)]
    {original expression : Syntax Symbol Guard} {inputs : List (Value Symbol Guard)}
    {before : State Symbol Guard} {raw : Value Symbol Guard} {after : State Symbol Guard}
    {fullRow : EdgeValue Symbol Guard}
    (context : Context before inputs)
    (reached : Reached original [] expression inputs before)
    (source : SourceRow expression inputs before raw after fullRow) :
    ∃ terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter,
      SourceRow terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter fullRow ∧
      build terminalExpression terminalInputs terminalBefore = .done terminalRaw terminalAfter ∧
      ((∃ rows, terminalExpression = Syntax.node rows) ∨
        ∃ smart body, terminalExpression = Syntax.binder smart body) ∧
      (∀ members, terminalExpression ≠ Syntax.union members) ∧
      Context terminalBefore terminalInputs ∧
      Reached original [] terminalExpression terminalInputs terminalBefore ∧
      sizeOf terminalExpression ≤ sizeOf expression ∧
      Grows terminalAfter after ∧ Extends terminalAfter.nodes.issued after.nodes.issued := by
  obtain ⟨terminalExpression,terminalInputs,terminalBefore,terminalRaw,terminalAfter,
    terminalSource,nonunion,terminalContext,terminalReached,bound,growth,issued⟩ :=
    SourceCurrentSourceRowTerminalSuffix.terminal_source context reached source
  have kind : (∃ rows, terminalExpression = Syntax.node rows) ∨
      ∃ smart body, terminalExpression = Syntax.binder smart body := by
    cases terminalSource with
    | capture found inside =>
      obtain ⟨crossings,path,_⟩ := terminalReached
      exact (SourceCurrentSourceCaptureOriginalSlots.empty_initial path _ _ found fullRow inside).elim
    | node => exact .inl ⟨_,rfl⟩
    | union => exact (nonunion _ rfl).elim
    | binder => exact .inr ⟨_,_,rfl⟩
  exact ⟨terminalExpression,terminalInputs,terminalBefore,terminalRaw,terminalAfter,
    terminalSource,source_done terminalSource,kind,nonunion,terminalContext,terminalReached,bound,growth,issued⟩

end MicroCFTA.SourceCurrentNativeOriginalRowTerminals

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000

#check @MicroCFTA.SourceCurrentNativeOriginalRowTerminals.terminal
#print MicroCFTA.SourceCurrentNativeOriginalRowTerminals.terminal
#print axioms MicroCFTA.SourceCurrentNativeOriginalRowTerminals.terminal
