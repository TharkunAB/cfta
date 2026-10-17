import MicroCFTA.InternedFreshOrdinaryPlanEquivalence
import MicroCFTA.InternedFreshOrdinaryReplay

/-!
# Actual row plans replay at one common heap

Each row evaluates its ordered children and requests its exact symbol and
full guard. Equivalent captured child plans have identical row outcomes.
A completed row list supplies every row's common-heap replay in order.
No caller supplies a separate completed row execution.
-/
namespace MicroCFTA.SourceCurrentRowPlanReplay
open Cache InternedConstructorTemplates
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work Growing Replays)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryGrowth InternedFreshOrdinaryReplay
open InternedFreshOrdinaryPlanEquivalence
open Language

/-- A literal row plan evaluates all children before its exact edge request. -/
def rowRun [DecidableEq (EdgeKey Symbol Guard)] (row : EdgeSyntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) : Outcome Symbol Guard (EdgeValue Symbol Guard) :=
  match row with
  | .mk symbol guard children =>
      (buildMany children environment state).bind fun values middle => work (makeEdge symbol guard values) middle

/-- Equivalent captured child plans retain the exact full row outcome at any current heap. -/
theorem equivalent [DecidableEq (EdgeKey Symbol Guard)]
    (firstSymbol secondSymbol : Symbol) (firstGuard secondGuard : Guard)
    (first second : List (Syntax Symbol Guard)) (firstInputs secondInputs : List (Value Symbol Guard))
    (state : State Symbol Guard) (symbol : firstSymbol = secondSymbol) (guard : firstGuard = secondGuard)
    (children : ManyEquivalent first firstInputs second secondInputs) :
    rowRun (.mk firstSymbol firstGuard first) firstInputs state =
      rowRun (.mk secondSymbol secondGuard second) secondInputs state := by
  subst secondSymbol secondGuard
  simp only [rowRun, buildMany_exact first firstInputs second secondInputs state children]

private theorem growing [DecidableEq (EdgeKey Symbol Guard)] (row : EdgeSyntax Symbol Guard)
    (environment : List (Value Symbol Guard)) : Growing (rowRun row environment) := by
  cases row with
  | mk symbol guard children =>
      intro state valid
      exact InternedNestedConstruction.bind_correct _ _ state (buildMany_correct children environment state valid)
        (fun values middle retained => InternedNestedConstruction.work_correct (makeEdge symbol guard values) middle retained)

/-- Every completed literal row replays its original complete edge after actual cache growth. -/
theorem replays [DecidableEq (EdgeKey Symbol Guard)] (row : EdgeSyntax Symbol Guard)
    (environment : List (Value Symbol Guard)) : Replays (rowRun row environment) := by
  cases row with
  | mk symbol guard children =>
      exact InternedNestedConstruction.bind_replays (buildMany children environment)
        (fun values state => work (makeEdge symbol guard values) state)
        (buildMany_correct children environment)
        (fun values => InternedNestedConstruction.work_correct (makeEdge symbol guard values))
        (buildMany_replays children environment)
        (fun values => InternedNestedConstruction.work_replays (makeEdge symbol guard values))

private theorem cons_run [DecidableEq (EdgeKey Symbol Guard)] (first : EdgeSyntax Symbol Guard)
    (rest : List (EdgeSyntax Symbol Guard)) (environment : List (Value Symbol Guard)) (state : State Symbol Guard) :
    buildEdges (first :: rest) environment state =
      (rowRun first environment state).bind fun value middle =>
        (buildEdges rest environment middle).bind fun values after => .done (value :: values) after := by
  cases first with
  | mk symbol guard children =>
      simp only [buildEdges, rowRun]
      cases actual : buildMany children environment state <;> rfl

/-- A completed row list derives every original row's exact replay at one common later heap. -/
theorem rows [DecidableEq (EdgeKey Symbol Guard)] (originals : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (before : State Symbol Guard) (outputs : List (EdgeValue Symbol Guard))
    (after common : State Symbol Guard) (valid : Valid before)
    (actual : buildEdges originals environment before = .done outputs after) (growth : Grows after common) :
    All₂ (fun original output => rowRun original environment common = .done output common) originals outputs := by
  induction originals generalizing before outputs after with
  | nil =>
      simp only [buildEdges, Outcome.done.injEq] at actual
      rcases actual with ⟨rfl, rfl⟩
      exact .nil
  | cons first rest ih =>
      rw [cons_run] at actual
      cases firstDone : rowRun first environment before with
      | pending key middle => simp only [firstDone, Outcome.bind] at actual; cases actual
      | done output middle =>
          have prefix := growing first environment before valid
          have middleValid : Valid middle := by simpa only [firstDone, Outcome.state] using prefix.1
          simp only [firstDone, Outcome.bind] at actual
          cases restDone : buildEdges rest environment middle with
          | pending key final => simp only [restDone, Outcome.bind] at actual; cases actual
          | done values final =>
              simp only [restDone, Outcome.bind, Outcome.done.injEq] at actual
              rcases actual with ⟨rfl, rfl⟩
              have suffix : Grows middle after := by
                simpa only [restDone, Outcome.state] using (buildEdges_correct rest environment middle middleValid).2
              exact .cons (replays first environment before common output middle valid firstDone (grows_trans suffix growth))
                (ih middle values after middleValid restDone growth)

end MicroCFTA.SourceCurrentRowPlanReplay
