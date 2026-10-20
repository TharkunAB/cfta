import MicroCFTA.SourceCurrentNativeOriginalPublicationTrace
import MicroCFTA.SourceCurrentNativeOriginalUnionDescent

namespace MicroCFTA.SourceCurrentNativeOriginalIndexedResumption
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome request finish)
open InternedFreshOrdinaryConstruction (build ordinaryLevel)
open InternedFreshOrdinaryFacts (callback)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentNativeMuIssuedHistory (Path)
open SourceCurrentNativeOriginalPublicationTrace (events)
open SourceCurrentBuildStructuralRowOrigins (SourceRow)
open SourceCurrentStoredLiteralRowLineage (RowAt)
open InternedFreshOrdinarySourceHistory (Reached)
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

private theorem binder_before (original : Syntax Symbol Guard) (traceAfter : State Symbol Guard)
    (path : Path empty traceAfter)
    (precompletion : ∀ (index : Nat) outer, (events path)[index]? = some outer →
      ∀ key entry body depth ordinary,
        outer.afterBody.nodeRecords key = some (.mu entry body depth ordinary) →
        ∃ earlierIndex : Nat, ∃ earlier, earlierIndex < index ∧ (events path)[earlierIndex]? = some earlier ∧
          Reached original [] (.binder earlier.smart earlier.expression) earlier.environment earlier.before ∧
          key = earlier.key ∧ Value.mu entry body depth ordinary = earlier.candidate ∧
          earlier.afterBody.nodeRecords earlier.key = none ∧
          Nonempty (Path empty earlier.before) ∧
          Nonempty (Path earlier.before earlier.afterDepth) ∧
          Nonempty (Path earlier.afterDepth earlier.cut) ∧
          Nonempty (Path earlier.allocated earlier.afterBody) ∧
          Grows earlier.after outer.afterBody ∧
          Extends earlier.after.nodes.issued outer.afterBody.nodes.issued)
    (index : Nat) (outer : @Publication Symbol Guard _)
    (selectedOuter : (events path)[index]? = some outer)
    (raw : Value Symbol Guard) (rawAfter : State Symbol Guard)
    (context : Context outer.allocated (.reference (.interned outer.entry.identity) :: outer.environment))
    (built : build outer.expression (.reference (.interned outer.entry.identity) :: outer.environment)
      outer.allocated = .done raw rawAfter)
    (filtered : run (withoutSelfReference (.interned outer.entry.identity) raw) rawAfter =
      (outer.body,outer.afterBody))
    (smart : Bool) (terminalExpression : Syntax Symbol Guard) (terminalInputs : List (Value Symbol Guard))
    (terminalBefore : State Symbol Guard) (terminalRaw : Value Symbol Guard)
    (terminalAfter : State Symbol Guard) (row : EdgeValue Symbol Guard)
    (terminal : SourceRow (.binder smart terminalExpression) terminalInputs terminalBefore terminalRaw terminalAfter row)
    (suffix : Grows terminalAfter rawAfter)
    (suffixIssued : Extends terminalAfter.nodes.issued rawAfter.nodes.issued) :
    ∃ depth afterDepth ordinary cut entry storedBody,
      callback terminalExpression terminalInputs .depth terminalBefore = .done depth afterDepth ∧
      callback terminalExpression terminalInputs (.uninterned (ordinaryLevel depth)) afterDepth = .done ordinary cut ∧
      request smart depth ordinary (callback terminalExpression terminalInputs) cut = .done terminalRaw terminalAfter ∧
      terminalAfter.nodeRecords (muKey depth ordinary) = some (.mu entry storedBody depth ordinary) ∧
      outer.afterBody.nodeRecords (muKey depth ordinary) = some (.mu entry storedBody depth ordinary) ∧
      terminalRaw = finish smart (.mu entry storedBody depth ordinary) ∧ RowAt storedBody row ∧
      Grows terminalAfter outer.afterBody ∧ Extends terminalAfter.nodes.issued outer.afterBody.nodes.issued ∧
      ∃ earlierIndex : Nat, ∃ earlier : @Publication Symbol Guard _, earlierIndex < index ∧
        (events path)[earlierIndex]? = some earlier ∧
        Reached original [] (.binder earlier.smart earlier.expression) earlier.environment earlier.before ∧
        muKey depth ordinary = earlier.key ∧ Value.mu entry storedBody depth ordinary = earlier.candidate ∧
        earlier.afterBody.nodeRecords earlier.key = none ∧
        Nonempty (Path empty earlier.before) ∧
        Nonempty (Path earlier.before earlier.afterDepth) ∧
        Nonempty (Path earlier.afterDepth earlier.cut) ∧
        Nonempty (Path earlier.allocated earlier.afterBody) ∧
        Grows earlier.after outer.afterBody ∧
        Extends earlier.after.nodes.issued outer.afterBody.nodes.issued := by
  cases terminal with
  | @binder smart expression inputs before value after depth afterDepth ordinary cut entry storedBody row
      depthDone ordinaryDone requested selected returned inside =>
    have returnedContext : Context rawAfter
        (.reference (.interned outer.entry.identity) :: outer.environment) := by
      simpa only [built,Outcome.state] using context.build outer.expression
    have filterGrowth := (run_correct (withoutSelfReference (.interned outer.entry.identity) raw)
      rawAfter returnedContext.base.normal.facts.coherent.valid).2
    have filterIssued := run_issued_extends (withoutSelfReference (.interned outer.entry.identity) raw)
      rawAfter returnedContext.base.normal.facts.coherent.valid
    rw [filtered] at filterGrowth filterIssued
    have beforeGrowth : Grows terminalAfter outer.afterBody := grows_trans suffix filterGrowth
    have beforeIssued : Extends terminalAfter.nodes.issued outer.afterBody.nodes.issued :=
      extends_trans suffixIssued filterIssued
    have present := beforeGrowth.nodeRecords (muKey depth ordinary) _ selected
    exact ⟨depth,afterDepth,ordinary,cut,entry,storedBody,depthDone,ordinaryDone,requested,
      selected,present,returned,inside,beforeGrowth,beforeIssued,
      precompletion index outer selectedOuter (muKey depth ordinary) entry storedBody depth ordinary present⟩

end MicroCFTA.SourceCurrentNativeOriginalIndexedResumption
