import MicroCFTA.SourceCurrentNativeCapturedMuUnfoldRows
import MicroCFTA.SourceCurrentNativeOriginalRowTerminals

/-!
# Original source terminals from one observed Mu writer

One selected publication and raw callback stay fixed across all rows.
Each stored row and actual unfolded row retains its node or binder source
terminal and the exact suffix to that same raw callback return.
-/
namespace MicroCFTA.SourceCurrentNativeOriginalObservedTerminals
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax)
open InternedBinderProtocol (NodeKey)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentNativeMuIssuedHistory (Path)
open InternedFreshOrdinarySourceHistory (Reached)
open SourceCurrentStoredLiteralRowLineage (RowAt)
open SourceCurrentBuildStructuralRowOrigins (SourceRow)
open SourceCurrentLiteralRootParts (Row)
open SourceCurrentStoredSubstitutionCalls (Calls)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceCurrentNativeCapturedMuUnfoldRows (Observed)

/-- The same original row has an actual node or binder terminal and an exact raw-callback suffix. -/
def Terminal {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]
    (original expression : Syntax Symbol Guard) (after : State Symbol Guard) (row : EdgeValue Symbol Guard) : Prop :=
  ∃ terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter,
    SourceRow terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter row ∧
    InternedFreshOrdinaryConstruction.build terminalExpression terminalInputs terminalBefore = .done terminalRaw terminalAfter ∧
    ((∃ rows, terminalExpression = Syntax.node rows) ∨
      ∃ smart body, terminalExpression = Syntax.binder smart body) ∧
    (∀ members, terminalExpression ≠ Syntax.union members) ∧
    Context terminalBefore terminalInputs ∧
    Reached original [] terminalExpression terminalInputs terminalBefore ∧
    sizeOf terminalExpression ≤ sizeOf expression ∧
    Grows terminalAfter after ∧ Extends terminalAfter.nodes.issued after.nodes.issued

local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- One observed original writer supplies terminals for all stored rows and all actual unfold rows. -/
theorem of_observed (original : Syntax Symbol Guard) (before reader : Heap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Node) (current : Heap)
    (observed : Observed original [] before reader key entry body depth ordinary current) :
    ∃ event : @Publication Symbol Guard _,
      Reached original [] (.binder event.smart event.expression) event.environment event.before ∧
      key = event.key ∧ entry = event.entry ∧ body = event.body ∧ depth = event.depth ∧ ordinary = event.ordinary ∧
      event.afterBody.nodeRecords event.key = none ∧
      Nonempty (Path before event.before) ∧
      Nonempty (Path event.before event.afterDepth) ∧
      Nonempty (Path event.afterDepth event.cut) ∧
      Nonempty (Path event.allocated event.afterBody) ∧
      Grows event.after reader ∧ Extends event.after.nodes.issued reader.nodes.issued ∧
      ∃ raw rawAfter,
        InternedFreshOrdinaryConstruction.build event.expression
          (.reference (.interned event.entry.identity) :: event.environment) event.allocated = .done raw rawAfter ∧
        run (withoutSelfReference (.interned event.entry.identity) raw) rawAfter = (event.body,event.afterBody) ∧
        Context event.allocated (.reference (.interned event.entry.identity) :: event.environment) ∧
        Reached original [] event.expression (.reference (.interned event.entry.identity) :: event.environment)
          event.allocated ∧
        (∀ row, RowAt body row → RowAt raw row ∧
          SourceRow event.expression (.reference (.interned event.entry.identity) :: event.environment)
            event.allocated raw rawAfter row ∧ Terminal original event.expression rawAfter row) ∧
        ∀ value after,
          InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) current = .done value after →
          SemanticHeap after ∧ Grows current after ∧ Extends current.nodes.issued after.nodes.issued ∧
            Available after value ∧ Nonempty (SourceCurrentNativeMuPublication.History empty after) ∧
            ∀ row, Row value row →
          ∃ originalRow, RowAt body originalRow ∧ row.entry.key.symbol = originalRow.entry.key.symbol ∧
            row.entry.key.constraint = originalRow.entry.key.constraint ∧ row.children.length = originalRow.children.length ∧
            (row = originalRow ∨ ∃ lexical current next, Calls lexical originalRow.children current row.children next) ∧
            RowAt raw originalRow ∧
            SourceRow event.expression (.reference (.interned event.entry.identity) :: event.environment)
              event.allocated raw rawAfter originalRow ∧ Terminal original event.expression rawAfter originalRow := by
  obtain ⟨event,reached,keySame,entrySame,bodySame,depthSame,ordinarySame,missing,
    earlier,depthPath,ordinaryPath,bodyPath,growth,issued,raw,rawAfter,built,filtered,context,
    callbackReached,rows,unfolds⟩ := observed
  refine ⟨event,reached,keySame,entrySame,bodySame,depthSame,ordinarySame,missing,
    earlier,depthPath,ordinaryPath,bodyPath,growth,issued,raw,rawAfter,built,filtered,context,
    callbackReached,?_,?_⟩
  · intro row inside
    obtain ⟨rawRow,source⟩ := rows row inside
    exact ⟨rawRow,source,SourceCurrentNativeOriginalRowTerminals.terminal context callbackReached source⟩
  · intro value after actual
    obtain ⟨semanticAfter,nextGrowth,nextIssued,available,published,anchors⟩ := unfolds value after actual
    refine ⟨semanticAfter,nextGrowth,nextIssued,available,published,?_⟩
    intro row literal
    obtain ⟨originalRow,inside,symbol,guard,arity,calls,rawRow,source⟩ := anchors row literal
    exact ⟨originalRow,inside,symbol,guard,arity,calls,rawRow,source,
      SourceCurrentNativeOriginalRowTerminals.terminal context callbackReached source⟩

end MicroCFTA.SourceCurrentNativeOriginalObservedTerminals

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000

#check @MicroCFTA.SourceCurrentNativeOriginalObservedTerminals.Terminal
#print MicroCFTA.SourceCurrentNativeOriginalObservedTerminals.Terminal
#print axioms MicroCFTA.SourceCurrentNativeOriginalObservedTerminals.Terminal

#check @MicroCFTA.SourceCurrentNativeOriginalObservedTerminals.of_observed
#print MicroCFTA.SourceCurrentNativeOriginalObservedTerminals.of_observed
#print axioms MicroCFTA.SourceCurrentNativeOriginalObservedTerminals.of_observed
