import MicroCFTA.SourceCurrentNativeOriginalObservedTerminals
import MicroCFTA.SourceCurrentNativeOriginalBinderResume

/-!
# Actual node and binder returns from one observed source writer

The enclosing publication and callback stay fixed across all rows.
Each terminal keeps the same actual source call and callback suffix.
A node keeps its indexed row call. A binder keeps its selected writer.
-/
namespace MicroCFTA.SourceCurrentNativeOriginalObservedResume
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax request finish)
open InternedFreshOrdinaryConstruction (build buildEdges ordinaryLevel)
open InternedFreshOrdinaryFacts (callback)
open InternedBinderProtocol (NodeKey)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentNativeMuIssuedHistory (Path)
open InternedFreshOrdinarySourceHistory (Reached)
open SourceCurrentStoredLiteralRowLineage (RowAt)
open SourceCurrentBuildStructuralRowOrigins (SourceRow)
open SourceCurrentLiteralRootParts (Row)
open SourceCurrentStoredSubstitutionCalls (Calls)
open SourceCurrentStoredMuRetainedAlignment (RowCall)
open InternedEdgeResidency (nodeEdges)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceCurrentNativeCapturedMuUnfoldRows (Observed)
open SourceCurrentNativeOriginalObservedTerminals (Terminal)
open SourceCurrentCompletedBuildRootedWriters (Written)
open SourceCurrentNativeCapturedMuStoredRows (Stored)

/-- This bound uses the same generic syntax size function as Terminal. -/
def SyntaxBound {Symbol Guard : Type} (terminal expression : Syntax Symbol Guard) : Prop :=
  sizeOf terminal ≤ sizeOf expression

local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem terminal_resume (original : Syntax Symbol Guard) (sourceRoot : Node) (sourceHeap : Heap)
    (sourceBuilt : build original [] empty = .done sourceRoot sourceHeap)
    (event : @Publication Symbol Guard _) (raw : Node) (rawAfter : Heap)
    (context : Context event.allocated (.reference (.interned event.entry.identity) :: event.environment))
    (built : build event.expression (.reference (.interned event.entry.identity) :: event.environment)
      event.allocated = .done raw rawAfter)
    (filtered : run (withoutSelfReference (.interned event.entry.identity) raw) rawAfter = (event.body,event.afterBody))
    (growth : Grows event.after sourceHeap)
    (issued : Extends event.after.nodes.issued sourceHeap.nodes.issued)
    (row : EdgeValue Symbol Guard) (terminal : Terminal original event.expression rawAfter row) :
    ∃ terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter,
      SourceRow terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter row ∧
      build terminalExpression terminalInputs terminalBefore = .done terminalRaw terminalAfter ∧
      ((∃ expressions, terminalExpression = Syntax.node expressions) ∨
        ∃ smart terminalBody, terminalExpression = Syntax.binder smart terminalBody) ∧
      (∀ members, terminalExpression ≠ Syntax.union members) ∧
      Context terminalBefore terminalInputs ∧
      Reached original [] terminalExpression terminalInputs terminalBefore ∧
      SyntaxBound terminalExpression event.expression ∧
      Grows terminalAfter rawAfter ∧ Extends terminalAfter.nodes.issued rawAfter.nodes.issued ∧
      ((∃ expressions rows middle, ∃ sourceIndex outputIndex : Nat, ∃ symbol guard children,
          terminalExpression = Syntax.node expressions ∧
          buildEdges expressions terminalInputs terminalBefore = .done rows middle ∧
          run (makeNode rows) middle = (terminalRaw,terminalAfter) ∧
          (nodeEdges terminalRaw)[outputIndex]? = some row ∧
          ∃ call : RowCall expressions terminalInputs terminalBefore rows middle terminalAfter sourceIndex symbol guard children,
            call.output = row) ∨
        (∃ smart terminalBody,
          terminalExpression = Syntax.binder smart terminalBody ∧
          ∃ depth afterDepth ordinary cut entry storedBody,
            callback terminalBody terminalInputs .depth terminalBefore = .done depth afterDepth ∧
            callback terminalBody terminalInputs (.uninterned (ordinaryLevel depth)) afterDepth = .done ordinary cut ∧
            request smart depth ordinary (callback terminalBody terminalInputs) cut = .done terminalRaw terminalAfter ∧
            terminalAfter.nodeRecords (muKey depth ordinary) = some (.mu entry storedBody depth ordinary) ∧
            sourceHeap.nodeRecords (muKey depth ordinary) = some (.mu entry storedBody depth ordinary) ∧
            terminalRaw = finish smart (.mu entry storedBody depth ordinary) ∧ RowAt storedBody row ∧
            Grows terminalAfter sourceHeap ∧ Extends terminalAfter.nodes.issued sourceHeap.nodes.issued ∧
            Written original [] empty sourceHeap (muKey depth ordinary) (.mu entry storedBody depth ordinary) ∧
            Stored original [] empty sourceHeap (muKey depth ordinary) entry storedBody depth ordinary)) := by
  obtain ⟨terminalExpression,terminalInputs,terminalBefore,terminalRaw,terminalAfter,
    source,done,kind,nonunion,terminalContext,terminalReached,bound,suffix,suffixIssued⟩ := terminal
  refine ⟨terminalExpression,terminalInputs,terminalBefore,terminalRaw,terminalAfter,
    source,done,kind,nonunion,terminalContext,terminalReached,bound,suffix,suffixIssued,?_⟩
  rcases kind with ⟨expressions,rfl⟩ | ⟨smart,terminalBody,rfl⟩
  · cases source with
    | @node expressions inputs before raw after rows middle symbol guard children row sourceIndex outputIndex
        builtRows made selected call same =>
      exact .inl ⟨_,_,_,_,_,_,_,_,rfl,builtRows,made,selected,call,same⟩
  · exact .inr ⟨smart,terminalBody,rfl,
      SourceCurrentNativeOriginalBinderResume.resume original sourceRoot sourceHeap sourceBuilt
        event raw rawAfter context built filtered growth issued smart terminalBody terminalInputs
        terminalBefore terminalRaw terminalAfter row source suffix suffixIssued⟩

/-- One observed original writer retains actual node calls or selected binder writers for every source row. -/
theorem of_observed (original : Syntax Symbol Guard) (sourceRoot : Node) (sourceHeap : Heap)
    (sourceBuilt : build original [] empty = .done sourceRoot sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Node) (current : Heap)
    (observed : Observed original [] empty sourceHeap key entry body depth ordinary current) :
    ∃ event : @Publication Symbol Guard _,
      Reached original [] (.binder event.smart event.expression) event.environment event.before ∧
      key = event.key ∧ entry = event.entry ∧ body = event.body ∧ depth = event.depth ∧ ordinary = event.ordinary ∧
      event.afterBody.nodeRecords event.key = none ∧
      Nonempty (Path empty event.before) ∧
      Nonempty (Path event.before event.afterDepth) ∧
      Nonempty (Path event.afterDepth event.cut) ∧
      Nonempty (Path event.allocated event.afterBody) ∧
      Grows event.after sourceHeap ∧ Extends event.after.nodes.issued sourceHeap.nodes.issued ∧
      ∃ raw rawAfter,
        build event.expression (.reference (.interned event.entry.identity) :: event.environment)
          event.allocated = .done raw rawAfter ∧
        run (withoutSelfReference (.interned event.entry.identity) raw) rawAfter = (event.body,event.afterBody) ∧
        Context event.allocated (.reference (.interned event.entry.identity) :: event.environment) ∧
        Reached original [] event.expression (.reference (.interned event.entry.identity) :: event.environment)
          event.allocated ∧
        (∀ row, RowAt body row → RowAt raw row ∧
          SourceRow event.expression (.reference (.interned event.entry.identity) :: event.environment)
            event.allocated raw rawAfter row ∧
          ∃ terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter,
      SourceRow terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter row ∧
      build terminalExpression terminalInputs terminalBefore = .done terminalRaw terminalAfter ∧
      ((∃ expressions, terminalExpression = Syntax.node expressions) ∨
        ∃ smart terminalBody, terminalExpression = Syntax.binder smart terminalBody) ∧
      (∀ members, terminalExpression ≠ Syntax.union members) ∧
      Context terminalBefore terminalInputs ∧
      Reached original [] terminalExpression terminalInputs terminalBefore ∧
      SyntaxBound terminalExpression event.expression ∧
      Grows terminalAfter rawAfter ∧ Extends terminalAfter.nodes.issued rawAfter.nodes.issued ∧
      ((∃ expressions rows middle, ∃ sourceIndex outputIndex : Nat, ∃ symbol guard children,
          terminalExpression = Syntax.node expressions ∧
          buildEdges expressions terminalInputs terminalBefore = .done rows middle ∧
          run (makeNode rows) middle = (terminalRaw,terminalAfter) ∧
          (nodeEdges terminalRaw)[outputIndex]? = some row ∧
          ∃ call : RowCall expressions terminalInputs terminalBefore rows middle terminalAfter sourceIndex symbol guard children,
            call.output = row) ∨
        (∃ smart terminalBody,
          terminalExpression = Syntax.binder smart terminalBody ∧
          ∃ depth afterDepth ordinary cut entry storedBody,
            callback terminalBody terminalInputs .depth terminalBefore = .done depth afterDepth ∧
            callback terminalBody terminalInputs (.uninterned (ordinaryLevel depth)) afterDepth = .done ordinary cut ∧
            request smart depth ordinary (callback terminalBody terminalInputs) cut = .done terminalRaw terminalAfter ∧
            terminalAfter.nodeRecords (muKey depth ordinary) = some (.mu entry storedBody depth ordinary) ∧
            sourceHeap.nodeRecords (muKey depth ordinary) = some (.mu entry storedBody depth ordinary) ∧
            terminalRaw = finish smart (.mu entry storedBody depth ordinary) ∧ RowAt storedBody row ∧
            Grows terminalAfter sourceHeap ∧ Extends terminalAfter.nodes.issued sourceHeap.nodes.issued ∧
            Written original [] empty sourceHeap (muKey depth ordinary) (.mu entry storedBody depth ordinary) ∧
            Stored original [] empty sourceHeap (muKey depth ordinary) entry storedBody depth ordinary))) ∧
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
              event.allocated raw rawAfter originalRow ∧
            ∃ terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter,
      SourceRow terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter originalRow ∧
      build terminalExpression terminalInputs terminalBefore = .done terminalRaw terminalAfter ∧
      ((∃ expressions, terminalExpression = Syntax.node expressions) ∨
        ∃ smart terminalBody, terminalExpression = Syntax.binder smart terminalBody) ∧
      (∀ members, terminalExpression ≠ Syntax.union members) ∧
      Context terminalBefore terminalInputs ∧
      Reached original [] terminalExpression terminalInputs terminalBefore ∧
      SyntaxBound terminalExpression event.expression ∧
      Grows terminalAfter rawAfter ∧ Extends terminalAfter.nodes.issued rawAfter.nodes.issued ∧
      ((∃ expressions rows middle, ∃ sourceIndex outputIndex : Nat, ∃ symbol guard children,
          terminalExpression = Syntax.node expressions ∧
          buildEdges expressions terminalInputs terminalBefore = .done rows middle ∧
          run (makeNode rows) middle = (terminalRaw,terminalAfter) ∧
          (nodeEdges terminalRaw)[outputIndex]? = some originalRow ∧
          ∃ call : RowCall expressions terminalInputs terminalBefore rows middle terminalAfter sourceIndex symbol guard children,
            call.output = originalRow) ∨
        (∃ smart terminalBody,
          terminalExpression = Syntax.binder smart terminalBody ∧
          ∃ depth afterDepth ordinary cut entry storedBody,
            callback terminalBody terminalInputs .depth terminalBefore = .done depth afterDepth ∧
            callback terminalBody terminalInputs (.uninterned (ordinaryLevel depth)) afterDepth = .done ordinary cut ∧
            request smart depth ordinary (callback terminalBody terminalInputs) cut = .done terminalRaw terminalAfter ∧
            terminalAfter.nodeRecords (muKey depth ordinary) = some (.mu entry storedBody depth ordinary) ∧
            sourceHeap.nodeRecords (muKey depth ordinary) = some (.mu entry storedBody depth ordinary) ∧
            terminalRaw = finish smart (.mu entry storedBody depth ordinary) ∧ RowAt storedBody originalRow ∧
            Grows terminalAfter sourceHeap ∧ Extends terminalAfter.nodes.issued sourceHeap.nodes.issued ∧
            Written original [] empty sourceHeap (muKey depth ordinary) (.mu entry storedBody depth ordinary) ∧
            Stored original [] empty sourceHeap (muKey depth ordinary) entry storedBody depth ordinary)) := by
  obtain ⟨event,reached,keySame,entrySame,bodySame,depthSame,ordinarySame,missing,
    earlier,depthPath,ordinaryPath,bodyPath,growth,issued,raw,rawAfter,built,filtered,context,
    callbackReached,rows,unfolds⟩ :=
    SourceCurrentNativeOriginalObservedTerminals.of_observed original empty sourceHeap
      key entry body depth ordinary current observed
  refine ⟨event,reached,keySame,entrySame,bodySame,depthSame,ordinarySame,missing,
    earlier,depthPath,ordinaryPath,bodyPath,growth,issued,raw,rawAfter,built,filtered,context,
    callbackReached,?_,?_⟩
  · intro row inside
    obtain ⟨rawRow,source,terminal⟩ := rows row inside
    exact ⟨rawRow,source,terminal_resume original sourceRoot sourceHeap sourceBuilt
      event raw rawAfter context built filtered growth issued row terminal⟩
  · intro value after actual
    obtain ⟨semanticAfter,nextGrowth,nextIssued,available,published,anchors⟩ := unfolds value after actual
    refine ⟨semanticAfter,nextGrowth,nextIssued,available,published,?_⟩
    intro row literal
    obtain ⟨originalRow,inside,symbol,guard,arity,calls,rawRow,source,terminal⟩ := anchors row literal
    exact ⟨originalRow,inside,symbol,guard,arity,calls,rawRow,source,
      terminal_resume original sourceRoot sourceHeap sourceBuilt
        event raw rawAfter context built filtered growth issued originalRow terminal⟩

end MicroCFTA.SourceCurrentNativeOriginalObservedResume
