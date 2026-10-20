from pathlib import Path
p=Path(__file__).resolve().parent
origin='''∃ producerIndex : Nat, ∃ producer : @Publication Symbol Guard _,
        ∃ expressions inputs before raw after rows middle,
        ∃ sourceIndex outputIndex : Nat, ∃ symbol guard children,
          producerIndex ≤ index ∧ (events path)[producerIndex]? = some producer ∧
          SyntaxBound (Syntax.node expressions) producer.expression ∧
          UnionDescent producer.expression (Syntax.node expressions) ∧
          Context before inputs ∧ Reached original [] (Syntax.node expressions) inputs before ∧
          SourceRow (Syntax.node expressions) inputs before raw after row ∧
          build (Syntax.node expressions) inputs before = .done raw after ∧
          buildEdges expressions inputs before = .done rows middle ∧
          run (makeNode rows) middle = (raw,after) ∧
          (nodeEdges raw)[outputIndex]? = some row ∧
          ∃ call : RowCall expressions inputs before rows middle after sourceIndex symbol guard children,
            call.output = row ∧ Grows after outer.afterBody ∧
            Extends after.nodes.issued outer.afterBody.nodes.issued'''
source='''import MicroCFTA.SourceCurrentNativeOriginalIndexedResumption
import MicroCFTA.SourceCurrentNativeMuGrowthHistory

/-!
# Ultimate original node production for stored rows

One completed source build fixes one publication trace.
A binder stop resumes at a strictly earlier index in that trace.
Each full stored row reaches an actual original node call.
-/
namespace MicroCFTA.SourceCurrentNativeOriginalNodeRowOrigins
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build buildEdges)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentNativeMuIssuedHistory (Path)
open SourceCurrentNativeOriginalPublicationTrace (events)
open InternedFreshOrdinarySourceHistory (Reached)
open SourceCurrentStoredLiteralRowLineage (RowAt)
open SourceCurrentBuildStructuralRowOrigins (SourceRow)
open SourceCurrentStoredMuRetainedAlignment (RowCall)
open SourceCurrentNativeOriginalUnionDescent (UnionDescent)
open SourceCurrentNativeOriginalObservedResume (SyntaxBound)
open InternedEdgeResidency (nodeEdges)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Every stored row in one original source trace has an actual node producer in that same trace. -/
theorem build_node_row_origins (original : Syntax Symbol Guard) (sourceRoot : Node) (sourceHeap : Heap)
    (sourceBuilt : build original [] empty = .done sourceRoot sourceHeap) :
    ∃ path : Path empty sourceHeap,
      (∀ (index : Nat) event, (events path)[index]? = some event →
        Reached original [] (.binder event.smart event.expression) event.environment event.before) ∧
      (∀ key entry body depth ordinary,
        sourceHeap.nodeRecords key = some (.mu entry body depth ordinary) →
        ∃ index : Nat, ∃ event, (events path)[index]? = some event ∧
          Reached original [] (.binder event.smart event.expression) event.environment event.before ∧
          key = event.key ∧ Value.mu entry body depth ordinary = event.candidate ∧
          event.afterBody.nodeRecords event.key = none ∧
          Nonempty (Path empty event.before) ∧
          Nonempty (Path event.before event.afterDepth) ∧
          Nonempty (Path event.afterDepth event.cut) ∧
          Nonempty (Path event.allocated event.afterBody) ∧
          Grows event.after sourceHeap ∧ Extends event.after.nodes.issued sourceHeap.nodes.issued) ∧
      ∀ (index : Nat) outer, (events path)[index]? = some outer →
        ∀ row, RowAt outer.body row →
      '''+origin+''' := by
  obtain ⟨path,sites,finalWriters,_precompletion,resumptions⟩ :=
    SourceCurrentNativeOriginalIndexedResumption.build_row_resumptions original sourceRoot sourceHeap sourceBuilt
  have origins : ∀ (index : Nat) (outer : @Publication Symbol Guard _),
      (events path)[index]? = some outer → ∀ row, RowAt outer.body row →
      '''+origin+''' := by
    intro index
    induction index using Nat.strongRecOn with
    | ind index ih =>
      intro outer selectedOuter row inside
      obtain ⟨raw,rawAfter,built,filtered,context,_callbackReached,rows⟩ :=
        resumptions index outer selectedOuter
      obtain ⟨_rawRow,_rawSource,terminalExpression,terminalInputs,terminalBefore,terminalRaw,terminalAfter,
        terminalSource,terminalDone,_kind,_nonunion,terminalContext,terminalReached,bound,descent,
        suffix,suffixIssued,choice⟩ := rows row inside
      rcases choice with nodeFacts | binderFacts
      · obtain ⟨expressions,nodeRows,middle,sourceIndex,outputIndex,symbol,guard,children,
          same,builtRows,made,canonical,call,callSame⟩ := nodeFacts
        subst terminalExpression
        have returnedContext : Context rawAfter
            (.reference (.interned outer.entry.identity) :: outer.environment) := by
          simpa only [built,Outcome.state] using context.build outer.expression
        have filterGrowth := (run_correct (withoutSelfReference (.interned outer.entry.identity) raw)
          rawAfter returnedContext.base.normal.facts.coherent.valid).2
        have filterIssued := run_issued_extends (withoutSelfReference (.interned outer.entry.identity) raw)
          rawAfter returnedContext.base.normal.facts.coherent.valid
        rw [filtered] at filterGrowth filterIssued
        exact ⟨index,outer,expressions,terminalInputs,terminalBefore,terminalRaw,terminalAfter,
          nodeRows,middle,sourceIndex,outputIndex,symbol,guard,children,Nat.le_refl _,selectedOuter,
          bound,descent,terminalContext,terminalReached,terminalSource,terminalDone,builtRows,made,
          canonical,call,callSame,grows_trans suffix filterGrowth,extends_trans suffixIssued filterIssued⟩
      · obtain ⟨smart,terminalBody,_same,depth,afterDepth,ordinary,cut,entry,storedBody,
          _depthDone,_ordinaryDone,_requested,_present,_presentBefore,_returned,storedInside,
          _beforeGrowth,_beforeIssued,earlierIndex,earlier,less,selectedEarlier,_earlierReached,
          _keySame,valueSame,_missing,_prefixPath,_depthPath,_ordinaryPath,_bodyPath,
          earlierGrowth,earlierIssued,_earlierCallback⟩ := binderFacts
        have bodySame : storedBody = earlier.body := (Value.mu.inj valueSame).2.1
        obtain ⟨producerIndex,producer,expressions,inputs,before,value,after,nodeRows,middle,
          sourceIndex,outputIndex,symbol,guard,children,producerBound,producerLookup,nodeBound,
          nodeDescent,nodeContext,nodeReached,nodeSource,nodeDone,builtRows,made,canonical,call,
          callSame,nodeGrowth,nodeIssued⟩ :=
          ih earlierIndex less earlier selectedEarlier row (bodySame ▸ storedInside)
        have completionIssued : Extends earlier.afterBody.nodes.issued earlier.after.nodes.issued := by
          change Extends earlier.afterBody.nodes.issued earlier.afterBody.nodes.issued
          exact extends_refl _
        exact ⟨producerIndex,producer,expressions,inputs,before,value,after,nodeRows,middle,
          sourceIndex,outputIndex,symbol,guard,children,
          Nat.le_trans producerBound (Nat.le_of_lt less),producerLookup,nodeBound,nodeDescent,
          nodeContext,nodeReached,nodeSource,nodeDone,builtRows,made,canonical,call,callSame,
          grows_trans nodeGrowth
            (grows_trans (SourceCurrentNativeMuGrowthHistory.publication_growth earlier) earlierGrowth),
          extends_trans nodeIssued (extends_trans completionIssued earlierIssued)⟩
  exact ⟨path,sites,finalWriters,origins⟩

end MicroCFTA.SourceCurrentNativeOriginalNodeRowOrigins
'''
(p/'SourceCurrentNativeOriginalNodeRowOrigins.lean').write_text(source)
(p/'node-origin-result.lean.txt').write_text(origin)
