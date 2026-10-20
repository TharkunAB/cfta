from pathlib import Path
import re
p=Path(__file__).resolve().parent
header=(p/'header.lean.txt').read_text()
core=(p/'generated-backedge-core-snippet.lean.txt').read_text()
done=(p/'source-done-snippet.lean.txt').read_text()
pos=header.index('open Cache')
header=header[:pos]+'''open Cache InternedConstructorTemplates
open InternedNestedConstruction (Syntax Outcome work request)
open InternedFreshOrdinaryConstruction (build ordinaryLevel)
open InternedFreshOrdinaryFacts (callback)
open SourceCurrentBuildStructuralRowOrigins (SourceRow)
section SourceDone
variable {Symbol Guard : Type}

'''+done+'''\nend SourceDone

'''+header[pos:]
terminal=core[core.index('    ∃ terminalExpression',core.index('private theorem generated_terminal')):core.index(' := by\n',core.index('private theorem generated_terminal'))]
terminal=terminal.replace('SourceRow terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter fullRow ∧',
'''SourceRow terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter fullRow ∧
      build terminalExpression terminalInputs terminalBefore = .done terminalRaw terminalAfter ∧''',1)
terminal=terminal.replace('targetKey','targetEntry.key')
terminal=terminal.replace('SyntaxBound terminalExpression expression','SyntaxBound terminalExpression event.expression')
terminal=terminal.replace('Grows terminalAfter stop','Grows terminalAfter rawAfter').replace('stop.nodes.issued','rawAfter.nodes.issued')
(p/'terminal-result.lean.txt').write_text(terminal)
def terminal_for(row):return re.sub(r'\bfullRow\b',row,terminal)
public='''/-- An executed generated callback row retains its exact capture and an earlier native producer. -/
theorem generated_row_capture_backedge (original : Syntax Symbol Guard) (sourceRoot : Node)
    (request : NodeRequest Symbol Guard) (fuel : Nat) (before current : Checked width)
    (pair : Nat × Nat) (siteBody : Node) (siteNext : Node → Code Symbol Guard Node)
    (sourceBuild : build original [] empty = .done sourceRoot before.native.machine.heap)
    (good : Good before) (history : History before)
    (actual : Trace fuel (.code (requestNode request.domain request.left request.right)) before
      (.code (.optionalBinder pair siteBody siteNext)) current)
    (available : Available current.native.machine.heap siteBody)
    (result : Node) (generatedHeap : Heap)
    (executed : SourceRecursiveIntersectionMaybeMu.maybeMu pair siteBody current.native.machine.heap = .done result generatedHeap)
    (generatedBuild : build (.binder true (encode (leaves siteBody) [.intersection pair.1 pair.2] siteBody))
      (leaves siteBody) current.native.machine.heap = .done result generatedHeap)
    (targetEntry : Interned NodeKey) (targetBody targetDepth targetOrdinary : Node)
    (targetMissing : current.native.machine.heap.nodeRecords targetEntry.key = none)
    (targetSelected : generatedHeap.nodeRecords targetEntry.key =
      some (.mu targetEntry targetBody targetDepth targetOrdinary))
    (reader : Heap)
    (observed : Observed (.binder true (encode (leaves siteBody) [.intersection pair.1 pair.2] siteBody))
      (leaves siteBody) current.native.machine.heap generatedHeap targetEntry.key
      targetEntry targetBody targetDepth targetOrdinary reader) :
    SourceRecursiveIntersectionMaybeMu.maybeMu pair siteBody current.native.machine.heap = .done result generatedHeap ∧
    build (.binder true (encode (leaves siteBody) [.intersection pair.1 pair.2] siteBody))
      (leaves siteBody) current.native.machine.heap = .done result generatedHeap ∧
    current.native.machine.heap.nodeRecords targetEntry.key = none ∧
    generatedHeap.nodeRecords targetEntry.key = some (.mu targetEntry targetBody targetDepth targetOrdinary) ∧
    ∃ event : @Publication Symbol Guard _,
      Reached (.binder true (encode (leaves siteBody) [.intersection pair.1 pair.2] siteBody))
        (leaves siteBody) (.binder event.smart event.expression) event.environment event.before ∧
      targetEntry.key = event.key ∧ targetEntry = event.entry ∧ targetBody = event.body ∧
      targetDepth = event.depth ∧ targetOrdinary = event.ordinary ∧
      event.afterBody.nodeRecords event.key = none ∧
      Nonempty (Path current.native.machine.heap event.before) ∧
      Nonempty (Path event.before event.afterDepth) ∧
      Nonempty (Path event.afterDepth event.cut) ∧
      Nonempty (Path event.allocated event.afterBody) ∧
      Grows event.after generatedHeap ∧ Extends event.after.nodes.issued generatedHeap.nodes.issued ∧
      ∃ raw rawAfter,
        build event.expression (.reference (.interned event.entry.identity) :: event.environment)
          event.allocated = .done raw rawAfter ∧
        run (withoutSelfReference (.interned event.entry.identity) raw) rawAfter = (event.body,event.afterBody) ∧
        Context event.allocated (.reference (.interned event.entry.identity) :: event.environment) ∧
        Reached (.binder true (encode (leaves siteBody) [.intersection pair.1 pair.2] siteBody))
          (leaves siteBody) event.expression (.reference (.interned event.entry.identity) :: event.environment)
          event.allocated ∧
        (∀ storedRow, RowAt targetBody storedRow → RowAt raw storedRow ∧
          SourceRow event.expression (.reference (.interned event.entry.identity) :: event.environment)
            event.allocated raw rawAfter storedRow ∧
'''+terminal_for('storedRow')+''') ∧
        ∀ value after,
          InternedFreshOrdinaryStoredSubstitution.unfold (.mu targetEntry targetBody targetDepth targetOrdinary)
            reader = .done value after →
          SemanticHeap after ∧ Grows reader after ∧ Extends reader.nodes.issued after.nodes.issued ∧
          Available after value ∧ Nonempty (SourceCurrentNativeMuPublication.History empty after) ∧
          ∀ row, Row value row →
          ∃ originalRow, RowAt targetBody originalRow ∧
            row.entry.key.symbol = originalRow.entry.key.symbol ∧
            row.entry.key.constraint = originalRow.entry.key.constraint ∧
            row.children.length = originalRow.children.length ∧
            (row = originalRow ∨ ∃ lexical current next, Calls lexical originalRow.children current row.children next) ∧
            RowAt raw originalRow ∧
            SourceRow event.expression (.reference (.interned event.entry.identity) :: event.environment)
              event.allocated raw rawAfter originalRow ∧
'''+terminal_for('originalRow')+''' := by
  obtain ⟨event,reached,keySame,entrySame,bodySame,depthSame,ordinarySame,missing,
    prefixPath,depthPath,ordinaryPath,bodyPath,growth,issued,raw,rawAfter,built,filtered,
    context,callbackReached,rows,unfolds⟩ := observed
  refine ⟨executed,generatedBuild,targetMissing,targetSelected,event,reached,
    keySame,entrySame,bodySame,depthSame,ordinarySame,missing,prefixPath,depthPath,ordinaryPath,
    bodyPath,growth,issued,raw,rawAfter,built,filtered,context,callbackReached,?_,?_⟩
  · intro storedRow inside
    obtain ⟨rawRow,source⟩ := rows storedRow inside
    obtain ⟨terminalExpression,terminalInputs,terminalBefore,terminalRaw,terminalAfter,
      terminalSource,nonunion,terminalContext,terminalReached,bound,suffix,suffixIssued,classification⟩ :=
      generated_terminal original sourceRoot request fuel before current pair siteBody siteNext
        sourceBuild good history actual available targetEntry.key targetMissing event.expression
        (.reference (.interned event.entry.identity) :: event.environment) event.allocated raw rawAfter
        storedRow context callbackReached source
    exact ⟨rawRow,source,terminalExpression,terminalInputs,terminalBefore,terminalRaw,terminalAfter,
      terminalSource,source_done terminalSource,nonunion,terminalContext,terminalReached,bound,
      suffix,suffixIssued,classification⟩
  · intro value after actualUnfold
    obtain ⟨semanticAfter,unfoldGrowth,unfoldIssued,outputAvailable,publications,anchors⟩ :=
      unfolds value after actualUnfold
    refine ⟨semanticAfter,unfoldGrowth,unfoldIssued,outputAvailable,publications,?_⟩
    intro row literal
    obtain ⟨originalRow,originalInside,symbol,guard,arity,calls,rawRow,source⟩ := anchors row literal
    obtain ⟨terminalExpression,terminalInputs,terminalBefore,terminalRaw,terminalAfter,
      terminalSource,nonunion,terminalContext,terminalReached,bound,suffix,suffixIssued,classification⟩ :=
      generated_terminal original sourceRoot request fuel before current pair siteBody siteNext
        sourceBuild good history actual available targetEntry.key targetMissing event.expression
        (.reference (.interned event.entry.identity) :: event.environment) event.allocated raw rawAfter
        originalRow context callbackReached source
    exact ⟨originalRow,originalInside,symbol,guard,arity,calls,rawRow,source,
      terminalExpression,terminalInputs,terminalBefore,terminalRaw,terminalAfter,
      terminalSource,source_done terminalSource,nonunion,terminalContext,terminalReached,bound,
      suffix,suffixIssued,classification⟩
'''
(p/'public-producer.lean.txt').write_text(public)
(p/'SourceCurrentNativeGeneratedRowCaptureBackedge.lean').write_text(header+core+'\n'+public+'\nend MicroCFTA.SourceCurrentNativeGeneratedRowCaptureBackedge\n')
