from pathlib import Path
import re
p=Path(__file__).resolve().parent
snippet=(p/'captured-unfold-node-snippet.lean.txt').read_text()
header=(p/'header.lean.txt').read_text()
generated=(p/'generated-branch.lean.txt').read_text()
node=re.sub(r'\brow\b','storedRow',(p/'node-origin-result.lean.txt').read_text()).replace('producerIndex ≤ index','producerIndex ≤ outerIndex')
core_result=snippet[snippet.index('    SemanticHeap current.native.machine.heap ∧'):snippet.index(' := by\n')]
selector='''∀ key selectedEntry selectedBody selectedDepth selectedOrdinary,
          before.native.machine.heap.nodeRecords key = some (.mu selectedEntry selectedBody selectedDepth selectedOrdinary) →
          ∃ index : Nat, ∃ event, (events path)[index]? = some event ∧
            Reached original [] (.binder event.smart event.expression) event.environment event.before ∧
            key = event.key ∧ Value.mu selectedEntry selectedBody selectedDepth selectedOrdinary = event.candidate ∧
            event.afterBody.nodeRecords event.key = none ∧
            Nonempty (Path empty event.before) ∧
            Nonempty (Path event.before event.afterDepth) ∧
            Nonempty (Path event.afterDepth event.cut) ∧
            Nonempty (Path event.allocated event.afterBody) ∧
            Grows event.after before.native.machine.heap ∧
            Extends event.after.nodes.issued before.native.machine.heap.nodes.issued'''
public='''/-- An actual captured initial Mu retains indexed original node calls for its stored and unfolded rows. -/
theorem capture_node_rows (original : Syntax Symbol Guard) (sourceRoot : Node)
    (request : NodeRequest Symbol Guard) (fuel : Nat) (before current : Checked width)
    (pair : Nat × Nat) (siteBody : Node) (siteNext : Node → Code Symbol Guard Node)
    (sourceBuild : build original [] empty = .done sourceRoot before.native.machine.heap)
    (good : Good before) (history : History before)
    (actual : Trace fuel (.code (requestNode request.domain request.left request.right)) before
      (.code (.optionalBinder pair siteBody siteNext)) current)
    (available : Available current.native.machine.heap siteBody)
    (index : Nat) (entry : Interned NodeKey) (body depth ordinary : Node)
    (found : (leaves siteBody)[index]? = some (.mu entry body depth ordinary)) :
    (before.native.machine.heap.nodeRecords entry.key = some (.mu entry body depth ordinary) ∧
      ∃ path : Path empty before.native.machine.heap,
        (∀ (index : Nat) event, (events path)[index]? = some event →
          Reached original [] (.binder event.smart event.expression) event.environment event.before) ∧
        ('''+selector+''') ∧
        ∃ outerIndex : Nat, ∃ outer : @Publication Symbol Guard _,
          (events path)[outerIndex]? = some outer ∧
          Reached original [] (.binder outer.smart outer.expression) outer.environment outer.before ∧
          entry.key = outer.key ∧ Value.mu entry body depth ordinary = outer.candidate ∧
          entry = outer.entry ∧ body = outer.body ∧ depth = outer.depth ∧ ordinary = outer.ordinary ∧
          outer.afterBody.nodeRecords outer.key = none ∧
          Nonempty (Path empty outer.before) ∧
          Nonempty (Path outer.before outer.afterDepth) ∧
          Nonempty (Path outer.afterDepth outer.cut) ∧
          Nonempty (Path outer.allocated outer.afterBody) ∧
          Grows outer.after before.native.machine.heap ∧
          Extends outer.after.nodes.issued before.native.machine.heap.nodes.issued ∧
          (∀ storedRow, RowAt body storedRow →
            '''+node+''') ∧
'''+core_result+''') ∨
'''+generated+''' := by
  have semantic := SourceRecursiveIntersectionSemanticHeap.constructed original sourceRoot before.native.machine.heap sourceBuild
  have publications : SourceCurrentNativeMuPublication.History empty before.native.machine.heap := by
    simpa only [sourceBuild,InternedNestedConstruction.Outcome.state] using SourceCurrentNativeMuPublication.closed_history original
  rcases SourceCurrentNativeCapturedMuUnfoldRows.capture request fuel before current pair siteBody siteNext
      good history semantic publications actual available index entry body depth ordinary found with prior | generated
  · obtain ⟨path,sites,finalWriters,origins⟩ :=
      SourceCurrentNativeOriginalNodeRowOrigins.build_node_row_origins original sourceRoot before.native.machine.heap sourceBuild
    obtain ⟨outerIndex,outer,selectedOuter,rooted,keySame,valueSame,missing,prefixPath,
      depthPath,ordinaryPath,bodyPath,growth,issued⟩ :=
      finalWriters entry.key entry body depth ordinary prior
    obtain ⟨entrySame,bodySame,depthSame,ordinarySame⟩ := Value.mu.inj valueSame
    refine .inl ⟨prior,path,sites,finalWriters,outerIndex,outer,selectedOuter,rooted,keySame,valueSame,
      entrySame,bodySame,depthSame,ordinarySame,missing,prefixPath,depthPath,ordinaryPath,bodyPath,growth,issued,?_,?_⟩
    · intro storedRow inside
      exact origins outerIndex outer selectedOuter storedRow (bodySame ▸ inside)
    · exact captured_unfold_nodes original sourceRoot request fuel before current pair siteBody siteNext
        sourceBuild actual available index entry body depth ordinary found path outerIndex outer
        selectedOuter bodySame origins
  · exact .inr generated

end MicroCFTA.SourceCurrentNativeOriginalCapturedNodeRows
'''
(p/'public-producer.lean.txt').write_text(public)
(p/'SourceCurrentNativeOriginalCapturedNodeRows.lean').write_text(header+snippet+'\n'+public)
