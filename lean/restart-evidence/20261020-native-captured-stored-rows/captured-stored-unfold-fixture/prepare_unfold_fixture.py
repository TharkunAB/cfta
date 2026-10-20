from pathlib import Path
h=Path(__file__).resolve().parent
old=Path('/tmp/mcfta-native-nested-mu-row-capture-fixture/captured-row-kernels.lean').read_text()
module=Path('/tmp/mcfta-native-captured-mu-unfold-rows/SourceCurrentNativeCapturedMuUnfoldRows.lean').read_text()
s=old.split('private theorem checked_witness :',1)[0].replace('SourceCurrentNativeCapturedMuRowProduction','SourceCurrentNativeCapturedMuUnfoldRows').replace('NestedCapturedMuRowFixture','CapturedStoredUnfoldFixture')
s=s.replace('open SourceCurrentCompletedBuildRootedWriters (Written)','''open SourceCurrentCompletedBuildRootedWriters (Written)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentNativeMuIssuedHistory (Path)
open InternedFreshOrdinarySourceHistory (Reached)
open SourceCurrentStoredLiteralRowLineage (RowAt)
open SourceCurrentBuildStructuralRowOrigins (SourceRow)
open SourceCurrentStoredSubstitutionCalls (Calls)
open SourceCurrentLiteralRootParts (Row)''')
s=s.replace('# An outer optional retains its captured Mu row producers','# Actual captured Mu rows retain one source callback across unfolds').replace('Its same terminal writer supplies every selected raw row producer.','An actual unfold selects a changed row at the current heap.\nOne publication and raw callback remain fixed across its row observations.')
s+='''private def unfoldedRun := InternedFreshOrdinaryStoredSubstitution.unfold
  (.mu entry stored depth ordinary) current.native.machine.heap
private def unfolded : Node := match unfoldedRun with | .done value _ => value | .pending .. => .empty
private def unfoldedHeap : Heap := unfoldedRun.state
private def fallback : EdgeValue Symbol Guard := (run (makeEdge ("missing",.top) top []) (empty : Heap)).1
private def unfoldedRow : EdgeValue Symbol Guard := (InternedEdgeResidency.nodeEdges unfolded)[0]?.getD fallback
private def storedRow : EdgeValue Symbol Guard := (InternedEdgeResidency.nodeEdges stored)[0]?.getD fallback
private theorem actual_unfold : unfoldedRun = .done unfolded unfoldedHeap := by cbv
private theorem unfolded_selected : (InternedEdgeResidency.nodeEdges unfolded)[0]? = some unfoldedRow := by cbv
private theorem unfolded_fields : unfoldedRow.entry.key.symbol = ("rec",.top) ∧
    unfoldedRow.entry.key.constraint = top ∧ unfoldedRow.children = [.mu entry stored depth ordinary] := by
  constructor
  · cbv
  constructor <;> cbv
private theorem node_row {value : Node} {row : EdgeValue Symbol Guard}
    (selected : row ∈ InternedEdgeResidency.nodeEdges value) : Row value row := by
  cases value with
  | node => exact .node selected
  | empty | reference | union | mu => cases selected
private theorem stored_children : storedRow.children = [.reference (.interned entry.identity)] := by cbv
private theorem rows_distinct : unfoldedRow ≠ storedRow := by
  intro same
  have different : (unfoldedRow.children.map Value.referenceOf == storedRow.children.map Value.referenceOf) = false := by cbv
  rw [same] at different
  simp only [beq_self_eq_true] at different
  cases different
private theorem stored_row_unique (row : EdgeValue Symbol Guard) (inside : RowAt stored row) : row = storedRow := by
  have shape : (match stored with
    | .node _ rows _ _ => rows = [storedRow]
    | _ => False) := by cbv
  cases actual : stored with
  | node selected rows level free =>
      rw [actual] at inside shape
      cases inside with
      | node found =>
          have member := List.mem_of_getElem? found
          rw [shape] at member
          exact List.mem_singleton.mp member
  | empty | reference | union | mu => simp only [actual] at shape

'''
old_type=old.split('private theorem checked_witness :\n',1)[1].split(' := by\n',1)[0]
head,capture=old_type.split('    ∃ prefixFuel',1)
capture='    ∃ prefixFuel'+capture
head+='''    Nonempty (SourceCurrentNativeMuPublication.History empty current.native.machine.heap) ∧
    unfoldedRun = .done unfolded unfoldedHeap ∧
    (InternedEdgeResidency.nodeEdges unfolded)[0]? = some unfoldedRow ∧
    unfoldedRow.entry.key.symbol = ("rec",.top) ∧ unfoldedRow.entry.key.constraint = top ∧
    unfoldedRow.children = [.mu entry stored depth ordinary] ∧
    storedRow.children = [.reference (.interned entry.identity)] ∧ unfoldedRow ≠ storedRow ∧
'''
observed=module.split('def Observed',1)[1].split(' : Prop :=\n',1)[1].split('\n/-- Actual unfolded rows',1)[0]
observed,quantified=observed.split('      ∀ value after,',1)
quantified='      ∀ value after,'+quantified
quantified=quantified.replace('(.mu entry body depth ordinary) current =','(.mu entry stored depth ordinary) current.native.machine.heap =').replace('Grows current after','Grows current.native.machine.heap after').replace('Extends current.nodes.issued','Extends current.native.machine.heap.nodes.issued').replace('RowAt body original','RowAt stored original')
observed=observed.replace('root initial','(.binder true (encode (leaves parent) [.intersection priorPair.1 priorPair.2] parent)) (leaves parent)').replace('Path before event.before','Path siteBefore.native.machine.heap event.before').replace('key = event.key','entry.key = event.key').replace('body = event.body','stored = event.body').replace('RowAt body row','RowAt stored row').replace('Grows event.after reader','Grows event.after heap').replace('reader.nodes.issued','heap.nodes.issued')
observed+='      ('+quantified.strip()+') ∧\n'
observed+='''      RowAt stored storedRow ∧
      unfoldedRow.entry.key.symbol = storedRow.entry.key.symbol ∧
      unfoldedRow.entry.key.constraint = storedRow.entry.key.constraint ∧
      unfoldedRow.children.length = storedRow.children.length ∧
      (∃ lexical first last, Calls lexical storedRow.children first unfoldedRow.children last) ∧
      RowAt raw storedRow ∧
      SourceRow event.expression (.reference (.interned event.entry.identity) :: event.environment)
        event.allocated raw rawAfter storedRow'''
extra=''' ∧
      SourceCurrentNativeCapturedMuStoredRows.Stored
        (.binder true (encode (leaves parent) [.intersection priorPair.1 priorPair.2] parent))
        (leaves parent) siteBefore.native.machine.heap heap entry.key entry stored depth ordinary ∧
      SemanticHeap unfoldedHeap ∧ Grows current.native.machine.heap unfoldedHeap ∧
      Extends current.native.machine.heap.nodes.issued unfoldedHeap.nodes.issued ∧
      Available unfoldedHeap unfolded ∧ Nonempty (SourceCurrentNativeMuPublication.History empty unfoldedHeap) ∧
      ('''+observed.strip()+')'
type=head+capture+extra
proof=''' := by
  have rawTrace := execute_steps fuel control (.code (.optionalBinder outerPair siteBody siteNext)) before current actual_prefix
  have initial := SourceCurrentAllocatedRecursivePrefixState.initial heap inventory before good semantic_ready rfl
  have checked := SourceCurrentAllocatedRecursivePrefixAdmission.prefixes resources fuel control before
    (.code (.optionalBinder outerPair siteBody siteNext)) current (fun final output => Available final.heap output)
    initial certificate (fun _ => trivial) rawTrace
  have available : Available current.native.machine.heap siteBody := checked.inputs
  have initialPublished : SourceCurrentNativeMuPublication.History empty before.native.machine.heap :=
    SourceCurrentNativeMuPublication.closed_history expression
  have currentPublished := SourceCurrentNativePublicationTrace.source_trace expression checked.trace rfl
  rcases SourceCurrentNativeCapturedMuUnfoldRows.capture request fuel before current outerPair siteBody siteNext
      good history semantic initialPublished checked.trace available 1 entry stored depth ordinary found with prior | generated
  · change heap.nodeRecords entry.key = some (.mu entry stored depth ordinary) at prior
    rw [new_capture.1] at prior
    cases prior
  · obtain ⟨prefixFuel,suffixFuel,priorPair,parent,next,siteBefore,siteAfter,result,after,total,strict,
      earlier,siteSemantic,siteAvailable,called,advanced,one,suffix,missing,present,
      prefixGrowth,prefixIssued,suffixGrowth,suffixIssued,used,context,built,written,origin,storedCertificate,observe⟩ := generated
    obtain ⟨event,reached,keySame,entrySame,bodySame,depthSame,ordinarySame,unrecorded,
      startPath,depthPath,ordinaryPath,bodyPath,eventGrowth,eventIssued,raw,rawAfter,
      rawBuilt,filtered,callbackContext,callbackReached,storedRows,everyUnfold⟩ := observe
    obtain ⟨afterSemantic,growth,issued,outputAvailable,published,observedRows⟩ :=
      everyUnfold unfolded unfoldedHeap actual_unfold
    obtain ⟨original,inside,symbol,guard,arity,calls,rawRow,source⟩ :=
      observedRows unfoldedRow (node_row (List.mem_of_getElem? unfolded_selected))
    have same := stored_row_unique original inside
    subst original
    rcases calls with unchanged | actualCalls
    · exact False.elim (rows_distinct unchanged)
    · refine ⟨built_done,children_shape,closed.1,closed.2,operands_distinct,
        operands_used.1,operands_used.2,good,history,bounded.1,bounded.2,
        actual_prefix,checked.trace,available,found,new_capture.1,new_capture.2.1,new_capture.2.2,
        currentPublished.2,actual_unfold,unfolded_selected,unfolded_fields.1,unfolded_fields.2.1,
        unfolded_fields.2.2,stored_children,rows_distinct,prefixFuel,suffixFuel,priorPair,parent,next,
        siteBefore,siteAfter,result,after,total,strict,earlier,siteSemantic,siteAvailable,called,advanced,
        one,suffix,missing,present,prefixGrowth,prefixIssued,suffixGrowth,suffixIssued,used,context,
        built,written,origin,storedCertificate,afterSemantic,growth,issued,outputAvailable,published,
        event,reached,keySame,entrySame,bodySame,depthSame,ordinarySame,unrecorded,startPath,
        depthPath,ordinaryPath,bodyPath,eventGrowth,eventIssued,raw,rawAfter,rawBuilt,filtered,
        callbackContext,callbackReached,storedRows,everyUnfold,inside,symbol,guard,arity,actualCalls,rawRow,source⟩
'''
s+='private theorem checked_witness :\n'+type+proof
s+='\n/-- One actual captured Mu unfold retains the same callback and changed-child calls. -/\ntheorem actual_captured_unfold :\n'+type+' := checked_witness\n\nend MicroCFTA.CapturedStoredUnfoldFixture\n'
(h/'unfold-kernels.lean').write_text(s)
