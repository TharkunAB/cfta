from pathlib import Path
h=Path(__file__).resolve().parent
s=(h/'original-kernels.lean').read_text().split('end MicroCFTA.OriginalCapturedMuFixture',1)[0]
s+='''private def outerRow (value : Node) : EdgeValue Symbol Guard :=
  ((InternedEdgeResidency.nodeEdges (body value)).find? (fun row => row.entry.key.symbol == ("outer",.top))).getD fallback
private theorem shared_capture : (outerRow left).children[1]? = some (.mu entry stored depth ordinary) ∧
    (outerRow right).children[1]? = some (.mu entry stored depth ordinary) := by constructor <;> cbv

'''
old=Path('/tmp/mcfta-native-captured-stored-unfold-fixture/unfold-kernels.lean').read_text()
head=old.split('private theorem checked_witness :\n',1)[1].split('    ∃ prefixFuel',1)[0]
head=head.replace('heap.nodeRecords entry.key = none','heap.nodeRecords entry.key = some (.mu entry stored depth ordinary)').replace('(InternedEdgeResidency.nodeEdges unfolded)[0]?','(InternedEdgeResidency.nodeEdges unfolded)[unfoldedIndex]?')
head+='''    (outerRow left).children[1]? = some (.mu entry stored depth ordinary) ∧
    (outerRow right).children[1]? = some (.mu entry stored depth ordinary) ∧
    SemanticHeap unfoldedHeap ∧ Grows current.native.machine.heap unfoldedHeap ∧
    Extends current.native.machine.heap.nodes.issued unfoldedHeap.nodes.issued ∧
    Available unfoldedHeap unfolded ∧ Nonempty (SourceCurrentNativeMuPublication.History empty unfoldedHeap) ∧
'''
module=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceCurrentNativeCapturedMuUnfoldRows.lean').read_text()
observed=module.split('def Observed',1)[1].split(' : Prop :=\n',1)[1].split('\n/-- Actual unfolded rows',1)[0]
observed,quantified=observed.split('      ∀ value after,',1)
quantified='      ∀ value after,'+quantified
quantified=quantified.replace('(.mu entry body depth ordinary) current =','(.mu entry stored depth ordinary) current.native.machine.heap =').replace('Grows current after','Grows current.native.machine.heap after').replace('Extends current.nodes.issued','Extends current.native.machine.heap.nodes.issued').replace('RowAt body original','RowAt stored original')
observed=observed.replace('root initial','expression []').replace('Path before event.before','Path empty event.before').replace('key = event.key','entry.key = event.key').replace('body = event.body','stored = event.body').replace('RowAt body row','RowAt stored row').replace('Grows event.after reader','Grows event.after heap').replace('reader.nodes.issued','heap.nodes.issued')
observed+='      ('+quantified.strip()+') ∧\n'
observed+='''      RowAt stored storedRow ∧
      unfoldedRow.entry.key.symbol = storedRow.entry.key.symbol ∧
      unfoldedRow.entry.key.constraint = storedRow.entry.key.constraint ∧
      unfoldedRow.children.length = storedRow.children.length ∧
      (∃ lexical first last, Calls lexical storedRow.children first unfoldedRow.children last) ∧
      RowAt raw storedRow ∧
      SourceRow event.expression (.reference (.interned event.entry.identity) :: event.environment)
        event.allocated raw rawAfter storedRow'''
type=head+'      ('+observed.strip()+')'
proof=''' := by
  have rawTrace := execute_steps fuel control (.code (.optionalBinder outerPair siteBody siteNext)) before current actual_prefix
  have initial := SourceCurrentAllocatedRecursivePrefixState.initial heap inventory before good semantic_ready rfl
  have checked := SourceCurrentAllocatedRecursivePrefixAdmission.prefixes resources fuel control before
    (.code (.optionalBinder outerPair siteBody siteNext)) current (fun final output => Available final.heap output)
    initial certificate (fun _ => trivial) rawTrace
  have available : Available current.native.machine.heap siteBody := checked.inputs
  have currentPublished := SourceCurrentNativePublicationTrace.source_trace expression checked.trace rfl
  rcases SourceCurrentNativeOriginalCapturedMuRows.capture_source expression root request fuel before current
      outerPair siteBody siteNext built_done good history checked.trace available 1 entry stored depth ordinary found
      with capturedInitial | generated
  · obtain ⟨prior,observed⟩ := capturedInitial
    obtain ⟨event,reached,keySame,entrySame,bodySame,depthSame,ordinarySame,unrecorded,
      startPath,depthPath,ordinaryPath,bodyPath,eventGrowth,eventIssued,raw,rawAfter,
      rawBuilt,filtered,callbackContext,callbackReached,storedRows,everyUnfold⟩ := observed
    obtain ⟨afterSemantic,growth,issued,outputAvailable,published,observedRows⟩ :=
      everyUnfold unfolded unfoldedHeap actual_unfold
    obtain ⟨original,inside,symbol,guard,arity,calls,rawRow,source⟩ :=
      observedRows unfoldedRow (node_row (List.mem_of_getElem? unfolded_selected))
    have same := stored_rec_unique original inside (symbol.symm.trans unfolded_fields.1)
    subst original
    rcases calls with unchanged | actualCalls
    · exact False.elim (rows_distinct unchanged)
    · exact ⟨built_done,children_shape,closed.1,closed.2,operands_distinct,
        operands_used.1,operands_used.2,good,history,bounded.1,bounded.2,
        actual_prefix,checked.trace,available,found,prior,initial_capture.2.1,initial_capture.2.2,
        currentPublished.2,actual_unfold,unfolded_selected,unfolded_fields.1,unfolded_fields.2.1,
        unfolded_fields.2.2,stored_children,rows_distinct,shared_capture.1,shared_capture.2,
        afterSemantic,growth,issued,outputAvailable,published,
        event,reached,keySame,entrySame,bodySame,depthSame,ordinarySame,unrecorded,startPath,
        depthPath,ordinaryPath,bodyPath,eventGrowth,eventIssued,raw,rawAfter,rawBuilt,filtered,
        callbackContext,callbackReached,storedRows,everyUnfold,inside,symbol,guard,arity,actualCalls,rawRow,source⟩
  · obtain ⟨prefixFuel,suffixFuel,priorPair,parent,next,siteBefore,siteAfter,result,after,total,strict,
      earlier,siteSemantic,siteAvailable,called,advanced,one,suffix,missing,present,
      prefixGrowth,prefixIssued,suffixGrowth,suffixIssued,used,context,built,written,origin,storedCertificate,observe⟩ := generated
    have retained := prefixGrowth.nodeRecords entry.key (.mu entry stored depth ordinary) initial_capture.1
    rw [missing] at retained
    cases retained
'''
s+='private theorem checked_witness :\n'+type+proof
s+='\n/-- An actual initial Mu capture retains its original source and changed unfold child calls. -/\ntheorem actual_initial_capture :\n'+type+' := checked_witness\n\nend MicroCFTA.OriginalCapturedMuFixture\n'
(h/'original-kernels.lean').write_text(s)
