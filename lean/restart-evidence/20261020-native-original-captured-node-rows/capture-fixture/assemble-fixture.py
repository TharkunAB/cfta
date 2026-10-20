from pathlib import Path
import re
h=Path(__file__).resolve().parent
s=(h/'captured-node-rows-kernels.lean').read_text().split('-- The fixed capture API',1)[0]
s=s.replace('open InternedNestedConstruction (Syntax)','open InternedNestedConstruction (Syntax)\nopen InternedFreshOrdinaryConstruction (build buildEdges)\nopen InternedEdgeResidency (nodeEdges)\nopen SourceCurrentNativeOriginalPublicationTrace (events)\nopen SourceCurrentStoredMuRetainedAlignment (RowCall)\nopen SourceCurrentNativeOriginalUnionDescent (UnionDescent)\nopen SourceCurrentNativeOriginalObservedResume (SyntaxBound)')
api=Path('/tmp/mcfta-native-original-captured-node-rows/SourceCurrentNativeOriginalCapturedNodeRows.lean').read_text().split('theorem capture_node_rows',1)[1]
start=api.index('    (before.native.machine.heap.nodeRecords')+len('    (')
end=api.index(') ∨\n    ∃ prefixFuel',start)
initial='    '+api[start:end]
initial=re.sub(r'(?<![\w.])original\b','expression',initial)
initial=re.sub(r'(?<![\w.])body\b','stored',initial)
marker='              ∃ producerIndex : Nat, ∃ producer : @Publication Symbol Guard _,'
node=initial[initial.rindex(marker):]
actual_forall='      ∀ value after,\n        InternedFreshOrdinaryStoredSubstitution.unfold'
assert initial.count(actual_forall)==1
initial=initial.replace(actual_forall,actual_forall.replace('      ∀','      (∀',1))+') ∧\n'
old=Path('/tmp/mcfta-native-original-terminal-fixture/terminal-kernels.lean').read_text()
base=old.split('private theorem checked_witness :\n',1)[1].split('      (∃ event : @Publication',1)[0]
concrete='''      RowAt stored storedRow ∧
      unfoldedRow.entry.key.symbol = storedRow.entry.key.symbol ∧
      unfoldedRow.entry.key.constraint = storedRow.entry.key.constraint ∧
      unfoldedRow.children.length = storedRow.children.length ∧
      (∃ lexical start finish, Calls lexical storedRow.children start unfoldedRow.children finish) ∧
'''+node
claim=base+initial+concrete
proof='''  have rawTrace := execute_steps fuel control (.code (.optionalBinder outerPair siteBody siteNext)) before current actual_prefix
  have initial := SourceCurrentAllocatedRecursivePrefixState.initial heap inventory before good semantic_ready rfl
  have checked := SourceCurrentAllocatedRecursivePrefixAdmission.prefixes resources fuel control before
    (.code (.optionalBinder outerPair siteBody siteNext)) current (fun final output => Available final.heap output)
    initial certificate (fun _ => trivial) rawTrace
  have available : Available current.native.machine.heap siteBody := checked.inputs
  rcases SourceCurrentNativeOriginalCapturedNodeRows.capture_node_rows expression root request fuel before current
      outerPair siteBody siteNext built_done good history checked.trace available 1 entry stored depth ordinary found
      with capturedInitial | generated
  · obtain ⟨prior,path,sites,finalWriters,outerIndex,outer,selectedOuter,rooted,keySame,valueSame,
      entrySame,bodySame,depthSame,ordinarySame,missing,startPath,depthPath,ordinaryPath,bodyPath,
      eventGrowth,eventIssued,storedNodes,currentSemantic,capturedAvailable,currentPublished,everyUnfold⟩ := capturedInitial
    obtain ⟨afterSemantic,growth,issued,outputAvailable,published,observedRows⟩ :=
      everyUnfold unfolded unfoldedHeap actual_unfold
    obtain ⟨original,inside,symbol,guard,arity,calls,nodeFacts⟩ :=
      observedRows unfoldedRow (node_row (List.mem_of_getElem? unfolded_selected))
    have same := stored_rec_unique original inside (symbol.symm.trans unfolded_fields.1)
    subst original
    rcases calls with unchanged | actualCalls
    · exact False.elim (rows_distinct unchanged)
    · exact ⟨built_done,children_shape,closed.1,closed.2,operands_distinct,
        operands_used.1,operands_used.2,good,history,bounded.1,bounded.2,
        actual_prefix,checked.trace,available,found,prior,initial_capture.2.1,initial_capture.2.2,
        currentPublished,actual_unfold,unfolded_selected,unfolded_fields.1,unfolded_fields.2.1,
        unfolded_fields.2.2,stored_children,rows_distinct,shared_capture.1,shared_capture.2,
        afterSemantic,growth,issued,outputAvailable,published,
        prior,path,sites,finalWriters,outerIndex,outer,selectedOuter,rooted,keySame,valueSame,
        entrySame,bodySame,depthSame,ordinarySame,missing,startPath,depthPath,ordinaryPath,bodyPath,
        eventGrowth,eventIssued,storedNodes,currentSemantic,capturedAvailable,currentPublished,everyUnfold,
        inside,symbol,guard,arity,actualCalls,nodeFacts⟩
  · obtain ⟨prefixFuel,suffixFuel,priorPair,parent,next,siteBefore,siteAfter,result,after,total,strict,
      earlier,siteSemantic,siteAvailable,called,advanced,one,suffix,missing,present,
      prefixGrowth,prefixIssued,suffixGrowth,suffixIssued,used,context,built,written,origin,storedCertificate,observe⟩ := generated
    have retained := prefixGrowth.nodeRecords entry.key (.mu entry stored depth ordinary) initial_capture.1
    rw [missing] at retained
    cases retained
'''
s+='private theorem checked_witness :\n'+claim+' := by\n'+proof
s+='''
/-- An actual initial Mu capture keeps an original node call for its changed-child unfold row's stored anchor. -/
theorem actual_initial_captured_node_row :
'''+claim+' := checked_witness\n\nend MicroCFTA.OriginalCapturedNodeRowsFixture\n'
(h/'captured-node-rows-kernels.lean').write_text(s)
print(len(s.splitlines()))
