from pathlib import Path
import hashlib,json
root=Path('/home/tritlo/Code/mcfta')
out=Path('/tmp/mcfta-prepared-origins-20261028/ordinary-origins')
def digest(b): return hashlib.sha256(b).hexdigest()
specs=[
 ('CONTEXT.md',[(1,206)],'Whole glossary; exact path and position terminology.'),
 ('lean/MicroCFTA/Language.lean',[(414,455)],'Term.atPath and path composition. Other contents are unreviewed.'),
 ('lean/MicroCFTA/EnumerationCorrectness.lean',[(538,581),(706,790)],'Actual install and old fresh equality witnesses; bounded fill and state assignment congruence.'),
 ('lean/MicroCFTA/EnumerationSchedule.lean',[(1143,1161)],'Actual suspended counter. Other contents are unreviewed.'),
 ('lean/MicroCFTA/EnumerationConstruction.lean',[(1,205)],'Original generic head/tail model construction and inherited Holds transport.'),
 ('lean/MicroCFTA/SourcePruningEnumerationOrigins.lean',[(1,150)],'Whole shared origin foundation as read; exact allocated counter and empty-class witness branch.'),
 ('lean/MicroCFTA/SourcePruningEnumerationChildCoverage.lean',[(1,203)],'Whole old child coverage contract and constructive terminal/fresh assignment proof.'),
 ('lean/MicroCFTA/SourcePruningEnumerationEdgeInputs.lean',[(1,132)],'Whole exact equality allocation, actual ownCore and child resource admission.'),
 ('lean/MicroCFTA/SourcePruningEnumerationTraversalCoverage.lean',[(1,317)],'Whole old traversal producer and model observer.'),
 ('lean/MicroCFTA/SourcePruningEnumerationSelectedEdgeCoverage.lean',[(1,343)],'Whole old selected producer, witness allocation, child semantics and actual residual write.'),
 ('lean/MicroCFTA/SourcePruningEnumerationSelectedEdge.lean',[(1,61)],'Actual result constructors and residual finish; remaining contents are unreviewed.'),
 ('lean/MicroCFTA/SourcePruningEnumerationSelectedEdgeFinishLanguage.lean',[(1,31)],'Whole actual finish semantics.')]
records=[]
for rel,spans,scope in specs:
 p=root/rel; b=p.read_bytes(); lines=b.splitlines(keepends=True)
 copy=out/'sources'/p.name; copy.write_bytes(b)
 cuts=[]
 for start,stop in spans:
  stop=min(stop,len(lines)); assert 1<=start<=stop
  cb=b''.join(lines[start-1:stop]); cp=out/'cuts'/f'{p.stem}-L{start}-L{stop}{p.suffix}'
  cp.write_bytes(cb)
  cuts.append({'path':str(cp.relative_to(out)),'bytes':len(cb),'sha256':digest(cb),'first_line':start,'last_line':stop})
 records.append({'source':str(p),'whole':{'path':str(copy.relative_to(out)),'bytes':len(b),'sha256':digest(b)},'cuts':cuts,'scope':scope})
(out/'source-index.json').write_text(json.dumps({'sources':records},indent=2)+'\n')
# Recover each complete old public declaration from the actual new retained group.
comparisons=[]
for oldfile,newfile,oldname,newname in [
 ('SourcePruningEnumerationTraversalCoverage.lean','SourcePruningEnumerationTraversalCoverageOrigins.lean','complete_with_fragments_resources_accepting','complete_with_fragments_resources_accepting_origins'),
 ('SourcePruningEnumerationSelectedEdgeCoverage.lean','SourcePruningEnumerationSelectedEdgeOrigins.lean','complete_with_fragments_resources_accepting','complete_with_fragments_resources_origins')]:
 oldsource=(root/'lean/MicroCFTA'/oldfile).read_text(); newsource=(out/'drafts/v1'/newfile).read_text()
 os=oldsource.index('theorem '+oldname+'\n'); oe=oldsource.index(' := by',os); old=oldsource[os:oe]
 ns=newsource.index('theorem '+newname+'\n'); ne=newsource.index(' := by',ns); new=newsource[ns:ne]
 group=new.index('\n      ((∀')+len('\n      ')
 depth=0; close=None
 for i in range(group,len(new)):
  if new[i]=='(':depth+=1
  elif new[i]==')':
   depth-=1
   if depth==0: close=i; break
 assert close is not None and new[close+1:].startswith(' ∧\n      ∀ ')
 recovered=(new[:group]+new[group+1:close]).replace('theorem '+newname+'\n','theorem '+oldname+'\n',1)
 assert recovered==old,(oldfile,len(old),len(recovered))
 cp=out/'cuts'/f'{Path(oldfile).stem}-entire-original-declaration.lean'; cp.write_text(old)
 rp=out/'cuts'/f'{Path(newfile).stem}-recovered-original-declaration.lean'; rp.write_text(recovered)
 first=oldsource[:os].count('\n')+1; last=oldsource[:oe].count('\n')+1
 comparisons.append({'old_source':str(root/'lean/MicroCFTA'/oldfile),'new_candidate':str(out/'drafts/v1'/newfile),'scope':'ENTIRE theorem declaration including name, all binders and complete old existential result; proof excluded','original_first_line':first,'original_last_line':last,'original_path':str(cp.relative_to(out)),'recovered_path':str(rp.relative_to(out)),'bytes':len(old.encode()),'sha256':digest(old.encode()),'identical':True,'allowed_transformations':['Undo new theorem name','Remove only outer retained-result parentheses and appended origin observer']})
(out/'old-contract-comparison-v1.json').write_text(json.dumps({'comparisons':comparisons},indent=2)+'\n')
print(json.dumps({'whole_source_count':len(records),'cut_count':sum(len(r['cuts']) for r in records),'whole_old_declarations':comparisons},indent=2))
