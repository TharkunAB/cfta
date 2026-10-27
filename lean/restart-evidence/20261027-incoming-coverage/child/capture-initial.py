from pathlib import Path
import hashlib,json
base=Path('/tmp/mcfta-incoming-coverage-20261027/child');root=Path('/home/tritlo/Code/mcfta');stage=base.parent
sha=lambda d:hashlib.sha256(d).hexdigest()
records=[]
def cp(src,rel,first=None,last=None):
 full=src.read_bytes();data=full if first is None else b''.join(full.splitlines(keepends=True)[first-1:last]);out=base/rel;out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(data)
 item={'source':str(src),'snapshot':rel,'kind':'whole' if first is None else 'cut','bytes':len(data),'sha256':sha(data)}
 if first is not None:
  assert last<=len(full.splitlines(keepends=True));item.update(first_line=first,last_line=last,source_bytes=len(full),source_sha256=sha(full))
 records.append(item)
inputs=[(stage/'terminal-child/drafts/v2/SourcePruningEnumerationTerminalChildCoverage.lean',[(34,95),(96,113)]),
(root/'lean/MicroCFTA/SourcePruningEnumerationChildResources.lean',[(33,100)]),
(root/'lean/MicroCFTA/SourcePruningEnumerationCachedPrepareLanguage.lean',[(19,93)]),
(root/'lean/MicroCFTA/EnumerationCorrectness.lean',[(538,550),(630,649),(755,776)]),
(root/'lean/MicroCFTA/EnumerationConstruction.lean',[(44,49)]),
(root/'lean/MicroCFTA/SourcePruningEnumerationChildStableLanguage.lean',[(80,122)])]
for src,cuts in inputs:
 cp(src,'inputs/'+src.name)
 for a,b in cuts:cp(src,f'cuts/{src.stem}.{a}-{b}.lean.txt',a,b)
cp(root/'lean/MicroCFTA/SourcePruningEnumerationChildDispatch.lean','cuts/SourcePruningEnumerationChildDispatch.28-71.lean.txt',28,71)
new=(base/'drafts/v1/SourcePruningEnumerationChildCoverage.lean').read_text()
def stmt(text,name):
 a=text.index('theorem '+name);b=text.index(' := by',a);return text[a:b]
newstmt=stmt(new,'complete_with_fragments_resources_accepting')
oldterminal=stmt(inputs[0][0].read_text(),'complete_with_fragments_resources_terminal_accepting')
oldresources=stmt(inputs[1][0].read_text(),'complete_with_fragments_resources')
newheader,newoutput=newstmt.split(' :\n    ∃',1)
oldheader,oldoutput=oldterminal.split(' :\n    ∃',1)
end=newoutput.index(') ∧\n      ∀ (ambient : InternedGuardedLanguage.Env Symbol)',newoutput.index('      ∀ (ambient : InternedGuardedLanguage.Env Symbol)'))
recoveredoutput=newoutput[:end].replace('      ((∀ extraRepresentative','      (∀ extraRepresentative',1)
recovered=newheader.replace('theorem complete_with_fragments_resources_accepting','theorem complete_with_fragments_resources_terminal_accepting',1)+' :\n    ∃'+recoveredoutput
assert recovered==oldterminal
# The terminal observer is itself an appendix to the exact original resource packet.
a=oldterminal.index(' ∧\n      ∀ (ambient : InternedGuardedLanguage.Env Symbol)')
resourceRecovered=oldterminal[:a].replace('theorem complete_with_fragments_resources_terminal_accepting','theorem complete_with_fragments_resources',1)
assert resourceRecovered==oldresources
comparisons=[]
for label,original,derived in [('terminal',oldterminal,recovered),('resource',oldresources,resourceRecovered)]:
 for role,value in [('original',original),('recovered',derived)]:
  (base/f'contracts/{label}-{role}-full-statement.lean.txt').write_text(value)
 comparisons.append({'comparison':label,'status':'PASS','original':f'contracts/{label}-original-full-statement.lean.txt','recovered':f'contracts/{label}-recovered-full-statement.lean.txt','bytes':len(original.encode()),'sha256':sha(original.encode())})
comparison={'status':'PASS','comparisons':comparisons,'mapping':['Remove the final all-child assignment-extension observer.','Remove ONLY one pair grouping the entire original terminal conjunction.','Restore the terminal theorem name; all admission binders and existential witnesses are literal.','For the original ChildResources comparison also remove ONLY the prior terminal observer and restore the original resource theorem name.'], 'terminal_producer_calls':new.count('\n    complete_with_fragments_resources_terminal_accepting '),'cached_semantics_calls':new.count('SourcePruningEnumerationCachedPrepare.complete_semantics ')}
assert comparison['terminal_producer_calls']==1 and comparison['cached_semantics_calls']==1
(base/'contracts/comparison.json').write_text(json.dumps(comparison,indent=2)+'\n')
(base/'source-index.json').write_text(json.dumps({'status':'OPEN','line_convention':'one-based inclusive; preserve original LF','records':records},indent=2)+'\n')
print(json.dumps({'draft_sha256':sha(new.encode()),'records':len(records),'whole_inputs':len(inputs),'cuts':len(records)-len(inputs),'comparisons':comparisons},indent=2))
