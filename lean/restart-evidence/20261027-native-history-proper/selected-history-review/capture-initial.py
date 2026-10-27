from pathlib import Path
import json,hashlib
R=Path('/home/tritlo/Code/mcfta');O=Path('/tmp/mcfta-native-history-proper-20261027/selected-history-review');h=lambda b:hashlib.sha256(b).hexdigest()
scopes={
'SourcePruningEnumerationSelectedEdgeProper.lean':([(1,115)],'Whole original completed selected observer and children_proper_inputs read.'),
'SourcePruningEnumerationCapturedEdgeProper.lean':([(1,86)],'Whole original completed captured observer read.'),
'SourcePruningEnumerationSelectedEdgeResources.lean':([(45,99)],'Entire first original producer declaration read; historical proof body not independently reviewed.'),
'SourcePruningEnumerationCapturedEdgeResources.lean':([(32,91)],'Entire first original producer declaration and actual stopped/complete finalizer path read; cuts focus its contract.'),
'SourcePruningEnumerationSelectedEdge.lean':([(22,39),(69,87)],'Actual Result, finish and selected runtime read; unrelated producer proof bodies not reviewed.'),
'SourcePruningEnumerationCapturedEdge.lean':([(23,41)],'Actual captured run, optional finalizer and stopped identity read; historical producer body not reviewed in full.'),
'SourcePruningEnumerationTraversalProper.lean':([(1,49)],'Whole completed traversal trace/endpoint observer read.'),
'SourcePruningEnumerationOwnFinalizeProper.lean':([(1,103)],'Whole allocation, finalizer and residual proper observers read.'),
'SourcePruningEnumerationEdgeInputs.lean':([(14,73)],'Actual ordered children definition and full own-prefix receipt read; later proof body read through child protection, not unrelated dependencies.'),
'EnumerationProgress.lean':([(18,57),(221,237)],'ProperValue/State/Inputs, genuine inherited/descended inputs and actual suspension lemmas read; Graph-dependent enumeration theorems not used.')}
records=[]
for name,(spans,scope) in scopes.items():
 src=R/'lean/MicroCFTA'/name;b=src.read_bytes();p=O/'inputs/lean/MicroCFTA'/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b);cuts=[]
 for first,last in spans:
  last=min(last,len(b.splitlines()));v=b''.join(b.splitlines(keepends=True)[first-1:last]);q=O/'cuts'/f'{name}-L{first}-L{last}.txt';q.parent.mkdir(exist_ok=True);q.write_bytes(v);cuts.append({'path':str(q),'bytes':len(v),'sha256':h(v),'first_line':first,'last_line':last})
 records.append({'source':str(src),'whole':{'path':str(p),'bytes':len(b),'sha256':h(b)},'cuts':cuts,'reviewed_scope':scope})
(O/'source-index.json').write_text(json.dumps({'sources':records},indent=2)+'\n')
cs=[]
for family,old,new in [('SelectedEdge','complete_with_fragments_resources','complete_with_fragments_resources_proper'),('CapturedEdge','complete_with_history_resources','complete_with_history_resources_proper')]:
 a=(R/f'lean/MicroCFTA/SourcePruningEnumeration{family}Resources.lean').read_text();a=a[a.index('theorem '+old):];a=a[:a.index(' := by')]
 b=(O/f'drafts/v1/SourcePruningEnumeration{family}EndpointProper.lean').read_text();b=b[b.index('theorem '+new):];b=b[:b.index(' := by')]
 marker=') ∧\n      (ProperState before.core →';assert marker in b
 rec=b.split(marker,1)[0].replace('theorem '+new,'theorem '+old,1).replace('      ((∀ er','      (∀ er',1)
 assert rec==a
 folder=O/'contracts'/family;folder.mkdir(parents=True,exist_ok=True)
 for tag,v in [('old-entire-declaration',a),('new-entire-declaration',b),('recovered-entire-declaration',rec)]: (folder/f'{tag}.txt').write_text(v)
 body=(O/f'drafts/v1/SourcePruningEnumeration{family}EndpointProper.lean').read_text().split('theorem '+new,1)[1].split(' := by',1)[1]
 assert body.count('\n    '+old+' ')==1
 cs.append({'family':family,'original_theorem':old,'new_theorem':new,'entire_old_declaration_recovered':True,'bytes':len(a.encode()),'sha256':h(a.encode()),'single_original_producer_call':True,'normalization':'Only theorem rename, outer original-packet grouping and appended ProperState observer removed. All binders, witnesses, original conjunctions and order remain byte identical.'})
(O/'contracts/comparisons.json').write_text(json.dumps(cs,indent=2)+'\n')
print(json.dumps({'sources':len(records),'cuts':sum(len(x['cuts']) for x in records),'contracts':cs},indent=2))
