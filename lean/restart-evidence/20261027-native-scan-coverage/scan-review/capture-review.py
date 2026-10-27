from pathlib import Path
import hashlib,json
repo=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-native-scan-coverage-20261027');out=area/'scan-review';sha=lambda b:hashlib.sha256(b).hexdigest()
def put(rel,b):
 p=out/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b.encode() if isinstance(b,str) else b)
spec=[('SourcePruningEnumerationNativeBranchResources',[(1,319)],'Original head and full scan admission/result/induction inspected; remaining projection wrappers are provenance only.'),('SourcePruningEnumerationNativeBranches',[(21,63)],'Actual advance/run, fixed captured input, exact unsupported stopping; remaining whole bytes provenance.'),('SourcePruningEnumerationNativeLanguage',[(1,len((repo/'lean/MicroCFTA/SourcePruningEnumerationNativeLanguage.lean').read_bytes().splitlines()))],'Whole language transport module inspected; same-core native-growth iff is used.'),('SourcePruningEnumerationCapturedEdgeCoverage',[(35,113)],'Existing accepted captured full proposition; remaining proof provenance.'),('SourcePruningEnumerationCapturedEdgeAccepting',[(37,74),(139,174)],'Prior parent-model derivation and its actual local call; whole proof was reviewed in the preceding frozen checkpoint.'),('SourcePruningEnumerationSelectorLanguage',[(1,81)],'Whole current selector witness module inspected; canonical physical map correspondence remains explicit.'),('SourcePruningEnumerationNativeContinuations',[(17,71),(111,127)],'Exact hook result/stop and hook-before-sibling boundary; remaining whole bytes provenance.'),('SourceCurrentAllocatedPartialInvariant',[(24,84)],'Actual Context/Post/current full Memos and different-inventory composition; rest provenance.'),('SourcePruningEnumerationNativeHeadCoverage',[(1,201)],'Whole new head source reviewed; original branch costs and effects retained.'),('SourcePruningEnumerationNativeBranchCoverage',[(1,314)],'Whole new scan V2 source reviewed; indexed same-run observer and same captured cache.')]
rows=[]
for name,spans,scope in spec:
 src=repo/'lean/MicroCFTA'/f'{name}.lean';b=src.read_bytes();lines=b.splitlines(keepends=True);copy='sources/'+src.name;put(copy,b);row={'source':str(src),'whole':{'path':copy,'bytes':len(b),'sha256':sha(b)},'review_scope':scope,'cuts':[]}
 for a,z in spans:
  assert z<=len(lines),(name,a,z,len(lines))
  c=b''.join(lines[a-1:z]);p=f'cuts/{src.name}.{a}-{z}.txt';put(p,c);row['cuts'].append({'path':p,'bytes':len(c),'sha256':sha(c),'first_line':a,'last_line':z})
 rows.append(row)
put('source-index.json',json.dumps({'sources':rows},indent=2)+'\n')
def prop(src,name):
 s=src.read_text();return s[s.index('theorem '+name+'\n'):].split(' := by\n',1)[0]
contracts=[]
for module,theorem,marker in [('SourcePruningEnumerationNativeHeadCoverage','head_complete_resources_accepting',' ∧\n      ∀ (ambient'),('SourcePruningEnumerationNativeBranchCoverage','complete_with_history_resources_accepting',' ∧\n      ∀ (index : Nat) (chosen')]:
 new=prop(repo/'lean/MicroCFTA'/f'{module}.lean',theorem);oldname=theorem.removesuffix('_accepting');old=prop(repo/'lean/MicroCFTA/SourcePruningEnumerationNativeBranchResources.lean',oldname);recovered=new.rsplit(marker,1)[0].replace('theorem '+theorem,'theorem '+oldname,1);assert old==recovered
 put('contracts/'+module+'.original.txt',old);put('contracts/'+module+'.recovered.txt',recovered)
 contracts.append({'module':module,'old_name':oldname,'entire_old_proposition_bytes':len(old.encode()),'entire_old_proposition_sha256':sha(old.encode()),'exact_recovery':True,'only_mapping':'Delete final semantic observer and restore old theorem name.'})
put('contracts/independent-comparison.json',json.dumps({'status':'PASS','contracts':contracts},indent=2)+'\n')
for rel,dest in [('head-owner/drafts/v1/SourcePruningEnumerationNativeHeadCoverage.lean','reviewed-drafts/head-v1.lean'),('scan-owner/drafts/v2/SourcePruningEnumerationNativeBranchCoverage.lean','reviewed-drafts/scan-v2.lean')]:put(dest,(area/rel).read_bytes())
put('reviewed-drafts/status.json',json.dumps({'head_v1_sha256':sha((out/'reviewed-drafts/head-v1.lean').read_bytes()),'scan_v2_sha256':sha((out/'reviewed-drafts/scan-v2.lean').read_bytes()),'proof_review':'CLEAR for these exact sources; Root owns checks and edits','bundle':'OPEN; actual final strict/public/docs pending'},indent=2)+'\n')
print(json.dumps({'status':'PASS','source_records':len(rows),'literal_cuts':sum(len(x['cuts']) for x in rows),'old_contracts':contracts}))
