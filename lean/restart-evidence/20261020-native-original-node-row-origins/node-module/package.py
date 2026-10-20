from pathlib import Path
import hashlib,json,shutil
p=Path(__file__).resolve().parent
root=Path('/home/tritlo/Code/mcfta')
def write(name,value):(p/name).write_text(json.dumps(value,indent=2)+'\n')
def pin(base,name):
 data=(base/name).read_bytes();return {'path':name,'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)}
shutil.copyfile(p/'node-row-origins-peaks.txt',p/'node-row-origins-peaks-final.txt')
head='MicroCFTA.SourceCurrentNativeOriginalNodeRowOrigins.build_node_row_origins'
write('node-row-origins-selection.json',{'source':'SourceCurrentNativeOriginalNodeRowOrigins.lean',
 'sha256':pin(p,'SourceCurrentNativeOriginalNodeRowOrigins.lean')['sha256'],
 'selected_strict':'node-row-origins-direct-2','selected_public':'node-row-origins-public-1',
 'public_heads':[head],'lean_jobs':3,'failed_attempts':1,'public_pairs':1,'constructed_pairs':0,'canonical_jobs':0,
 'unselected':[{'stem':'node-row-origins-direct-1','status':'failed','reason':'Unknown Nat.strong_induction_on; Lean4.34 uses Nat.strongRecOn. The corrected source also unpacks the actual rawRow/SourceRow prefix before terminal witnesses.'}],
 'scope':'Actual original source build gives one trace and ultimate original node calls for its full stored rows. No global native rank or changed unfold-row identity.'})
(p/'node-row-origins-review.md').write_text('''# Ultimate original node-row provenance

The sole public head is build_node_row_origins. The caller supplies only the actual completed build of original syntax with empty inputs from the empty heap. The native formula and guard instances follow the existing source consumers.

The proof calls build_row_resumptions once. It retains that same publication path, indexed rooted sites, and final full-cell writer selector. Strong natural induction on a publication index derives an actual original node producer for every full structural row in that indexed event's stored body. No source-origin, rank, chain, writer, or induction hypothesis is a public premise.

In the node arm, the same returned terminal supplies the source node expression, actual build, rich Context, original Reached, SourceRow, generic SyntaxBound, union descent, buildEdges, makeNode, distinct source and canonical output indices, and the actual full RowCall. The call's complete output equals the selected EdgeValue. The producer index is the current index. The terminal suffix reaches the fixed raw callback's return. Its actual withoutSelfReference filter then reaches the outer afterBody. Context.build establishes validity at the raw return before run_correct and run_issued_extends are used. No reverse growth is used.

In the binder arm, the same resumption supplies an earlier index strictly smaller than the current index and an exact lookup in the same event list. Full candidate injectivity aligns the selected stored body with that earlier event's body. The induction hypothesis consumes that exact earlier lookup and the same complete structural row. It retains the resulting actual node SourceRow and RowCall unchanged. Its producer index is at most the earlier index, hence at most the current index.

The returned node heap grows to the earlier afterBody by induction. Public publication_growth extends this through actual publication to earlier.after. Completion preserves issued names definitionally. The exact resumption suffix then reaches outer.afterBody. No standalone completion Path is fabricated. The proof does not preserve a bound against the later requester expression across a historical jump. Its generic SyntaxBound and UnionDescent remain relative to the actual node producer's expression.

The result includes nullary rows. It requires no selected child, positive arity, guard positivity, stored winner uniqueness, or current-callback identity. The source and output row indices remain distinct. The exact row includes all stored children and full fields. It is not an identity claim about a later row whose children were changed by an actual unfold.

Selected strict2 has an empty log. The full public printer contains the complete type and proof with all eight settings and only propext, Classical.choice, and Quot.sound. The expanded public type has no private helper names. Three own capped jobs are retained: one failed induction-name draft, one successful strict check, and one successful full printer. Each uses pinned Lean4.34.1, all linters, effective4GiB memory.max/high, zero swap, a five-minute wrapper, and fresh usage. This package adds one public group, no constructed group, and no canonical job.

This theorem closes repeated binder stops for a fixed stored row in one completed original source trace. It does not yet attach every later generated native capture to that original trace. It does not transport a full reader continuation, identify changed unfold children, prove original lexical uniqueness, or establish global runtime termination or Haskell refinement. Publication index orders past source events. It is not a general future native rank.

Run node-row-origins-verify.py from any directory. Ordinary verification uses retained source snapshots. --live additionally checks the current ROOT, selected with --root. The verifier invokes no Lean process. The manifest excludes itself, generated verification output, mutable peaks, and other owners' metadata.
'''.replace('Lean4.34.1','Lean 4.34.1').replace('effective4GiB','effective 4 GiB'))
modules=['SourceCurrentNativeOriginalIndexedResumption','SourceCurrentNativeOriginalPublicationTrace',
 'SourceCurrentNativeOriginalUnionDescent','SourceCurrentNativeOriginalObservedResume',
 'SourceCurrentNativeMuPublication','SourceCurrentNativeMuGrowthHistory','SourceCurrentNativeMuIssuedHistory',
 'SourceCurrentBuildStructuralRowOrigins','SourceCurrentConstrainedCapSourceHistory',
 'InternedFreshOrdinaryFacts','InternedProbeProvenance']
sources=[]
for module in modules:
 name='lean/MicroCFTA/'+module+'.lean';sources.append(pin(root,name))
 target=p/'inputs'/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(root/name,target)
write('node-row-origins-source-pins.json',{'snapshot_root':'inputs','files':sources})
files=['SourceCurrentNativeOriginalNodeRowOrigins.lean','node-row-origins-run-check.py','node-row-origins-capped-worker.py',
 'node-row-origins-public.lean','assemble.py','node-origin-result.lean.txt','node-row-origins-selection.json',
 'node-row-origins-review.md','node-row-origins-source-pins.json','node-row-origins-verify.py','node-row-origins-peaks-final.txt']
for stem in ['node-row-origins-direct-1','node-row-origins-direct-2','node-row-origins-public-1']:
 files += [stem+suffix for suffix in ['.json','.source.lean','.log','.limits.json','.usage.json']]
write('node-row-origins-manifest.json',{'schema':1,'files':[pin(p,n) for n in files],'sources':sources,
 'public_heads':[head],'lean_jobs':3,'failed_attempts':1,'public_pairs':1,'constructed_pairs':0,'canonical_jobs':0})
