from pathlib import Path
import hashlib,json,shutil,re,datetime
root=Path('/home/tritlo/Code/mcfta')
area=Path('/tmp/mcfta-traversal-coverage-20261027')
out=area/'edge-assessment'
sha=lambda b: hashlib.sha256(b).hexdigest()
def write(rel,b):
 p=out/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b.encode() if isinstance(b,str) else b)
def js(rel,x):write(rel,json.dumps(x,indent=2,ensure_ascii=False)+'\n')
def copy(src,rel):write(rel,src.read_bytes())
# Whole copies preserve provenance. Review scope is explicit for each literal cut.
specs=[
('SourcePruningEnumerationTraversalCoverage',[(1,317)],'whole final source reviewed; constructive same-result traversal coverage'),
('SourcePruningEnumerationTraversalResources',[(31,87),(126,164)],'old complete resource contract and actual suffix admission'),
('SourcePruningEnumerationChildCoverage',[(35,114),(115,204)],'child accepting contract and assignment-extension proof dependency'),
('SourcePruningEnumerationSelectedEdge',[(19,90)],'actual selected-edge runtime; remaining whole bytes are provenance only'),
('SourcePruningEnumerationSelectedEdgeResources',[(28,119)],'existing original resource admission/output and preparation; rest provenance'),
('SourcePruningEnumerationEdgeInputs',[(14,133)],'actual projected/inherited ordered child preparation'),
('SourcePruningEnumerationConstraint',[(1,90)],'whole project_complete contract and proof'),
('SourcePruningEnumerationEdgeProjectionLanguage',[(1,75)],'whole current resident guard projection theorem'),
('SourcePruningEnumerationAnnotationHeap',[(1,38)],'whole Context/Post annotation derivation'),
('InternedGuardedLanguage',[(24,52),(109,136)],'independent native meaning and ordered forest decomposition'),
('EnumerationCorrectness',[(84,93),(412,449),(539,600),(755,788)],'assignment equality/residual/fresh-state construction and storage congruence; rest provenance'),
('EnumerationState',[(22,28),(196,201),(394,420),(459,527)],'Holds, arity, and inherited descent laws; rest provenance'),
('EnumerationConstruction',[(44,49),(136,194)],'assignment extension and GRAPH proof pattern only; not a native proof'),
('SourcePruningEnumerationSelectedEdgeFinishLanguage',[(1,30)],'whole actual residual-write semantics'),
('SourceCurrentAllocatedParentEdge',[(83,109)],'current receipt construction and conditional forward parent language'),
('InternedEdgeResidency',[(20,44)],'parent resident outgoing-edge residency'),
('SourcePruningEnumerationNativeOrdinary',[(23,100)],'actual ordinary edge selection and subset admission; rest provenance'),
('EqualityTrie',[(23,67),(75,111),(133,151),(623,646)],'descent lookup definitions/laws; validity-free forward bridge is a PROPOSAL'),
('SourcePruningEnumerationShallowChild',[(14,61)],'actual fresh node versus opaque Mu/Union slot shape'),
('SourcePruningEnumerationNativeIndex',[(17,46)],'actual candidate flag and indexed write'),
('MergedOrdinaryHeight',[(88,97)],'actual recursive boundary'),
('EnumerationIndexSelection',[(37,40)],'candidate list definition'),
('EnumerationPureSelection',[(164,172)],'actual empty-candidate selection'),
('SourcePruningEnumerationRestart',[(12,42)],'actual stop/selection restart'),
('SourcePruningEnumerationRecursive',[(78,94)],'actual done-frontier emission'),
('SourcePruningEnumerationRendering',[(22,62)],'Discharged and actual marker rendering boundary'),
('SourcePruningEnumerationSelectedEdgeStableResourceLanguage',[(31,82)],'existing conditional stable runtime semantic observer; not coverage')]
records=[]
for name,spans,scope in specs:
 src=root/'lean/MicroCFTA'/f'{name}.lean';b=src.read_bytes();lines=b.splitlines(keepends=True)
 rec={'source_path':str(src),'copy':f'sources/{name}.lean','bytes':len(b),'sha256':sha(b),'review_scope':scope,'cuts':[]}
 copy(src,rec['copy'])
 for a,z in spans:
  assert 1<=a<=z<=len(lines),(name,a,z,len(lines))
  cut=b''.join(lines[a-1:z]);p=f'cuts/{name}.{a}-{z}.txt';write(p,cut)
  rec['cuts'].append({'path':p,'start_line':a,'end_line':z,'bytes':len(cut),'sha256':sha(cut)})
 records.append(rec)
for rel,spans,scope in [('cfta/src/Data/CFTA/Enumeration.hs',[(711,747),(776,801),(1048,1074),(1109,1125)],'literal actual source branches only; no native execution or Haskell defect claim'),('lean/notes-current-traversal-coverage.md',[(1,len((root/'lean/notes-current-traversal-coverage.md').read_bytes().splitlines()))],'whole final new checkpoint note reviewed')]:
 src=root/rel;b=src.read_bytes();lines=b.splitlines(keepends=True);name=src.name
 rec={'source_path':str(src),'copy':f'sources/{name}','bytes':len(b),'sha256':sha(b),'review_scope':scope,'cuts':[]};copy(src,rec['copy'])
 for a,z in spans:
  c=b''.join(lines[a-1:z]);p=f'cuts/{name}.{a}-{z}.txt';write(p,c);rec['cuts'].append({'path':p,'start_line':a,'end_line':z,'bytes':len(c),'sha256':sha(c)})
 records.append(rec)
js('source-index.json',{'source_head':(area/'source-head.txt').read_text().strip(),'sources':records})
for rel in ['statistics.json','strict-checks.json','source-validation.json','public-validation.json','public-declarations.json','prior-public-declarations.json','public-definitions.json','prior-strong-sources.json','document-paths.json','document-validation.json','source-head.txt','source-commit.json','traversal-dependent-result-repair.json','audit-import-insertion.json']:
 copy(area/rel,'evidence/'+rel)
for d in ['strict-traversal-coverage-1','strict-traversal-coverage-2','strict-audit-coverage-1','audit-coverage-1','public-readback-1','prior-public-readback']:
 for src in sorted((area/d).rglob('*')):
  if src.is_file() and src.name not in ['pins.json','FROZEN.json']:
   copy(src,str(Path('evidence')/d/src.relative_to(area/d)))
for rel in ['original-full-statement.txt','recovered-full-statement.txt','comparison.json','v1-v2-proof-only.patch']:
 copy(area/'owner/contracts'/rel,'contracts/root-'+rel)
copy(area/'new-public-block.txt','evidence/new-public-block.txt')
# Recover the ENTIRE old proposition directly from both current source declarations.
new=(root/'lean/MicroCFTA/SourcePruningEnumerationTraversalCoverage.lean').read_text()
old=(root/'lean/MicroCFTA/SourcePruningEnumerationTraversalResources.lean').read_text()
new_stmt=new[new.index('theorem complete_with_fragments_resources_accepting'):].split(' := by\n',1)[0]
old_stmt=old[old.index('theorem complete_with_fragments_resources\n'):].split(' := by\n',1)[0]
recovered=new_stmt.rsplit(' ∧\n      ∀ (ambient',1)[0].replace('theorem complete_with_fragments_resources_accepting','theorem complete_with_fragments_resources',1)
assert recovered==old_stmt
write('contracts/independent-old-statement.txt',old_stmt);write('contracts/independent-recovered-statement.txt',recovered)
assert old_stmt.encode()==(area/'owner/contracts/original-full-statement.txt').read_bytes()
# All original public output is literal prefix; the ONLY added suffix is the fully read new block.
public=(area/'public-readback-1/raw.log').read_bytes();prior=(area/'prior-public-readback/raw.log').read_bytes();block=(area/'new-public-block.txt').read_bytes()
assert public==prior+block
axiom_lists=re.findall(rb'depends on axioms: \[([^\]]*)\]',public)
assert len(axiom_lists)==163,len(axiom_lists)
standard={b'propext',b'Classical.choice',b'Quot.sound'}
for aa in axiom_lists:
 assert set(x.strip() for x in aa.replace(b'\n',b' ').split(b',') if x.strip()) <= standard,aa
assert '⋯'.encode() not in public
# Reports are actual existing parent-run checks, not checks run by this review.
checks=[]
for d in ['strict-traversal-coverage-1','strict-traversal-coverage-2','strict-audit-coverage-1','audit-coverage-1','public-readback-1']:
 report=json.loads((area/d/'report.json').read_text());raw=(area/d/'raw.log').read_bytes()
 assert len(raw)==report['bytes'] and sha(raw)==report['sha256']
 assert report['exit_code']==(1 if d.endswith('coverage-1') and d.startswith('strict-traversal') else 0)
 assert report['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 checks.append({'check':d,'exit_code':report['exit_code'],'bytes':len(raw),'sha256':sha(raw),'limits':report['cgroup_limits']})
installed=(root/'lean/MicroCFTA/SourcePruningEnumerationTraversalCoverage.lean').read_bytes()
assert installed==(area/'strict-traversal-coverage-2/MicroCFTA/SourcePruningEnumerationTraversalCoverage.lean').read_bytes()
assert installed==(area/'installed-sources/lean/MicroCFTA/SourcePruningEnumerationTraversalCoverage.lean').read_bytes()
assert len(installed)==23184 and len(installed.splitlines())==317 and sha(installed)=='2c364afef1dc3f20742e48a2822f70b06589a98563c0bb688f81a2694b3497c6'
prior_sources=json.loads((area/'prior-strong-sources.json').read_text())
assert len(prior_sources)==85
for x in prior_sources:
 b=(root/x['path']).read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256'],x['path']
# Document regions are exact byte slices. Deleting each slice recovers ALL prior bytes.
docs=[]
for x in json.loads((area/'document-validation.json').read_text()):
 src=root/x['path'];b=src.read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256']
 rec={'document_source_path':str(src),'bytes':len(b),'sha256':sha(b)}
 if 'offset' in x:
  offset=x['offset'];n=x['inserted_bytes'];cut=b[offset:offset+n];oldbytes=b[:offset]+b[offset+n:]
  assert oldbytes==(area/'prior-documents'/x['path']).read_bytes()
  assert len(oldbytes)==x['prior_bytes'] and sha(oldbytes)==x['prior_sha256']
  p='documents/insertions/'+x['path'];write(p,cut)
  rec.update({'offset':offset,'inserted_bytes':n,'insertion_copy':p,'insertion_sha256':sha(cut),'prior_bytes':len(oldbytes),'prior_sha256':sha(oldbytes),'entire_prior_bytes_recovered':True})
 else:
  p='documents/'+x['path'];write(p,b);rec['whole_copy']=p
 docs.append(rec)
js('documents/independent-validation.json',docs)
audit=(root/'lean/MicroCFTA/Audit.lean').read_bytes();insertion=json.loads((area/'audit-import-insertion.json').read_text());off=insertion['insertion_offset'];n=insertion['inserted_bytes']
assert audit[:off]+audit[off+n:]==(area/'prior-sources/Audit.lean').read_bytes()
copy(area/'prior-sources/Audit.lean','evidence/prior-Audit.lean')
js('verification-final.json',{'status':'PASS','review_scope':'read-only byte checks and source/contract review; no compiler, build, Git, network or repository writes by reviewer','source_head':(area/'source-head.txt').read_text().strip(),'source_records':len(records),'literal_cuts':sum(len(r['cuts']) for r in records),'old_entire_proposition_bytes':len(old_stmt.encode()),'old_entire_proposition_sha256':sha(old_stmt.encode()),'public_old_blocks':162,'public_new_blocks':1,'public_all_blocks':len(axiom_lists),'entire_old_public_bytes_literal_prefix':True,'standard_axioms_only':True,'prior_source_pins_unchanged':len(prior_sources),'document_regions':9,'new_note_whole':True,'all_prior_document_bytes_recovered':True,'installed_strict_snapshot_equal':True,'audit_import_only_inverse':True,'checks':checks})
print(json.dumps({'assembled':True,'source_records':len(records),'literal_cuts':sum(len(r['cuts']) for r in records),'old_contract_bytes':len(old_stmt.encode()),'files_before_reports':sum(p.is_file() for p in out.rglob('*'))}))
