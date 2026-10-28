from pathlib import Path
import hashlib,json,difflib
R=Path('/home/tritlo/Code/mcfta');B=Path('/tmp/mcfta-native-carriers-20261028');O=B/'native-incoming-review'
assert not (O/'FROZEN.json').exists()
sha=lambda b:hashlib.sha256(b).hexdigest()
def put(p,b):
 p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
 return {'path':str(p),'bytes':len(b),'sha256':sha(b)}
def dump(p,obj):return put(p,(json.dumps(obj,indent=2)+'\n').encode())
idx=json.loads((O/'source-index.json').read_text());records={x['source']:x for x in idx['sources']}
validation=json.loads((B/'document-validation.json').read_text());docrows=[];common=[]
for z in validation:
 p=R/z['path'];b=p.read_bytes();assert len(b)==z['bytes'] and sha(b)==z['sha256']
 if 'offset' not in z:
  assert z['path']=='lean/notes-current-native-carrier-history.md' and len(b)==12442 and sha(b)=='f6d5f1348b259f39dfc4615faabda50f6e77ef75449f45774d67648eb82e25c5'
  records[str(p)]={'source':str(p),'whole':put(O/'docs/current'/z['path'],b),'cuts':[],'reviewed_scope':'WHOLE final corrected note read. Its earlier 12443-byte state is preserved separately with the exact directional diff. No whole-reading claim for previous notes.'}
  continue
 offset=z['offset'];count=z['inserted_bytes'];insert=b[offset:offset+count];prior=(B/'prior-documents'/z['path']).read_bytes()
 assert b[:offset]+b[offset+count:]==prior and len(prior)==z['old_bytes'] and sha(prior)==z['old_sha256']
 oldrec=put(O/'docs/prior'/z['path'],prior);newrec=put(O/'docs/insertions'/(z['path']+'.txt'),insert)
 first=b[:offset].count(b'\n')+1;last=first+insert.count(b'\n')-1
 assert b''.join(b.splitlines(keepends=True)[first-1:last])==insert
 cut=dict(newrec,first_line=first,last_line=last,byte_start=offset,byte_end_exclusive=offset+count)
 records[str(p)]={'source':str(p),'source_bytes':len(b),'source_sha256':sha(b),'cuts':[cut],'reconstruction':{'prior':oldrec,'insert':newrec,'offset':offset},'reviewed_scope':'ALL exact current insertion bytes read. Whole prior body is preserved and inverse removal/reconstruction verified; the large old body is NOT claimed read.'}
 docrows.append({'path':z['path'],'offset':offset,'inserted_bytes':count,'first_line':first,'last_line':last,'inserted_sha256':sha(insert),'current_bytes':len(b),'current_sha256':sha(b),'prior_bytes':len(prior),'prior_sha256':sha(prior),'exact_inverse':True})
 if z['path']!='FINDINGS.md':common.append(insert)
assert len(docrows)==9 and len(common)==8 and len(set(common))==1
findings=next((R/z['path']).read_bytes()[z['offset']:z['offset']+z['inserted_bytes']] for z in validation if z['path']=='FINDINGS.md')
assert findings.startswith(common[0].rstrip()+b'\n')
# Retain the initial reviewed wording and Root's evidence state before the narrow correction.
for rel in ['notes-current-native-carrier-history.md','root-source-index-before.json']:
 p=B/'root-drafts/v12-doc-empty-merge'/rel;b=p.read_bytes();rec=put(O/'root-revisions/docs-before-empty-merge'/rel,b)
 records[str(p)]={'source':str(p),'whole':rec,'cuts':[],'reviewed_scope':'Historical pre-correction note/evidence state. Earlier note was read in full. It is not the final claim source.'}
old=(B/'root-drafts/v12-doc-empty-merge/notes-current-native-carrier-history.md').read_bytes();new=(R/'lean/notes-current-native-carrier-history.md').read_bytes()
assert len(old)==12443 and sha(old)=='90afda2e0a24d995f6a9d2c55598c5d24ccf9c8cb69ec1137d1d69a05b5e1631'
assert old.replace(b'The SOME handle zero used for an empty\nbucket supplies structural provenance',b'The SOME handle zero used for an Empty\nmerge supplies structural provenance')==new
put(O/'root-revisions/docs-empty-merge-correction.diff',''.join(difflib.unified_diff(old.decode().splitlines(keepends=True),new.decode().splitlines(keepends=True),fromfile='reviewed-12443B-note',tofile='final-12442B-note')).encode())
for name in ['document-validation.json','document-paths.json']:
 p=B/name
 if p.exists():records[str(p)]={'source':str(p),'whole':put(O/'integration-evidence'/name,p.read_bytes()),'cuts':[],'reviewed_scope':'Final document byte/offset validation metadata read and independently reconstructed.'}
dump(O/'docs/validation.json',{'status':'pass','documents':docrows,'all_nine_old_bodies_exact':True,'eight_common_insertions_byte_identical':True,'common_bytes':len(common[0]),'common_sha256':sha(common[0]),'findings_insertion_bytes':len(findings),'findings_extra_scope':'No new public Haskell defect; no Haskell/Cabal change, Haskell test or benchmark. Previous integrated LPO/KBO and correspondence gaps retained.','whole_current_note_read':True,'whole_historical_bodies_read':False,'correction':{'old_bytes':len(old),'old_sha256':sha(old),'final_bytes':len(new),'final_sha256':sha(new),'delta':'empty bucket -> Empty merge; no common insertion/proof/public change'}})
dump(O/'source-index.json',{'sources':list(records.values())})
print(json.dumps({'sources':len(records),'cuts':sum(len(z['cuts']) for z in records.values()),'doc_inverses':len(docrows),'note_sha256':sha(new)},indent=2))
