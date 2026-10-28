from pathlib import Path
import hashlib,json,shutil
base=Path('/tmp/mcfta-prepared-origins-20261028'); out=base/'ordinary-origins'; root=Path('/home/tritlo/Code/mcfta')
def sha(b):return hashlib.sha256(b).hexdigest()
idx=json.loads((out/'source-index.json').read_text()); records=[]
inv=json.loads((base/'document-inverse.json').read_text())
for name in ['document-inverse.json','document.py','source-validation.json','source-head.txt']:
 shutil.copyfile(base/name,out/'final-evidence'/name)
for rel,r in inv.items():
 current=(root/rel).read_bytes(); prior=(base/'prior-documents'/rel).read_bytes()
 insertion=(base/'document-insertions'/('findings.md' if rel=='FINDINGS.md' else 'common.md')).read_bytes()
 offset=prior.index(b'\n')+1
 assert len(insertion)==r['inserted_bytes'] and sha(prior)==r['before_sha256'] and sha(current)==r['after_sha256']
 assert current==prior[:offset]+insertion+prior[offset:]
 assert current[:offset]+current[offset+len(insertion):]==prior
 whole=out/'documents/current'/rel; old=out/'documents/prior'/rel; cut=out/'documents/insertions'/(rel.replace('/','__')+'.insert.md')
 for p,b in [(whole,current),(old,prior),(cut,insertion)]: p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
 first=current[:offset].count(b'\n')+1; last=first+insertion.count(b'\n')-1
 assert b''.join(current.splitlines(keepends=True)[first-1:last])==insertion
 idx['sources'].append({'source':str(root/rel),'whole':{'path':str(whole.relative_to(out)),'bytes':len(current),'sha256':sha(current)},'cuts':[{'path':str(cut.relative_to(out)),'bytes':len(insertion),'sha256':sha(insertion),'first_line':first,'last_line':last}],'scope':'WHOLE exact current insertion read. Prior body preserved and byte-compared; giant prior historical body is not a semantic review claim.'})
 records.append({'source':str(root/rel),'prior':{'path':str(old.relative_to(out)),'bytes':len(prior),'sha256':sha(prior)},'insert':{'path':str(cut.relative_to(out)),'offset':offset,'bytes':len(insertion),'sha256':sha(insertion)},'current':{'path':str(whole.relative_to(out)),'bytes':len(current),'sha256':sha(current)},'exact_inverse':True})
rel='lean/notes-current-prepared-origins.md'; note=(root/rel).read_bytes(); p=out/'documents/current'/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(note)
cut=out/'documents/insertions/notes-current-prepared-origins-WHOLE.md';cut.write_bytes(note)
idx['sources'].append({'source':str(root/rel),'whole':{'path':str(p.relative_to(out)),'bytes':len(note),'sha256':sha(note)},'cuts':[{'path':str(cut.relative_to(out)),'bytes':len(note),'sha256':sha(note),'first_line':1,'last_line':len(note.splitlines())}],'scope':'WHOLE final standalone note read, including final current/inherited command denominators.'})
(out/'source-index.json').write_text(json.dumps(idx,indent=2)+'\n')
(out/'documents/inverse-independent.json').write_text(json.dumps({'status':'PASS','documents':records,'note':{'path':str(p.relative_to(out)),'bytes':len(note),'sha256':sha(note)},'scope':'All9 exact current inserted regions and entire new note reviewed; every old body retained byte-for-byte without claiming a whole historical semantic rereview'},indent=2)+'\n')
print(json.dumps({'insertions':len(records),'note_bytes':len(note),'note_sha256':sha(note),'source_wholes':len(idx['sources']),'source_cuts':sum(len(r['cuts'])for r in idx['sources'])},indent=2))
