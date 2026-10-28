from pathlib import Path
import json,hashlib
stage=Path('/tmp/mcfta-prepared-composition-20261028');own=stage/'sibling-origins';repo=Path('/home/tritlo/Code/mcfta')
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(path,b):
    dst=own/path;dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(b)
    return {'path':path,'bytes':len(b),'sha256':sha(b)}
common=(stage/'document-insertions/common.md').read_bytes();findings=(stage/'document-insertions/findings.md').read_bytes()
pin('documents/common.md',common);pin('documents/findings.md',findings)
records=[]
for prior in sorted((stage/'prior-documents').rglob('*')):
    if not prior.is_file():continue
    rel=prior.relative_to(stage/'prior-documents').as_posix();old=prior.read_bytes();current=(repo/rel).read_bytes();ins=findings if rel=='FINDINGS.md' else common
    a=old.index(b'\n')+1;assert current==old[:a]+ins+old[a:];assert current[:a]+current[a+len(ins):]==old
    prior_pin=pin('documents/prior/'+rel,old);span={'first_line':current[:a].count(b'\n')+1,'last_line':current[:a+len(ins)].count(b'\n')}
    records.append({'source':str(repo/rel),'current_bytes':len(current),'current_sha256':sha(current),'prior':prior_pin,'insert':{'path':'documents/findings.md' if rel=='FINDINGS.md' else 'documents/common.md','bytes':len(ins),'sha256':sha(ins)},'insertion_first_byte':a,'insertion_last_byte_exclusive':a+len(ins),**span,'inverse_exact':True,'scope':'Only the exact new insertion is semantically reviewed. Complete old body is preserved and hash/reconstruction verified; it was not reread.'})
assert len(records)==9
note=(repo/'lean/notes-current-prepared-composition.md').read_bytes();assert note==(stage/'root-review/notes-current-prepared-composition.md').read_bytes();assert len(note)==9443
np=pin('documents/notes-current-prepared-composition.md',note);lines=note.splitlines(keepends=True)
cp=pin('cuts/notes-current-prepared-composition-L1-L'+str(len(lines))+'.md',note)
idx=json.loads((own/'source-index.json').read_text());idx['sources'].append({'source':str(repo/'lean/notes-current-prepared-composition.md'),'whole':np,'cuts':[{**cp,'first_line':1,'last_line':len(lines)}],'scope':'WHOLE final current checkpoint note semantically reviewed against checked own contracts, assigned whole public statements and actual validation records.'})
(own/'source-index.json').write_text(json.dumps(idx,indent=2)+'\n')
(own/'document-inverse-review-final.json').write_text(json.dumps({'status':'PASS','whole_new_note':np,'insertions':records,'common_identical_documents':8,'findings_adds_haskell_handoff':True,'reconstruction':'current = prior[:insertion_first_byte] + insert + prior[insertion_first_byte:]; removal exactly recovers prior','review_scope':'Whole new note and both complete insertion texts reviewed. All nine actual insertion regions and exact prior-body reconstruction checked. No whole old-document semantic review claimed.'},indent=2)+'\n')
print(json.dumps({'status':'PASS','note_bytes':len(note),'note_sha256':sha(note),'insertions':len(records),'prior_bytes_preserved':sum(r['prior']['bytes'] for r in records)},indent=2))
