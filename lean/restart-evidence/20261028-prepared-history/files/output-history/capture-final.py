from pathlib import Path
import hashlib,json,shutil
stage=Path('/tmp/mcfta-prepared-history-20261028')
own=stage/'output-history'
repo=Path('/home/tritlo/Code/mcfta')
def sha(b):return hashlib.sha256(b).hexdigest()
def writejson(p,v):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(v,indent=2)+'\n')
def cp(src,dst):
 dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(src.read_bytes());return dst
assert not (own/'FROZEN.json').exists()
# Preserve final validator revisions separately from the earlier review capture.
for rel in ['source-validation.json','public-validation.json','audit-summary.json','strict-checks.json','modules.json','source-head.txt','document-inverse.json']:
 cp(stage/rel,own/'integration/final'/rel)
validation=json.loads((stage/'source-validation.json').read_text())
commands=[]
for expected in validation['commands']:
 folder=expected['folder'];src=stage/folder;dest=own/'commands-final'/folder
 for p in sorted(src.rglob('*')):
  if p.is_file() and p.suffix not in ['.olean','.ilean']:
   cp(p,dest/p.relative_to(src))
 report=json.loads((dest/'report.json').read_text());raw=(dest/'raw.log').read_bytes()
 assert report['exit_code']==expected['exit_code']
 assert (len(raw),sha(raw))==(expected['bytes'],expected['sha256'])
 assert report['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 if 'source_sha256' in report:
  tested=list(dest.rglob('*.lean'))
  assert any(sha(p.read_bytes())==report['source_sha256'] for p in tested),(folder,'tested source absent')
 commands.append({**expected,'report':'commands-final/'+folder+'/report.json','raw':'commands-final/'+folder+'/raw.log','measured_limits_match':True})
assert len(commands)==18 and sum(c['exit_code']!=0 for c in commands)==4
assert validation['current_commands']==17 and validation['inherited_commands']==1
writejson(own/'command-verification-final.json',{'status':'PASS','current_commands':17,'inherited_commands':1,'failures':4,'commands':commands,'review_scope':'Receipt hashes, exact tested source snapshots and measured limits checked. Root read every failed log. This owner does not claim semantic review of unrelated projection proof failures.'})
# Preserve current whole note, both exact inserted regions, and reversible old bodies.
note=stage/'root-review/notes-current-prepared-history.md';note_bytes=note.read_bytes()
assert len(note_bytes)==10627
assert note_bytes==(repo/'lean/notes-current-prepared-history.md').read_bytes()
cp(note,own/'documents/notes-current-prepared-history.md')
for name,n in [('common.md',2592),('findings.md',5752)]:
 b=(stage/'document-insertions'/name).read_bytes();assert len(b)==n
 assert b'No new required Haskell fix\nwas established.' in b
 cp(stage/'document-insertions'/name,own/'documents/insertions'/name)
root_inverse=json.loads((stage/'document-inverse.json').read_text());inverses=[]
for rel,expected in root_inverse.items():
 old=(stage/'prior-documents'/rel).read_bytes();current=(repo/rel).read_bytes();name='findings.md' if rel=='FINDINGS.md' else 'common.md'
 insert=(own/'documents/insertions'/name).read_bytes();offset=old.index(b'\n')+1
 assert current==old[:offset]+insert+old[offset:]
 assert current[:offset]+current[offset+len(insert):]==old
 assert sha(old)==expected['before_sha256'] and sha(current)==expected['after_sha256'] and len(insert)==expected['inserted_bytes']
 prior_path='documents/prior/'+rel;cp(stage/'prior-documents'/rel,own/prior_path)
 inverses.append({'source':str(repo/rel),'prior':{'path':prior_path,'bytes':len(old),'sha256':sha(old)},'insert':{'path':'documents/insertions/'+name,'bytes':len(insert),'sha256':sha(insert)},'insert_offset':offset,'current':{'bytes':len(current),'sha256':sha(current)},'inverse_exact':True,'review_scope':'Exact inserted region read. Complete historical body retained and reconstructed mechanically, not claimed semantically read.'})
assert len(inverses)==9
writejson(own/'document-inverses-final.json',{'status':'PASS','documents':inverses,'whole_note':{'path':'documents/notes-current-prepared-history.md','bytes':len(note_bytes),'sha256':sha(note_bytes),'review_scope':'WHOLE current note read; separate from narrow insertion review of historical documents.'}})
# Preserve evidence-only earlier insertion wording as historical, without replacing it.
for p in sorted((stage/'root-review/document-drafts/v1').rglob('*')):
 if p.is_file():cp(p,own/'documents/historical-insertion-v1'/p.relative_to(stage/'root-review/document-drafts/v1'))
# Current source index contains exact whole provenance and only honestly read cuts.
idx=json.loads((own/'source-index.json').read_text())
source=repo/'lean/notes-current-prepared-history.md'
assert not any(s['source']==str(source) for s in idx['sources'])
copy='documents/notes-current-prepared-history.md';cut='cuts/notes-current-prepared-history-L1-L%d.md'%len(note_bytes.splitlines())
(own/cut).write_bytes(note_bytes)
idx['sources'].append({'source':str(source),'whole':{'path':copy,'bytes':len(note_bytes),'sha256':sha(note_bytes)},'cuts':[{'path':cut,'bytes':len(note_bytes),'sha256':sha(note_bytes),'first_line':1,'last_line':len(note_bytes.splitlines())}],'scope':'WHOLE final checkpoint note reviewed. Nine older status documents have separately recorded insertion-only semantic scope and exact inverses.'})
writejson(own/'source-index.json',idx)
for s in idx['sources']:
 b=(own/s['whole']['path']).read_bytes();assert b==Path(s['source']).read_bytes();assert (len(b),sha(b))==(s['whole']['bytes'],s['whole']['sha256'])
 lines=b.splitlines(keepends=True)
 for cut in s['cuts']:
  assert 1<=cut['first_line']<=cut['last_line']<=len(lines)
  cb=(own/cut['path']).read_bytes();assert cb==b''.join(lines[cut['first_line']-1:cut['last_line']]);assert (len(cb),sha(cb))==(cut['bytes'],cut['sha256'])
# All original return binders/results and existing Complete argument recover exactly.
left=(own/'cuts/entire-original-prepared-head-declaration.lean').read_bytes();right=(own/'cuts/entire-prepared-head-declaration-recovered.lean').read_bytes()
assert left==right and len(left)==4615 and sha(left)=='d1d0b4332770bbc4818c182a7dbe54e5d127651857f72f01cf383cd410598127'
# Public records reference literal raw byte intervals and exact appended blocks.
pub=json.loads((own/'public-read-scopes-v1.json').read_text());raw=(own/'commands-final/public-readback-final/raw.log').read_bytes();prior=(own/'commands-final/prior-public-readback/raw.log').read_bytes();appendix=(own/'integration/v1/new-public-blocks.txt').read_bytes()
assert raw==prior+appendix
for block in pub['blocks']:
 b=(own/block['path']).read_bytes();assert (len(b),sha(b))==(block['bytes'],block['sha256']);assert raw[block['raw_first_byte']:block['raw_last_byte_exclusive']]==b
 assert raw[:block['raw_first_byte']].count(b'\n')+1==block['raw_first_line']
 assert raw[:block['raw_last_byte_exclusive']].count(b'\n')==block['raw_last_line']
assert len(pub['blocks'])==11 and sum(b['bytes'] for b in pub['blocks'])==66605
result={'status':'PASS','source_wholes':len(idx['sources']),'literal_source_cuts':sum(len(s['cuts']) for s in idx['sources']),'source_head':(stage/'source-head.txt').read_text().strip(),'current_commands':17,'inherited_commands':1,'failed_attempts':4,'final_strict_checks':9,'audit_jobs':4409,'audit_dependencies':81113,'assigned_whole_public_blocks':11,'assigned_public_bytes':66605,'assigned_public_lines':932,'whole_note_bytes':len(note_bytes),'whole_note_sha256':sha(note_bytes),'common_insertion_bytes':2592,'common_insertion_sha256':sha((own/'documents/insertions/common.md').read_bytes()),'findings_insertion_bytes':5752,'findings_insertion_sha256':sha((own/'documents/insertions/findings.md').read_bytes()),'exact_document_inverses':9,'entire_original_head_declaration_bytes':4615,'entire_original_head_declaration_sha256':sha(left),'owner_compiler_or_repository_mutations':0,'scope':'CLEAR within assigned actual history/invocation/rich receipt, exact checked source, public and document review. Whole prepared history resource and backward semantic composition remains OPEN.'}
writejson(own/'verification-final.json',result)
print(json.dumps(result,indent=2))
