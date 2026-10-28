from pathlib import Path
from hashlib import sha256
from datetime import datetime
import json

R=Path('/home/tritlo/Code/mcfta')
A=Path('/tmp/mcfta-native-partial-output-20261028')
O=A/'recursive-model-review'
index=json.loads((O/'source-index.json').read_text())
records=index['sources']
def copy(src,dest):
    data=src.read_bytes()
    (O/dest).parent.mkdir(parents=True,exist_ok=True)
    (O/dest).write_bytes(data)
    return {'source':str(src),'path':str(dest),'bytes':len(data),'sha256':sha256(data).hexdigest()}
# Keep the literal full historical snapshots for the two initial cuts whose
# live repository documents now contain the new checkpoint insertion.
for rec in records:
    if rec['source'] in [str(R/'NEXT-PROMPT.md'),str(R/'FINDINGS.md')]:
        name=Path(rec['source']).name
        original=A/'prior-documents'/name
        data=original.read_bytes()
        assert sha256(data).hexdigest()==rec['sha256'] and len(data)==rec['bytes']
        rel=Path('documents/historical-whole')/name
        copied=copy(original,rel)
        rec['whole']={k:copied[k] for k in ['path','bytes','sha256']}
        rec['snapshot_status']='Exact historical whole bytes from this stage prior-documents; line cuts predate current insertion.'

validation=json.loads((A/'document-validation.json').read_text())
documents=[]
for v in validation:
    source=R/v['path']; data=source.read_bytes()
    assert len(data)==v['bytes'] and sha256(data).hexdigest()==v['sha256']
    whole=copy(source,Path('documents/current-whole')/v['path'])
    rec={'source':str(source),'bytes':len(data),'sha256':whole['sha256'],
         'whole':{k:whole[k] for k in ['path','bytes','sha256']},'cuts':[]}
    if 'offset' in v:
        start=v['offset']; end=start+v['inserted_bytes']
        inserted=data[start:end]
        old=data[:start]+data[end:]
        expected=(A/'prior-documents'/v['path']).read_bytes()
        assert old==expected
        assert len(old)==v['old_bytes'] and sha256(old).hexdigest()==v['old_sha256']
        assert start==0 or data[start-1:start]==b'\n'
        assert data[end-1:end]==b'\n'
        first=data[:start].count(b'\n')+1; last=data[:end].count(b'\n')
        assert b''.join(data.splitlines(keepends=True)[first-1:last])==inserted
        rel=Path('documents/insertion-cuts')/(v['path'].replace('/','__')+f'.L{first}-L{last}.txt')
        (O/rel).parent.mkdir(parents=True,exist_ok=True); (O/rel).write_bytes(inserted)
        rec['cuts'].append({'path':str(rel),'first_line':first,'last_line':last,
          'first_byte':start,'last_byte_exclusive':end,'bytes':len(inserted),
          'sha256':sha256(inserted).hexdigest(),'source_sha256':whole['sha256'],
          'span_convention':'1-based inclusive lines; zero-based half-open byte offsets; exact literal insertion.'})
        rec['inspection']='Inserted region only; whole bytes preserved for exact inverse checks. No whole-reading claim for older body.'
        documents.append({'path':v['path'],'whole_sha256':whole['sha256'],
          'insertion':rec['cuts'][0],'old_body_bytes':len(old),'old_body_sha256':sha256(old).hexdigest(),
          'literal_inverse_equals_stage_prior':True})
        print(v['path']+f' lines {first}-{last}, exact inserted {len(inserted)} bytes:')
        print(inserted.decode())
    else:
        rec['inspection']='WHOLE new note read; all current claims reviewed.'
        documents.append({'path':v['path'],'whole_bytes':len(data),'whole_sha256':whole['sha256'],'inspection':'whole'})
    records.append(rec)
# Current Haskell partial renderer, read explicitly for the new-note comparison.
for rec in records:
    if rec['source']==str(R/'cfta/src/Data/CFTA/Enumeration.hs'):
        data=(R/'cfta/src/Data/CFTA/Enumeration.hs').read_bytes()
        cut=b''.join(data.splitlines(keepends=True)[1028:1048])
        rel=Path('cuts/Enumeration.hs.L1029-L1048.txt'); (O/rel).write_bytes(cut)
        rec['cuts'].append({'path':str(rel),'first_line':1029,'last_line':1048,'bytes':len(cut),
            'sha256':sha256(cut).hexdigest(),'source_sha256':sha256(data).hexdigest()})
index['captured_final_at']=datetime.now().astimezone().isoformat()
(O/'source-index.json').write_text(json.dumps(index,indent=2)+'\n')
(O/'document-inverse-checks.json').write_text(json.dumps({'status':'PASS','documents':documents},indent=2)+'\n')

metadata=['modules.json','strict-checks.json','source-stats.json','source-head.txt','source-validation.json',
          'public-validation.json','public-prefix-comparison.json','preservation-validation.json',
          'audit-import-insertion.json','root-contract-comparisons.json','actual-commands.json',
          'command-validation.json','document-validation.json','document-paths.json',
          'new-public-declarations.json','public-declarations.json','public-definitions.json']
files=[copy(A/name,Path('final-evidence/root-metadata')/name) for name in metadata]
commands=json.loads((A/'actual-commands.json').read_text())
assert len(commands)==17 and sum(c['report']['exit_code']!=0 for c in commands)==5
for command in commands:
    name=command['name']; report=command['report']; origin=A/name
    raw=(origin/'raw.log').read_bytes()
    assert len(raw)==report['bytes'] and sha256(raw).hexdigest()==report['sha256']
    assert report['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
    files.append(copy(origin/'report.json',Path('final-evidence/commands')/name/'report.json'))
    files.append(copy(origin/'raw.log',Path('final-evidence/commands')/name/'raw.log'))
    if 'source_sha256' in report:
        checked=Path(report['command'][-1])
        assert sha256(checked.read_bytes()).hexdigest()==report['source_sha256']
        files.append(copy(checked,Path('final-evidence/commands')/name/checked.name))

current=(A/'public-readback-1/raw.log').read_bytes()
prior=(A/'prior-public-readback/raw.log').read_bytes()
appendix=(A/'new-public-blocks.txt').read_bytes()
assert current==prior+appendix
assert len(prior)==1292203 and len(current)==1329075 and len(appendix)==36872
assert sha256(current).hexdigest()=='08e37eb0ddd0f9032a3f2fb9a8368e5e4c0bdbb7e22bde80ee83ef248c65bc13'
assert sha256(appendix).hexdigest()=='44a27ef0302330e156b4eae437003fffff6a23af789ccb4dfdd31570a5debdb2'
files.append(copy(A/'new-public-blocks.txt',Path('final-evidence/new-public-blocks.txt')))
files.append(copy(A/'prior-public-readback/raw.log',Path('final-evidence/prior-public-readback/raw.log')))
files.append(copy(A/'prior-public-readback/report.json',Path('final-evidence/prior-public-readback/report.json')))
(O/'final-evidence-index.json').write_text(json.dumps({'files':files,'status':'PASS',
 'commands':17,'failed_commands':5,'inherited_prior_readback_counted_as_current':False,
 'public_equals_exact_prior_plus_whole_new_appendix':True,
 'new_appendix_read':'WHOLE 469 lines / 3 public operation bodies / 9 theorem blocks; no prefix-only reading claim.',
 'source_head':(A/'source-head.txt').read_text().strip(),
 'note_read':'WHOLE final 14784-byte note; all nine actual literal insertions read; all nine old bodies independently recovered byte-for-byte.'},indent=2)+'\n')
