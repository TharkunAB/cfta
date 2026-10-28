from pathlib import Path
import hashlib,json
own=Path('/tmp/mcfta-prepared-history-20261028/output-history');stage=own.parent;name='SourcePruningEnumerationPreparedOutputHistory.lean';source=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA')/name
b=source.read_bytes();sha=lambda b:hashlib.sha256(b).hexdigest();assert sha(b)=='3148bb137069d3cba43593f438cec240cc80140c49713e17348be740ec0c2eac';assert b==(own/'drafts/v2'/name).read_bytes();lines=b.splitlines(keepends=True);whole='sources/'+name;(own/whole).write_bytes(b);cuts=[]
for a,z in [(1,105),(106,len(lines))]:
 cb=b''.join(lines[a-1:z]);path=f'cuts/{source.stem}-L{a}-L{z}.lean';(own/path).write_bytes(cb);cuts.append({'path':path,'bytes':len(cb),'sha256':sha(cb),'first_line':a,'last_line':z})
idx=json.loads((own/'source-index.json').read_text());idx['sources'].append({'source':str(source),'whole':{'path':whole,'bytes':len(b),'sha256':sha(b)},'cuts':cuts,'scope':'WHOLE owner final v2 actual history relation, genuine new-Failure callback/finish lemmas and arbitrary-work/depth extraction proofs reviewed; exact checked/installed source. No resource or model premise.'});(own/'source-index.json').write_text(json.dumps(idx,indent=2)+'\n')
folder='prepared-output-history-v2'
for src in sorted((stage/folder).rglob('*')):
 if src.is_file() and src.suffix not in ['.olean','.ilean']:
  dst=own/'checks'/folder/src.relative_to(stage/folder);dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(src.read_bytes())
report=json.loads((stage/folder/'report.json').read_text());assert report['exit_code']==0 and report['source_sha256']==sha(b) and (stage/folder/'raw.log').read_bytes()==b'';assert (stage/folder/'MicroCFTA'/name).read_bytes()==b
(own/'checked-status-v2.json').write_text(json.dumps({'status':'PASS','source':str(source),'bytes':len(b),'lines':len(lines),'sha256':sha(b),'strict_check':'checks/'+folder,'strict_raw_bytes':0,'actual_first_attempt_on_v2':True,'v1':'Historical UNTESTED draft, preserved. V2 adds only explicit shared Output import. No actual failed owner theorem check.','owner_compiler_commands':0,'bundle_status':'OPEN for installed build, aggregate/public/docs review and Root cue'},indent=2)+'\n');print(json.dumps({'status':'PASS','bytes':len(b),'lines':len(lines),'sha256':sha(b)},indent=2))
