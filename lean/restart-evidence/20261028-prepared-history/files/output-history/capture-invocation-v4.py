from pathlib import Path
import hashlib,json,difflib
stage=Path('/tmp/mcfta-prepared-history-20261028');own=stage/'output-history';repo=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA');name='SourcePruningEnumerationSelectedInvocation.lean'
def sha(b):return hashlib.sha256(b).hexdigest()
source=repo/name;b=source.read_bytes();assert sha(b)=='4ec94612025fd51b4873b9d117d1e6625c6f75e59a45c796277091c1d8d61ff5';path='sources/'+name;(own/path).write_bytes(b);lines=b.splitlines(keepends=True);cuts=[]
for a,z in [(1,59),(60,90),(91,len(lines))]:
    cb=b''.join(lines[a-1:z]);cp=f'cuts/{source.stem}-L{a}-L{z}.lean';(own/cp).write_bytes(cb);cuts.append({'path':cp,'bytes':len(cb),'sha256':sha(cb),'first_line':a,'last_line':z})
idx=json.loads((own/'source-index.json').read_text());idx['sources'].append({'source':str(source),'whole':{'path':path,'bytes':len(b),'sha256':sha(b)},'cuts':cuts,'scope':'WHOLE current Root generic selected invocation and both extraction proofs independently reviewed, exact original preparation and ordinary/terminal/opaque cases including stopped-hook outputs.'});(own/'source-index.json').write_text(json.dumps(idx,indent=2)+'\n')
for folder in ['selected-invocation-v2','selected-invocation-v3','selected-invocation-v4','selected-invocation-build']:
    for src in sorted((stage/folder).rglob('*')):
        if src.is_file() and src.suffix not in ['.olean','.ilean']:
            dst=own/'checks'/folder/src.relative_to(stage/folder);dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(src.read_bytes())
initial=stage/'projection-heap-v1/input-sources'/name;dst=own/'dependencies/selected-invocation-initial-UNTESTED.lean';dst.parent.mkdir();dst.write_bytes(initial.read_bytes());(own/'dependencies/selected-invocation-initial-to-v4.diff').write_text(''.join(difflib.unified_diff(initial.read_text().splitlines(keepends=True),b.decode().splitlines(keepends=True),fromfile='initial-UNTESTED',tofile='v4-STRICTPASS')))
rep=json.loads((stage/'selected-invocation-v4/report.json').read_text());assert rep['exit_code']==0 and rep['source_sha256']==sha(b) and (stage/'selected-invocation-v4/raw.log').read_bytes()==b''
assert (stage/'selected-invocation-v4/MicroCFTA'/name).read_bytes()==b
(own/'selected-invocation-review-v4.json').write_text(json.dumps({'status':'CLEAR','source_bytes':len(b),'source_lines':len(lines),'source_sha256':sha(b),'strict_exit_code':0,'strict_raw_bytes':0,'exact_checked_installed':True,'build_exit_code':json.loads((stage/'selected-invocation-build/report.json').read_text())['exit_code'],'review':'Whole final source and both extraction proofs read. Actual preparation target/handle/decoded separated from prepared value/heap. Terminal-first; ordinary Invocation or actual singleton complete receipt. Both complete/stopped hook outputs retained. No model/resource/future-success gate. Prior v2/v3 failed strict receipts preserved, not claimed semantically reread in full.'},indent=2)+'\n')
print(len(b),len(lines),sha(b))
