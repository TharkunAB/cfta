from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parent
hash_bytes=lambda b:hashlib.sha256(b).hexdigest()
checks=0
index=json.loads((root/'source-pins.json').read_text())
for source in index['sources']:
 whole=(root/source['copy']).read_bytes()
 assert len(whole)==source['bytes'] and hash_bytes(whole)==source['sha256']
 assert Path(source['source_path']).read_bytes()==whole
 checks+=1
 lines=whole.splitlines(keepends=True)
 for cut in source['cuts']:
  data=(root/cut['path']).read_bytes()
  assert data==b''.join(lines[cut['first_line']-1:cut['last_line']])
  assert len(data)==cut['bytes'] and hash_bytes(data)==cut['sha256']
  checks+=1
for source in json.loads((root/'installed-identities.json').read_text())['sources']:
 data=(root/source['draft']).read_bytes()
 assert Path(source['source_path']).read_bytes()==data
 assert hash_bytes(data)==source['sha256']
 checks+=1
for item in json.loads((root/'root-evidence-index.json').read_text())['files']:
 data=(root/item['copy']).read_bytes()
 assert hash_bytes(data)==item['sha256'] and len(data)==item['bytes']
 assert Path(item['source_path']).read_bytes()==data
 checks+=1
for report in (root/'root-evidence').glob('*/report.json'):
 record=json.loads(report.read_text());data=(report.parent/'raw.log').read_bytes()
 assert hash_bytes(data)==record['sha256'] and len(data)==record['bytes']
 limits=record['cgroup_limits']
 assert limits['memory.max']=='4294967296' and limits['memory.swap.max']=='0'
 source=report.parent/'MicroCFTA/SourcePruningEnumerationArityOrigins.lean'
 if not source.exists():source=report.parent/'MicroCFTA/SourcePruningEnumerationCheckedSyntaxOrigins.lean'
 if source.exists():assert hash_bytes(source.read_bytes())==record['source_sha256']
 checks+=1
print(json.dumps({'status':'PASS','data_checks':checks,'whole_sources':index['whole_count'],'literal_cuts':index['cut_count'],'cut_lines':index['cut_lines'],'scope':'File identities and literal source/evidence correspondence only. No compiler or theorem validation ran.'}))
