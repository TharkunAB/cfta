from pathlib import Path
import gzip,hashlib,json
area=Path('/tmp/mcfta-native-carriers-20261028');snapshot=Path('/home/tritlo/Code/mcfta/lean/restart-evidence/20261028-native-carrier-history');manifest=json.loads((snapshot/'manifest.json').read_text());decoded=json.loads((snapshot/'decoded-files.json').read_text());archives={x['stored_path']:x for x in decoded};logical={}
for r in manifest['files']:
 if r['path']=='decoded-files.json':continue
 b=(snapshot/r['path']).read_bytes();assert len(b)==r['bytes'] and hashlib.sha256(b).hexdigest()==r['sha256']
 if r['path'] in archives:
  x=archives[r['path']];b=gzip.decompress(b);assert len(b)==x['bytes'] and hashlib.sha256(b).hexdigest()==x['sha256'];name=x['original_path']
 else:name=r['path']
 assert name not in logical;logical[name]=b
actual={str(p.relative_to(area)) for p in area.rglob('*') if p.is_file()};assert set(logical)==actual,(set(logical)^actual)
for n,b in logical.items():assert b==(area/n).read_bytes(),n
report=dict(status='pass',exact_logical_files=len(logical),raw_bytes=sum(map(len,logical.values())),manifest_sha256=hashlib.sha256((snapshot/'manifest.json').read_bytes()).hexdigest(),temporary_tree_exact=True)
Path('/tmp/mcfta-native-carriers-temp-reconstruction.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
