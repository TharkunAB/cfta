from pathlib import Path
import gzip,hashlib,json,sys
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-prepared-models-20261028');snapshot=root/'lean/restart-evidence/20261028-prepared-models'
def sha(b):return hashlib.sha256(b).hexdigest()
assert (area/'FROZEN.json').exists()
assert not snapshot.exists();snapshot.mkdir()
records=[]
for p in sorted(area.rglob('*')):
 if not p.is_file():continue
 assert not p.is_symlink(),p
 raw=p.read_bytes();rel=p.relative_to(area).as_posix();compressed=len(raw)>8192
 stored='files/'+rel+('.gz' if compressed else '')
 data=gzip.compress(raw,compresslevel=9,mtime=0) if compressed else raw
 target=snapshot/stored;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
 records.append(dict(path=rel,stored=stored,size=len(raw),sha256=sha(raw),stored_size=len(data),stored_sha256=sha(data),gzip=compressed))
manifest=dict(format='mcfta-prepared-models-v1',source_head=(area/'source-head.txt').read_text().strip(),frozen_area=str(area),payloads=records)
(snapshot/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
(snapshot/'README.md').write_text('''# Prepared enumeration model evidence

The manifest records every frozen TEMP payload and its stored and raw SHA256.
Large payloads use deterministic gzip. No file is omitted from the frozen set.
The source checkpoint precedes the documentation and evidence commit.
Run `python3 files/verify-archive.py SNAPSHOT --live` to verify live sources.
Add `--reconstruct DESTINATION` to reconstruct and compare the exact TEMP set.
Use `--committed` after the evidence commit to compare stored Git bytes.
The old proof and evidence archives remain unchanged.
''')
print(json.dumps(dict(snapshot=str(snapshot),payloads=len(records),stored_bytes=sum(x['stored_size'] for x in records),raw_bytes=sum(x['size'] for x in records),gz=sum(x['gzip'] for x in records),manifest_sha256=sha((snapshot/'manifest.json').read_bytes()))))
