from pathlib import Path
import hashlib,json,re,sys
sys.dont_write_bytecode=True
from patch_replay import replay
root=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
pins=json.loads((root/'PINS').read_text());manifest=(root/'MANIFEST').read_bytes();assert sha(manifest)==pins['manifest_sha256'];expected=set()
for line in manifest.decode().splitlines():
 digest,size,name=line.split(' ',2);p=root/name;assert p.is_file() and not p.is_symlink();b=p.read_bytes();assert sha(b)==digest and len(b)==int(size);expected.add(name)
assert {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}==expected|{'MANIFEST','PINS'}
assert len(expected)==pins['payloads']
base=(root/'Root-reported-checked-v2-base.lean').read_text();full=(root/'SourcePruningEnumerationSelectedClearCycles-v3-corollary-UNCOMPILED.lean').read_text();addition=(root/'ADDITION.lean.txt').read_text();header=(root/'HEADER.txt').read_text();patch=(root/'additive.patch').read_text();checks=json.loads((root/'CHECKS.json').read_text())
for name,value in [('base',base),('candidate',full),('addition',addition),('header',header)]:assert sha(value.encode())==checks[name+'_sha256']
assert base.count('end MicroCFTA.SourcePruningEnumerationRecursion')==1
assert full==base.replace('end MicroCFTA.SourcePruningEnumerationRecursion',addition+'end MicroCFTA.SourcePruningEnumerationRecursion')
assert full.count(addition)==1 and full.replace(addition,'')==base
assert replay(base,patch)==full and replay(full,patch,True)==base
start=addition.index('theorem selected_clear_proper_cycle_unsatisfiable');end=addition.index(':= by',start)+len(':= by');assert addition[start:end]==header
assert len(addition.splitlines())==33 and len(full.splitlines())==187
assert not re.search(r'\b(?:sorry|admit|axiom)\b',addition)
assert 'Satisfies language meaning assignment after' in header
assert 'Satisfies language meaning assignment before' not in header and 'Suspended.Holds' not in header
assert pins['status']=='WRITE HALT; additive corollary UNCOMPILED'
print('PASS complete v2 byte preservation, exact new header and forward/reverse additive replay; corollary UNCOMPILED')
