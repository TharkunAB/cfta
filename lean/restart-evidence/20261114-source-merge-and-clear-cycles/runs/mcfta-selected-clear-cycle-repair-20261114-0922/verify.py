from pathlib import Path
import hashlib,json,re,sys
sys.dont_write_bytecode=True
from patch_replay import replay
root=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
pins=json.loads((root/'PINS').read_text());manifest=(root/'MANIFEST').read_bytes()
assert sha(manifest)==pins['manifest_sha256']
expected=set()
for line in manifest.decode().splitlines():
 digest,size,name=line.split(' ',2);p=root/name;assert p.is_file() and not p.is_symlink();b=p.read_bytes();assert sha(b)==digest and len(b)==int(size);expected.add(name)
assert {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}==expected|{'MANIFEST','PINS'}
assert len(expected)==pins['payloads']
old=(root/'original-failed-instrumented.lean').read_text();new=(root/'SourcePruningEnumerationSelectedClearCycles-v2-UNCOMPILED.lean').read_text();patch=(root/'repair.patch').read_text();checks=json.loads((root/'CHECKS.json').read_text());heads=json.loads((root/'HEADERS.json').read_text())
assert sha(old.encode())==checks['original_sha256'] and sha(new.encode())==checks['candidate_sha256']
assert sha((root/'original-failed-private-proof.txt').read_bytes())==checks['original_diagnostic_sha256']
assert replay(old,patch)==new and replay(new,patch,True)==old
for name,h in heads.items():
 for tag,source in [('original',old),('candidate',new)]:
  start=source.index('theorem '+name);end=source.index(':= by',start)+len(':= by');assert source[start:end]==h[tag];assert sha(h[tag].encode())==checks[name][tag+'_sha256']
first='selected_clear_keeps_closed_references';second='proper_closed_references_no_assignment'
assert heads[second]['original']==heads[second]['candidate']
assert old[:old.index('theorem '+first)]==new[:new.index('theorem '+first)]
marker='    (∀ (language : NodeLanguage Symbol)'
assert heads[first]['original'].split(marker)[0]==heads[first]['candidate'].split(marker)[0]
assert heads[first]['original'].replace('      slotSatisfies assignment vertex (EnumerationCorrectness.heap language after.values vertex) ↔','      (slotSatisfies assignment vertex (EnumerationCorrectness.heap language after.values vertex) ↔').replace('before.core.values vertex)) := by','before.core.values vertex))) := by')==heads[first]['candidate']
assert not re.search(r'\b(?:sorry|admit|axiom)\b',new)
assert 'sorryAx' in (root/'original-failed-private-proof.txt').read_text()
assert pins['status']=='WRITE HALT; UNCOMPILED; original strict FAIL retained'
print('PASS exact approved header correction, preserved clauses/second header and forward/reverse replay; UNCOMPILED')
