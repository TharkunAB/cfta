from pathlib import Path
import hashlib,json
r=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA');o=Path('/tmp/mcfta-prepared-composition-20261028/sibling-origins')
def sha(b):return hashlib.sha256(b).hexdigest()
p=r/'SourcePruningEnumerationPreparedFiniteParentOrigins.lean';data=p.read_bytes();s=data.decode();dest=o/'sources'/p.name;dest.write_bytes(data);cuts=[];lines=data.splitlines(keepends=True)
for a,z in [(1,170),(171,len(lines))]:
 cp=o/'cuts'/f'{p.stem}-L{a}-L{z}.lean';b=b''.join(lines[a-1:z]);cp.write_bytes(b);cuts.append({'path':str(cp.relative_to(o)),'bytes':len(b),'sha256':sha(b),'first_line':a,'last_line':z})
idx=json.loads((o/'source-index.json').read_text());idx['sources'].append({'source':str(p),'whole':{'path':str(dest.relative_to(o)),'bytes':len(data),'sha256':sha(data)},'cuts':cuts,'scope':'WHOLE root parent candidate reviewed; original prepared-parent acceptance and actual Perm selector derive a chosen original index, preserving the whole sibling result before the appended model observer.'});(o/'source-index.json').write_text(json.dumps(idx,indent=2)+'\n')
sibling=(o/'drafts/v1/SourcePruningEnumerationPreparedFiniteSiblingOrigins.lean').read_text();a=sibling.index('    ∃ (bound :');z=sibling.index(' := by',a);old=sibling[a:z]
a=s.index('    ∃ (bound :');z=s.index(' := by',a);result=s[a:z];group=result.index('\n      ((∀')+len('\n      ');depth=0;close=None
for i in range(group,len(result)):
 if result[i]=='(':depth+=1
 elif result[i]==')':
  depth-=1
  if depth==0:close=i;break
assert close is not None and result[close+1:].startswith(' ∧\n      ∀ ')
recovered=result[:group]+result[group+1:close];assert recovered==old
(o/'cuts/entire-sibling-result-original.lean').write_text(old);(o/'cuts/entire-sibling-result-parent-recovered.lean').write_text(recovered)
rec={'scope':'ENTIRE sibling existential result, all resource fields and entire uniform indexed origin observer. Parent admission deliberately replaces selected-membership with Perm and full original support; no claim that those headers are identical.','old_result_bytes':len(old.encode()),'old_result_sha256':sha(old.encode()),'parent_result_recovery_identical':True,'parent_candidate_bytes':len(data),'parent_candidate_sha256':sha(data),'allowed_transform':'Remove only parent outer result grouping and appended original-parent semantic observer'}
(o/'parent-result-comparison-v1.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec,indent=2))
