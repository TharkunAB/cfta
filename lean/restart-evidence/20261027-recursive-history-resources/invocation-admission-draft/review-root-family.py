from pathlib import Path
import json,hashlib,re,datetime
repo=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-recursive-history-resources-20261027');out=area/'invocation-admission-draft';sha=lambda b:hashlib.sha256(b).hexdigest();folder=out/'root-family-review';folder.mkdir(exist_ok=True)
idx=json.loads((out/'source-pins.json').read_text());result=[]
clause=re.compile(r' ∧\n\s+SourcePruningEnumerationRecursive\.RecursiveCallbackAdmission formulas solver\n\s+returnedInventory reached returnedMemos metadata after uv fragment recursiveFuel\n\s+\(SourcePruningEnumerationRecursiveReservation\.afterHead headSeed inherited\)\n\s+\(SourcePruningEnumerationRecursiveReservation\.massCeil headSeed capturedMass inherited\)')
def strip_comments(s):return re.sub(r'/\-.*?\-/','',s,flags=re.S)
def normalize(s):return re.sub(r'\s+',' ',strip_comments(s)).strip()
def declarations(s):
 starts=[m.start() for m in re.finditer(r'^theorem ',s,re.M)];end=s.rfind('\nend ');return [s[a:b] for a,b in zip(starts,starts[1:]+[end])]
families=[('SourcePruningEnumerationSiblingInvocationResources','SourcePruningEnumerationSiblingInvocationAdmission',[
 ('alternatives_finite_complete_resources_with_callback_admissions','alternatives_finite_complete_resources_with_invocations'),
 ('alternatives_finite_complete_invocation_admission_resources','alternatives_finite_complete_invocation_resources'),
 ('alternatives_finite_invocation_admissions','alternatives_finite_invocation_receipts')]),
 ('SourcePruningEnumerationOrdinaryInvocationResources','SourcePruningEnumerationOrdinaryInvocationAdmission',[
 ('ordinary_finite_complete_resources_with_callback_admissions','ordinary_finite_complete_resources_with_invocations'),
 ('ordinary_finite_complete_invocation_admission_resources','ordinary_finite_complete_invocation_resources'),
 ('alternatives_finite_invocation_admissions','alternatives_finite_invocation_receipts')])]
for oldname,newname,renames in families:
 oldpath=repo/'lean/MicroCFTA'/(oldname+'.lean');newpath=repo/'lean/MicroCFTA'/(newname+'.lean');old=oldpath.read_text();new=newpath.read_text();restored,count=clause.subn('',new);assert count==2,(newname,count)
 for a,b in renames:restored=restored.replace(a,b)
 olddecl=declarations(old);newdecl=declarations(restored);assert len(olddecl)==len(newdecl)==2
 comparisons=[]
 for number,(a,b) in enumerate(zip(olddecl,newdecl),1):
  assert normalize(a)==normalize(b),(newname,number)
  ah=a[:a.index(' := by')];bh=b[:b.index(' := by')];assert normalize(ah)==normalize(bh)
  basename=newname+f'-theorem-{number}'
  for label,text in [('old-full-declaration',a),('retained-full-declaration',b),('old-contract',ah),('retained-contract',bh),('normalized-retained',normalize(b))]:
   (folder/(basename+'-'+label+'.txt')).write_text(text)
  comparisons.append(dict(theorem_number=number,old_contract_sha256=sha(ah.encode()),normalized_retained_contract_sha256=sha(normalize(bh).encode()),whole_normalized_body_and_contract_identical=True))
 for name in [oldname,newname]:
  p=repo/'lean/MicroCFTA'/(name+'.lean');raw=p.read_bytes();snapshot='inputs/lean/MicroCFTA/'+p.name;(out/snapshot).write_bytes(raw)
  idx['sources'].append(dict(path=str(p),source=str(p),snapshot=snapshot,bytes=len(raw),sha256=sha(raw),read_scope='whole current family source read; old source proof reused at exact prior checked identity and independently compared'))
  text=raw.decode();lines=raw.splitlines(keepends=True)
  for m in re.finditer(r'^theorem ',text,re.M):
   end=text.index(' := by',m.start())+len(' := by');start=text[:m.start()].count('\n')+1;last=text[:end].count('\n')+1;b=b''.join(lines[start-1:last]);cut=f'cuts/{name}--{start}-{last}.lean';(out/cut).write_bytes(b);idx['cuts'].append(dict(path=str(p),source=str(p),snapshot=cut,start=start,end=last,source_sha256=sha(raw),bytes=len(b),sha256=sha(b)))
 result.append(dict(old_source=str(oldpath),new_source=str(newpath),old_sha256=sha(old.encode()),new_sha256=sha(new.encode()),removed_admission_conjunct_count=count,renames=renames,only_comments_and_whitespace_normalized=True,comparisons=comparisons))
(folder/'independent-comparison.json').write_text(json.dumps(dict(status='PASS',observed_at=datetime.datetime.now().astimezone().isoformat(),families=result),indent=2)+'\n')
original=area/'root-family-comparison.json';b=original.read_bytes();(folder/'root-family-comparison.json').write_bytes(b)
idx.setdefault('evidence',[]).append(dict(source=str(original),snapshot='root-family-review/root-family-comparison.json',bytes=len(b),sha256=sha(b)))
(out/'source-pins.json').write_text(json.dumps(idx,indent=2)+'\n')
print(json.dumps(dict(status='CLEAR',sources=len(idx['sources']),cuts=len(idx['cuts']),cut_lines=sum(c['end']-c['start']+1 for c in idx['cuts']),all_four_public_declaration_and_proof_bodies_exact_after_precise_admission_drop_names_and_whitespace_comments=True),indent=2))
