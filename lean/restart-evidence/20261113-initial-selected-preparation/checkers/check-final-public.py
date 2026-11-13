from pathlib import Path
import datetime,hashlib,json,os,re,shlex,subprocess
root=Path('/home/tritlo/Code/mcfta'); runtime=Path(__file__).parent
cg=next(x.split(':',2)[2] for x in Path('/proc/self/cgroup').read_text().splitlines() if x.startswith('0::'))
base=Path('/sys/fs/cgroup')/cg.lstrip('/')
limits={k:(base/k).read_text().strip() for k in ['memory.max','memory.high','memory.swap.max']}
assert limits=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
sha=lambda b:hashlib.sha256(b).hexdigest()
def snapshot():return '\n'.join(p.name+' '+sha(p.read_bytes()) for p in sorted((root/'lean/MicroCFTA').glob('*.lean')))+'\n'
before=snapshot();(runtime/'final-source-pins.txt').write_text(before)
expected={'SourceSynthesisCurrentInitialPrefixOrigin':'786a7f5f1f3938fd720eecfcbef94608f625377c36af66138532bfc800f265e6','SourceSynthesisCurrentInitialOuterNarrowFacts':'a6e7b4874537313f62fdf4416bf64dbb1ecafb2a1c17eae57f99992114a43ab4','SourcePruningEnumerationSharedBranchingAppend':'997933df32672c54609d4359a06532007c87f3e03ef6768f05334f1fd44e8101'}
for module,digest in expected.items():assert sha((root/'lean/MicroCFTA'/(module+'.lean')).read_bytes())==digest
env=dict(os.environ);env.pop('LEAN_SYSROOT',None);env['LEAN_NUM_THREADS']='1'
checks=[];allowed={'propext','Classical.choice','Quot.sound'}
def run(name,command,min_groups=0):
 p=subprocess.run(['nix-shell',str(root/'shell.nix'),'--run',command],cwd=root/'lean',env=env,capture_output=True,text=True)
 out=p.stdout+p.stderr;(runtime/(name+'.txt')).write_text(out)
 groups=[set(x.strip() for x in g.split(',') if x.strip()) for g in re.findall(r'depends on axioms:\s*\[([^]]*)\]',out,re.S)]
 bad=sorted(set().union(*groups)-allowed) if groups else []
 item={'name':name,'exit':p.returncode,'axiom_groups':len(groups),'nonstandard_axioms':bad};checks.append(item)
 (runtime/'final-partial-report.json').write_text(json.dumps(checks,indent=2)+'\n')
 assert p.returncode==0 and len(groups)>=min_groups and not bad and 'sorryAx' not in out,name
run('final-full-audit-build','exec lake build MicroCFTA.Audit')
module='SourceSynthesisCurrentInitialPreparationOrigin'; name='MicroCFTA.SourceSynthesisCurrentInitialPrefixOrigin.initial_prefix_preparation_rows'
p=runtime/'preparation-public-strict.lean';p.write_text((root/'lean/MicroCFTA'/(module+'.lean')).read_text()+'\n#print axioms '+name+'\n')
run('preparation-public-strict','exec lake env lean -j1 -DwarningAsError=true '+shlex.quote(str(p)),1)
laws={'SourceSynthesisCurrentInitialPrefixOrigin':'MicroCFTA.SourceSynthesisCurrentInitialPrefixOrigin.initial_prefix_narrowed_rows','SourceSynthesisCurrentInitialOuterNarrowFacts':'MicroCFTA.SourceSynthesisCurrentInitialOuterNarrowFacts.initial_outer_narrow_facts','SourceSynthesisCurrentInitialPreparationOrigin':name,'SourcePruningEnumerationSharedBranchingAppend':'MicroCFTA.SourcePruningEnumerationSharedBranching.scan_append','SourceSynthesisCurrentZeroProgramObstruction':'MicroCFTA.SourceSynthesisCurrentZeroProgramObstruction.size_zero_frontend_without_program'}
p=runtime/'final-public-imports.lean';p.write_text(''.join('import MicroCFTA.'+m+'\n' for m in laws)+''.join('\n#check '+n+'\n#print axioms '+n+'\n' for n in laws.values()))
run('final-public-imports','exec lake env lean -j1 -DwarningAsError=true '+shlex.quote(str(p)),5)
p=runtime/'final-Audit.lean';p.write_bytes((root/'lean/MicroCFTA/Audit.lean').read_bytes())
run('final-full-audit-strict','exec lake env lean -j1 -DwarningAsError=true '+shlex.quote(str(p)),1)
counts=re.findall(r'Checked axiom dependencies of (\d+) MicroCFTA theorems',(runtime/'final-full-audit-strict.txt').read_text());assert len(counts)==1 and int(counts[0])>94990
assert snapshot()==before
report={'at':datetime.datetime.now().astimezone().isoformat(),'limits':limits,'live_modules':len(before.splitlines()),'audit_imports':sum(s.startswith('import ') for s in p.read_text().splitlines()),'audited_theorems':int(counts[0]),'source_tree_sha256':sha(before.encode()),'checks':checks,'reused_checked_sources_unchanged':['prefix236','facts101','scan_append49'],'haskell_changes':False,'joint_completion_proved':False}
(runtime/'final-checked.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
