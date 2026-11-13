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
expected={'SourceSynthesisCurrentInitialSharedVisitorOrigin':'7eaf53b409635287b0899b989d5f07e1ab34e21fd16f1416bb16235a07f75ac4','SourceSynthesisCurrentInitialEagerInvocation':'fd1a31072856240c4822da795476ca408c89eddb1920bdb0282fb3d2ae1c5599'}
for module,digest in expected.items():assert sha((root/'lean/MicroCFTA'/(module+'.lean')).read_bytes())==digest
baseline=json.loads((runtime/'baseline-live-source-pins.json').read_text())
for path,digest in baseline.items():
 if path!='lean/MicroCFTA/Audit.lean':assert sha((root/path).read_bytes())==digest,path
assert len(before.splitlines())==5913
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
visitor='MicroCFTA.SourceSynthesisCurrentInitialSharedVisitorOrigin.initial_prepared_shared_root_scan_origin'
reused=Path('/tmp/mcfta-initial-shared-visitor-public-check-20261113-1832')
assert json.loads((reused/'draft-checked.json').read_text())['compiler_exit']==0
assert (reused/'check.lean').read_bytes()==(root/'lean/MicroCFTA/SourceSynthesisCurrentInitialSharedVisitorOrigin.lean').read_bytes()+('\n#print axioms '+visitor+'\n').encode()
run('final-full-audit-build','exec lake build MicroCFTA.Audit')
names=['MicroCFTA.SourceSynthesisCurrentProgramEagerOutputs.initial_runEager_canonical','MicroCFTA.SourceSynthesisCurrentProgramEagerOutputs.accepted_initial_prefix']
p=runtime/'eager-public-strict.lean';p.write_text((root/'lean/MicroCFTA/SourceSynthesisCurrentInitialEagerInvocation.lean').read_text()+''.join('\n#print axioms '+n+'\n' for n in names))
run('eager-public-strict','exec lake env lean -j1 -DwarningAsError=true '+shlex.quote(str(p)),2)
p=runtime/'final-public-imports.lean';p.write_text(''.join('import MicroCFTA.'+m+'\n' for m in expected)+''.join('\n#check @'+n+'\n#print axioms '+n+'\n' for n in [visitor]+names))
run('final-public-imports','exec lake env lean -j1 -DwarningAsError=true '+shlex.quote(str(p)),3)
p=runtime/'final-Audit.lean';p.write_bytes((root/'lean/MicroCFTA/Audit.lean').read_bytes())
run('final-full-audit-strict','exec lake env lean -j1 -DwarningAsError=true '+shlex.quote(str(p)),1)
counts=re.findall(r'Checked axiom dependencies of (\d+) MicroCFTA theorems',(runtime/'final-full-audit-strict.txt').read_text());assert len(counts)==1 and int(counts[0])>95033
assert snapshot()==before
report={'at':datetime.datetime.now().astimezone().isoformat(),'limits':limits,'live_modules':len(before.splitlines()),'audit_imports':sum(s.startswith('import ') for s in p.read_text().splitlines()),'audited_theorems':int(counts[0]),'source_tree_sha256':sha(before.encode()),'checks':checks,'reused_checked_sources_unchanged':['public-visitor277'],'prior_live_sources_unchanged_except_Audit':len(baseline),'haskell_changes':False,'joint_completion_proved':False,'default_Haskell_entry_correspondence_proved':False}
(runtime/'final-checked.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
