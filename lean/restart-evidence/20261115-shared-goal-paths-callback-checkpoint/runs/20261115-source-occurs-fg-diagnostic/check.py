from pathlib import Path
import datetime,hashlib,json,os,subprocess
root=Path('/home/tritlo/Code/mcfta');runtime=Path(__file__).parent
pins=json.loads((runtime/'source-pins.json').read_text())
def verify():
 for name,wanted in pins.items():assert hashlib.sha256((root/name).read_bytes()).hexdigest()==wanted,name
verify()
relative=next(line.split(':',2)[2] for line in Path('/proc/self/cgroup').read_text().splitlines() if line.startswith('0:'));cg=Path('/sys/fs/cgroup')/relative.lstrip('/');limits={name:(cg/name).read_text().strip() for name in ['memory.max','memory.high','memory.swap.max']};assert limits=={'memory.max':'8589934592','memory.high':'8589934592','memory.swap.max':'0'},limits
with (runtime/'probe.txt').open('w') as log:p=subprocess.run(['bash',str(runtime/'probe.sh')],cwd=root,stdout=log,stderr=subprocess.STDOUT)
verify();text=(runtime/'probe.txt').read_text();report={'at':datetime.datetime.now().astimezone().isoformat(),'exit':p.returncode,'limits':limits,'source_pins_unchanged':True,'executed_via_existing_cabal_package_artifacts':True,'fresh_binary_source_correspondence_established':False,'formal_counterexample_established':False,'haskell_application_source_changed':False};(runtime/'result.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report),flush=True);print(text[-16000:],flush=True)
raise SystemExit(p.returncode)
