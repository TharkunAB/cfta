from pathlib import Path
import json,os,subprocess,shutil,datetime
w=Path(__file__).parent;preview=json.loads((w/'terminal-cleanup-preview.json').read_text());assert preview['bytes']==158494408
rows=[s.strip().split(None,2) for s in subprocess.check_output(['ps','-eo','pid=,ppid=,args='],text=True).splitlines() if s.strip()];parents={int(x[0]):int(x[1]) for x in rows};ancestors=set();pid=os.getpid()
while pid and pid not in ancestors:ancestors.add(pid);pid=parents.get(pid,0)
for item in preview['items']:
 p=Path(item['path']);assert p.is_absolute() and str(p).startswith('/tmp/mcfta-') and not p.is_symlink()
 assert not [x for x in rows if len(x)==3 and int(x[0]) not in ancestors and (str(p) in x[2] or item['run'] in x[2])]
 assert any(q.exists() and str(p) in q.read_text() for q in [w.parent/item['run']/'check.py',w.parent/item['run']/'strict-modules.py'])
 files=list(p.rglob('*'));assert not any(q.is_symlink() for q in files);objects=[q for q in files if q.is_file()];assert all(q.suffix in ['.olean','.ilean'] for q in objects);assert len(objects)==item['files'];assert sum(q.stat().st_size for q in objects)==item['bytes']
for item in preview['items']:
 p=Path(item['path']);shutil.rmtree(p);assert not p.exists()
result={'at':datetime.datetime.now().astimezone().isoformat(),'removed_bytes':preview['bytes'],'cumulative_removed_bytes':1751900240+preview['bytes'],'real_host_processes_rechecked':True,'only_verified_terminal_olean_ilean_removed':True,'all_sources_logs_public_lake_live_and_unknown_entries_preserved':True,'free_bytes':shutil.disk_usage('/tmp').free};(w/'terminal-cleanup-result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
