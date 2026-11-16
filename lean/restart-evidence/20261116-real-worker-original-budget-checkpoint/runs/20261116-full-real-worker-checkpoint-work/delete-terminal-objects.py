from pathlib import Path
import datetime,json,shutil,subprocess,sys
work=Path(__file__).parent
p=work/'terminal-cleanup-preview.json'
before=json.loads(p.read_text())
subprocess.run([sys.executable,str(work/'preview-terminal-cleanup.py')],check=True)
fresh=json.loads(p.read_text())
assert [(x['path'],x['bytes'],x['files']) for x in before['items']]==[(x['path'],x['bytes'],x['files']) for x in fresh['items']]
removed=[]
for item in fresh['items']:
 path=Path(item['path']);assert not item['live_matches']
 if path.exists():shutil.rmtree(path)
 assert not path.exists();removed.append(item)
result={'at':datetime.datetime.now().astimezone().isoformat(),'removed':removed,'bytes':sum(x['bytes'] for x in removed),'known_cumulative_bytes_removed':807500928+sum(x['bytes'] for x in removed),'sources_and_logs_preserved':True,'public_lake_and_unknown_entries_preserved':True}
(work/'terminal-cleanup-result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
