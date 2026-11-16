from pathlib import Path
import datetime
import json
import os
import subprocess

work = Path(__file__).parent
specs = [(86488, 1, '/tmp/mcfta-selected-prefix-union-normal-0ngk47wr', '20261116-native-selected-prefix-union-normal-check'), (85113, 1, '/tmp/mcfta-native-origin-invariants-i66ni6dj', '20261116-native-prefix-union-and-next-query-inner-laws-check'), (50530, 0, '/tmp/mcfta-native-origin-invariants-iz4_ouli', '20261116-native-prefix-union-and-next-query-repaired-check'), (74625, 0, '/tmp/mcfta-real-worker-task-publication-khmefmy0', '20261116-native-origin-invariants-publication'), (52102, 1, '/tmp/mcfta-selected-preparation-union-normal-v51jz7il', '20261116-native-selected-preparation-union-normal-check')]
rows = subprocess.check_output(['ps','-eo','pid=,ppid=,args='],text=True).splitlines()
processes = [line.strip().split(None,2) for line in rows if line.strip()]
parents = {int(row[0]):int(row[1]) for row in processes}
ancestors = set()
current = os.getpid()
while current and current not in ancestors:
    ancestors.add(current)
    current = parents.get(current,0)
items = []
for session, terminal_exit, name, run in specs:
    receipt_files = [work.parent / run / "check.py", work.parent / run / "strict-modules.py"]
    assert any(p.exists() and name in p.read_text() for p in receipt_files), name
    path = Path(name)
    assert path.is_absolute() and str(path).startswith('/tmp/mcfta-') and not path.is_symlink()
    live = [{'pid':int(row[0]),'args':row[2]} for row in processes if len(row)==3 and int(row[0]) not in ancestors and (name in row[2] or run in row[2])]
    assert not live, live
    files = list(path.rglob('*')) if path.exists() else []
    assert not any(p.is_symlink() for p in files)
    objects = [p for p in files if p.is_file()]
    assert all(p.suffix in ['.olean','.ilean'] for p in objects), objects
    items.append({'session':session,'terminal_exit':terminal_exit,'path':name,'run':run,
                  'bytes':sum(p.stat().st_size for p in objects),'files':len(objects),'live_matches':live})
report = {'at':datetime.datetime.now().astimezone().isoformat(),'host_processes_checked':True,
          'items':items,'bytes':sum(x['bytes'] for x in items),'preserve':'All sources, logs, live objects, public .lake and protected unknown tmp entries.'}
(work / 'terminal-cleanup-preview.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
