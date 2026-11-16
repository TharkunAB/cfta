from pathlib import Path
import datetime
import json
import os
import subprocess

work = Path(__file__).parent
specs = [(51055, 1, '/tmp/mcfta-private-proof-vy3t8cjl/objects', '20261116-native-real-rows-task-core-and-bridges-check'), (12631, 1, '/tmp/mcfta-private-proof-u_mozo8k/objects', '20261116-native-real-rows-core-opacity-and-typing-check'), (45622, 0, '/tmp/mcfta-private-proof-wc197xw1/objects', '20261116-native-real-task-and-opaque-subset-check'), (24743, 1, '/tmp/mcfta-private-proof-cy09j_pt/objects', '20261116-native-whole-real-worker-original-budget-check'), (74959, 0, '/tmp/mcfta-real-worker-task-publication-qa7idak0', '20261116-real-worker-task-flow-publication'), (63305, 1, '/tmp/mcfta-private-proof-t86v4cqn/objects', '20261116-native-whole-real-worker-factored-scan-check'), (55777, 1, '/tmp/mcfta-private-proof-gy4q0jb7/objects', '20261116-native-whole-real-worker-4m-and-actual-dispatch-check')]
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
(work / 'post-task-terminal-cleanup-preview.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
