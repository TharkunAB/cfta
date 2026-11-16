from pathlib import Path
import datetime
import json
import os
import subprocess

work = Path(__file__).parent
specs = [(30934, 0, '/tmp/mcfta-real-isolated-o9tby7ha', '20261116-native-earlier-isolation-normalization-check'), (27428, 1, '/tmp/mcfta-prefix-readback-86zd53nj', '20261116-native-prefix-native-readback-check'), (94150, 0, '/tmp/mcfta-prefix-readback-s4hljlbf', '20261116-native-prefix-native-readback-bool-check'), (86845, 0, '/tmp/mcfta-callback-isolation-publication-9xmesc8g', '20261116-real-callback-and-isolation-publication'), (4603, 1, '/tmp/mcfta-private-proof-6lllwnw0/objects', '20261116-native-identity-verified-components-check'), (96985, 1, '/tmp/mcfta-real-nullary-m0_qpd_d', '20261116-native-real-nullary-captured-frame-check')]
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
(work / 'terminal-cleanup-second-preview.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
