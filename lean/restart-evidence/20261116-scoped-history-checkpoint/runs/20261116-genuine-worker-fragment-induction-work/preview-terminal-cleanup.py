from pathlib import Path
import datetime
import json
import os
import subprocess

work = Path(__file__).parent
specs = [(42761, 1, '/tmp/mcfta-residual-finalize-history-sknc8pf_', '20261116-residual-finalize-history-check'), (23874, 0, '/tmp/mcfta-residual-finalize-history-syntax-repair-s6h0vsnw', '20261116-residual-finalize-history-syntax-repair-check'), (14632, 1, '/tmp/mcfta-genuine-fragment-task-components-5yo35120', '20261116-genuine-fragment-task-components-check'), (68707, 1, '/tmp/mcfta-genuine-fragment-expanded-components-9c__j7r_', '20261116-genuine-fragment-expanded-components-check'), (89134, 1, '/tmp/mcfta-genuine-history-base-and-row-b5f2raoy', '20261116-genuine-history-base-and-row-check'), (43169, 1, '/tmp/mcfta-genuine-history-resource-and-finalize-fre2w_as', '20261116-genuine-history-resource-and-finalize-check'), (98737, 1, '/tmp/mcfta-genuine-history-local-producers-r_4myaqi', '20261116-genuine-history-local-producers-check')]
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
