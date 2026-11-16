from pathlib import Path
import datetime
import json
import os
import subprocess

work = Path(__file__).parent
specs = [(78990, 1, '/tmp/mcfta-full-none-domain-parked-vto_zl3a', '20261116-full-none-domain-origin-eager-parked-check'), (6360, 0, '/tmp/mcfta-issued-domain-projection-69_eb7ap', '20261116-issued-domain-empty-projection-check'), (62133, 1, '/tmp/mcfta-full-none-universe-match-3utmu3c_', '20261116-full-none-universe-match-check'), (50936, 0, '/tmp/mcfta-full-none-option-append-cbhchoo_', '20261116-full-none-option-append-check'), (36974, 0, '/tmp/mcfta-eager-history-publication-umuy26gw', '20261116-eager-history-invariants-publication'), (7355, 1, '/tmp/mcfta-source-native-warm-parked-my1t819b', '20261116-source-native-none-warm-parked-witness-check'), (93873, 1, '/tmp/mcfta-parked-arrow-frame-scope-cxd9jsyn', '20261116-parked-arrow-frame-scope-repair-check'), (59881, 1, '/tmp/mcfta-source-rendering-parked-qhbimbs0', '20261116-real-source-rendering-parked-bucket-witness-check'), (11755, 1, '/tmp/mcfta-parked-witness-warm-owners-1267dcjk', '20261116-parked-bucket-witness-and-warm-origin-owner-check'), (34204, 0, '/tmp/mcfta-warm-origin-owner-probes-tawzz8wa', '20261116-warm-origin-owner-correct-probes-check'), (19411, 0, '/tmp/mcfta-warm-return-admission-5godr9xk', '20261116-stored-dispatch-warm-return-admission-check')]
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
