from pathlib import Path
import ast
import datetime
import hashlib
import json
import shlex
import subprocess

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
base = root / 'lean/restart-evidence'
old_builder = base / '20261115-real-prefix-and-opaque-resources-checkpoint-work/prepare-consumer.py'
builder = work / 'prepare-consumer-unique.py'
text = old_builder.read_text()
needle = "jobs.append((folder, command, probe.read_text().count('#print axioms ')))"
assert text.count(needle) == 1
text = text.replace(needle, "jobs.append((str(index) + '-' + folder, command, probe.read_text().count('#print axioms ')))")
builder.write_text(text)
collision = {'at':datetime.datetime.now().astimezone().isoformat(), 'session':34657,
    'run':'20261116-native-identity-components-and-types-check',
    'cause':'Two specs in the same folder used the same log name.',
    'lost':'The first APPEND96 failure log was overwritten by TYPE-ONLY output.',
    'retained':'Both exact candidate copies, driver, pins and terminal check summaries remain.',
    'type_only_terminal_exit':0,'component_terminal_exit':1,
    'recovery':'Repeat only APPEND96 with a unique job label; do not repeat the passed type-only job.'}
(work / 'diagnostic-log-collision.json').write_text(json.dumps(collision,indent=2)+'\n')
run = base / '20261116-native-small-identity-and-real-callback-check'
subprocess.run(['python3',str(builder),'--run',run.name,'--spec',
    '20261116-current-any-budget-identity-targeted-diagnostics:APPEND.lean.txt:COMPONENT-PROBES.lean.txt'],check=True)
driver = run / 'check.py'
text = driver.read_text(); start = text.index('jobs = '); end = text.index('\nfor name, command, count in jobs:',start)
jobs = ast.literal_eval(text[start+len('jobs = '):end])
parts = shlex.split(jobs[1][1]); objects = Path(parts[parts.index('-o')+1]).parents[2]
callback = base / '20261116-current-real-worker-callback-induction-draft'
name = 'SourcePruningEnumerationRealWorkerCallbackResources.lean'
assert hashlib.sha256((callback / name).read_bytes()).hexdigest() == 'd8ca646e1602b09e7b1640329fac02b011a4bcc7f485ecdc64240e74cb2de52f'
source = run / 'callback-source/MicroCFTA' / name
source.parent.mkdir(parents=True)
source.write_bytes((callback / name).read_bytes()+b'\n'+(callback / 'PROBES.lean.txt').read_bytes())
modules = [line.split()[1] for line in (callback / name).read_text().splitlines() if line.startswith('import ')]
jobs[0] = (jobs[0][0],jobs[0][1]+''.join(' '+shlex.quote(m) for m in modules),0)
command = 'exec lake env lean -j1 -DwarningAsError=true -R '+shlex.quote(str(source.parent.parent))
command += ' -o '+shlex.quote(str(objects / 'RealCallback.olean'))+' '+shlex.quote(str(source))
jobs.append(('real-callback',command,(callback / 'PROBES.lean.txt').read_text().count('#print axioms ')))
assert len({name for name,_,_ in jobs}) == len(jobs)
driver.write_text(text[:start]+'jobs = '+repr(jobs)+text[end:])
pins = json.loads((run / 'source-pins.json').read_text())
for p in [Path(__file__),callback / name,callback / 'PROBES.lean.txt',source,driver]:
    pins[str(p.relative_to(root))] = hashlib.sha256(p.read_bytes()).hexdigest()
(run / 'source-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
(run / 'objects.json').write_text(json.dumps({'path':str(objects)},indent=2)+'\n')
print(json.dumps({'jobs':len(jobs),'unique_job_names':True,'component_reports':jobs[1][2],
    'callback_reports':jobs[2][2],'objects':str(objects)}))
