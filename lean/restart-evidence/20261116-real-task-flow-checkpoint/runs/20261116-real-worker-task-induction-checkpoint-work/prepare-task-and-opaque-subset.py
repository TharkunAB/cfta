from pathlib import Path
import hashlib
import json
import subprocess

root=Path('/home/tritlo/Code/mcfta')
base=root/'lean/restart-evidence'
work=Path(__file__).parent
rows=base/'20261116-current-real-actual-source-rows-plan-and-helper-repair'
core=base/'20261116-current-real-worker-task-core-local-opacity-repair'
opaque=base/'20261116-current-real-opaque-prepared-typing-repair'
core_data=(core/'APPEND-CORE.lean.txt').read_text()
cut=core_data.index('private theorem real_actual_prepared_scan_prefixes_at_any_budget')
doc=core_data.rfind('/--',0,cut)
if doc>=0 and core_data[doc:cut].count('-/')==1:cut=doc
prefix=core_data[:cut]
assert prefix.count('private theorem ')==5
prefix+='\nend RealWorkerTaskAndRootAssembly\nend MicroCFTA.SourcePruningEnumerationSharedEagerReservation\n'
(work/'CORE-FIRST-FIVE.lean.txt').write_text(prefix)
raws=[(rows/'APPEND.lean.txt').read_bytes(),prefix.encode(),(opaque/'OPAQUE-APPEND.lean.txt').read_bytes()]
core_probes=(core/'PROBES-CORE.lean.txt').read_bytes().splitlines(keepends=True)
core_probes=b''.join(x for x in core_probes if b'real_actual_prepared_scan_prefixes_at_any_budget' not in x)
probes=[(work/'TaskRepair105Probes.lean.txt').read_bytes(),(rows/'PROBES.lean.txt').read_bytes(),core_probes,(opaque/'OPAQUE-PROBE-APPEND.lean.txt').read_bytes()]
(work/'ROWS-TASK-OPAQUE-APPEND.lean.txt').write_bytes(b'\n'.join(raws))
(work/'Task123Probes.lean.txt').write_bytes(b'\n'.join(probes))
assert (work/'Task123Probes.lean.txt').read_bytes().count(b'#print axioms ')==123
builder=base/'20261116-real-prefix-all-outcome-checkpoint-work/prepare-consumer-unique.py'
run=base/'20261116-native-real-task-and-opaque-subset-check'
subprocess.run(['python3',str(builder),'--run',run.name,'--spec',
    work.name+':ROWS-TASK-OPAQUE-APPEND.lean.txt:Task123Probes.lean.txt'],check=True)
pins=json.loads((run/'source-pins.json').read_text())
for p in [Path(__file__),rows/'APPEND.lean.txt',rows/'PROBES.lean.txt',core/'APPEND-CORE.lean.txt',
    core/'PROBES-CORE.lean.txt',opaque/'OPAQUE-APPEND.lean.txt',opaque/'OPAQUE-PROBE-APPEND.lean.txt',work/'CORE-FIRST-FIVE.lean.txt']:
    pins[str(p.relative_to(root))]=hashlib.sha256(p.read_bytes()).hexdigest()
(run/'source-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
(work/'SUBSET-LAYOUT.json').write_text(json.dumps({'retained_owner_probes':105,'rows_probes':12,
    'genuine_task_and_captured_startup_probes':5,'actual_opaque_probe':1,'total_probes':123,
    'retained_theorem_headers_and_proof_bytes_unchanged':True,
    'full_prepared_scan_and_two_dependent_bridge_declarations_excluded':True,
    'full_worker_public_target_5493_unchanged_and_unproved':True},indent=2)+'\n')
