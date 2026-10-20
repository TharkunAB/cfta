import json,shutil
from pathlib import Path
root=Path('/home/tritlo/Code/mcfta')
here=root/'lean/restart-evidence/20261020-native-original-captured-node-rows'
assert not (here/'next-generated-capture').exists()
shutil.copytree('/tmp/mcfta-native-generated-capture-next-plan',here/'next-generated-capture')
item=dict(path='next-generated-capture/plan-verify.py',arguments=['--live','--root',str(root)])
p=here/'component-verifiers.json'
data=json.loads(p.read_text());data.append(item);p.write_text(json.dumps(data,indent=2)+'\n')
p=here/'prepare-metadata.py';s=p.read_text();anchor='unique={};diagnostics={}'
assert s.count(anchor)==1
s=s.replace(anchor,"verifiers=read('component-verifiers.json');verifiers.append("+repr(item)+");write('component-verifiers.json',verifiers)\n"+anchor)
p.write_text(s)
addition='''
## Exact next contract

Read next-generated-capture/plan.md in this evidence folder. The design
is unproved. It proposes one generated-row consumer that fixes Observed
before all rows. It derives the same raw row's node, binder or capture
terminal. An actual row-bearing full-Mu capture keeps its original input
slot and calls capture_node_rows at the actual earlier native prefix.
The same stored row can then retain an original node call or a strictly
earlier generated receipt. The active source Path differs from the
issued publication Path. Non-Mu captures, warm prior cells, self
replacement and residual observations remain explicit open cases.
This design adds no checked theorem, example or Lean command.
'''
p=root/'lean/notes-current-native-original-captured-node-rows.md'
p.write_text(p.read_text()+addition)
p=here/'write-current-documents.py';s=p.read_text();anchor="(ROOT/'lean/notes-current-native-original-captured-node-rows.md').write_text(note)"
assert s.count(anchor)==1;s=s.replace(anchor,'note += '+repr(addition)+'\n'+anchor);p.write_text(s)
print(json.dumps({'status':'PASS','archived_design':'next-generated-capture','owned_lean_jobs':0}))
