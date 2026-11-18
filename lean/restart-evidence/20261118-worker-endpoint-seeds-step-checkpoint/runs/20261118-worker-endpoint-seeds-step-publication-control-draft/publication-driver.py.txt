from pathlib import Path
import datetime
import hashlib
import json
import os
import re
import shlex
import subprocess

ROOT = Path('/home/tritlo/Code/mcfta')
RUNTIME = Path(__file__).resolve().parent
pins = json.loads((RUNTIME/'source-pins.json').read_text())
selection = json.loads((RUNTIME/'INHERITANCE-SELECTION.json').read_text())
checks,limits,failure = [],{},None


def verify_pins():
    for name,digest in pins.items():
        assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest,name


def run(name,command,reports):
    verify_pins()
    (RUNTIME/'running.json').write_text(json.dumps({'name':name,'at':datetime.datetime.now().astimezone().isoformat()})+'\n')
    environment = dict(os.environ)
    environment.pop('LEAN_SYSROOT',None)
    environment['LEAN_NUM_THREADS'] = '1'
    path = RUNTIME/(name+'.txt')
    with path.open('w') as log:
        result = subprocess.run(['nix-shell',str(ROOT/'shell.nix'),'--run',command],cwd=ROOT/'lean',env=environment,
            stdout=log,stderr=subprocess.STDOUT,text=True)
    output = path.read_text()
    groups = [set(item.strip() for item in group.split(',') if item.strip())
        for group in re.findall(r'depends on axioms:\s*\[([^]]*)\]',output,re.S)]
    free = len(re.findall(r'does not depend on any axioms',output))
    bad = sorted(set().union(*groups)-{'propext','Classical.choice','Quot.sound'}) if groups else []
    definition_counts = {}
    item = {'name':name,'exit':result.returncode,'axiom_groups':len(groups),'axiom_free_reports':free,
        'total_axiom_reports':len(groups)+free,'nonstandard_axioms':bad,
        'diagnostics':len(re.findall(r': error(?:\(|:)',output)),'sorryAx':'sorryAx' in output,
        'declaration_checks':0,'definition_checks_by_qname':definition_counts,'expected_reports':reports}
    checks.append(item)
    (RUNTIME/'checks.json').write_text(json.dumps(checks,indent=2)+'\n')
    print(json.dumps(item),flush=True)
    verify_pins()


jobs = [
    ('public-build','exec lake build',746),
    ('strict-new-components-and-prior-bindings','exec python3 '+shlex.quote(str(RUNTIME/'strict-new-and-bind.py')),5),
    ('independent-imports','exec lake env lean -j1 -DwarningAsError=true '+shlex.quote(str(RUNTIME/'IndependentProbes.lean')),341),
    ('audit-build','exec lake build MicroCFTA.Audit',746),
    ('audit-strict','exec lake env lean -j1 -DwarningAsError=true MicroCFTA/Audit.lean',746),
]
try:
    assert not (RUNTIME/'checked.json').exists()
    group = next(line.split(':',2)[2] for line in Path('/proc/self/cgroup').read_text().splitlines() if line.startswith('0::'))
    cgroup = Path('/sys/fs/cgroup')/group.lstrip('/')
    limits = {name:(cgroup/name).read_text().strip() for name in ['memory.max','memory.high','memory.swap.max']}
    assert limits == {'memory.max':'8589934592','memory.high':'8589934592','memory.swap.max':'0'}
    for name,command,reports in jobs:
        run(name,command,reports)
    assert len(checks) == 5
    assert all(item['exit'] == 0 and not item['diagnostics'] and not item['sorryAx'] and not item['nonstandard_axioms']
        and item['total_axiom_reports'] == job[2] for item,job in zip(checks,jobs))
    assert [item['declaration_checks'] for item in checks] == [0,0,0,0,0]
    assert checks[1]['axiom_groups'] == selection['fresh_axiom_groups']
    assert checks[1]['axiom_free_reports'] == selection['fresh_axiom_free_reports']
    assert checks[2]['axiom_groups'] == selection['independent_axiom_groups']
    assert checks[2]['axiom_free_reports'] == selection['independent_axiom_free_reports']
    for index in [0,3,4]:
        assert checks[index]['axiom_groups'] == selection['audit_axiom_groups']
        assert checks[index]['axiom_free_reports'] == selection['audit_axiom_free_reports']
    match = re.search(r'Checked axiom dependencies of (\d+) MicroCFTA theorems\.',(RUNTIME/'audit-strict.txt').read_text())
    assert match
    verify_pins()
except Exception as error:
    failure = {'type':type(error).__name__,'message':str(error)}
if failure is not None:
    rejected = {'at':datetime.datetime.now().astimezone().isoformat(),'checks':checks,'limits':limits,'failure':failure,
        'all_five_gates_passed':False,'proof_credit':False,'credited_public_reports':0,'credited_private_reports':0,'published':False}
    (RUNTIME/'results.json').write_text(json.dumps(rejected,indent=2)+'\n')
    print(json.dumps(rejected),flush=True)
    raise SystemExit(1)
report = json.loads((RUNTIME/'REPORT-BASE.json').read_text())
report.update(checks=checks,limits=limits,at=datetime.datetime.now().astimezone().isoformat(),
    audited_theorems=int(match.group(1)),all_five_gates_passed=True,source_pins_unchanged=True,
    actual_private_session=selection['actual_private_session'],fresh_classification={
        'axiom_groups':checks[1]['axiom_groups'],'axiom_free_reports':checks[1]['axiom_free_reports']})
(RUNTIME/'results.json').write_text(json.dumps(report,indent=2)+'\n')
(RUNTIME/'checked.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report),flush=True)
