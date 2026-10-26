from pathlib import Path
import hashlib,json,re,subprocess
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-enumeration-original-forecast-20261026')
finals=json.loads((area/'final-strict.json').read_text())
for module,check in finals.items():
    data=(root/'lean/MicroCFTA'/f'{module}.lean').read_bytes(); report=json.loads((area/check/'report.json').read_text())
    assert report['exit_code']==0 and report['source_sha256']==hashlib.sha256(data).hexdigest(), module
    assert data.endswith(b'\n') and not data.endswith(b'\n\n') and all(line.rstrip()==line for line in data.splitlines()),module
for path in sorted(area.glob('*/report.json')):
    if path.parent.name=='contract-evidence':continue
    report=json.loads(path.read_text()); raw=(path.parent/'raw.log').read_bytes()
    assert len(raw)==report['bytes'] and hashlib.sha256(raw).hexdigest()==report['sha256'],path
    assert report['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'},path
for check in ['install-width-cost-1','install-original-1','install-admission-ordinary-1','install-expansion-final-1','aggregate-audit-1','public-final-1']:
    assert json.loads((area/check/'report.json').read_text())['exit_code']==0,check
raw=(area/'public-final-1/raw.log').read_text();decls=json.loads((area/'public-declarations.json').read_text())
assert len(decls)==23 and raw.count('depends on axioms:')+raw.count('does not depend on any axioms')==23
assert len(re.findall(r'^(?:def|structure) MicroCFTA\.',raw,re.M))==19
assert not re.search(r'\b(?:sorryAx|sorry|admit|native_decide)\b',raw)
assert '⋯' not in raw and '...' not in raw
for axioms in re.findall(r'depends on axioms: \[([^\]]*)\]',raw):
    assert set(x.strip() for x in axioms.split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'}
assert '77397' in (area/'strict-audit-1/raw.log').read_text()
assert '3837 jobs' in (area/'aggregate-audit-1/raw.log').read_text()
base=(area/'base.txt').read_text().strip();git=lambda *args:subprocess.check_output(['git',*args],cwd=root)
assert not git('diff',base,'--','cfta','specftacular','specftacular-ghc')
h6='lean/MicroCFTA/SourceCurrentColdFiniteWarmCalls.lean'
assert git('show',base+':'+h6)==(root/h6).read_bytes()
assert hashlib.sha256((root/h6).read_bytes()).hexdigest()=='e4665b0bb522ec88f1925fe6bc360b76e9e4bdfbe6192210ac708a3097a20cc5'
audit=(root/'lean/MicroCFTA/Audit.lean').read_text()
for line in ['import MicroCFTA.SourcePruningEnumerationOrdinaryForecastResources\n','import MicroCFTA.SourcePruningEnumerationExpansionAdmission\n']:
    assert audit.count(line)==1;audit=audit.replace(line,'',1)
assert audit.encode()==(area/'Audit-before.lean').read_bytes()
summary={'strict_sources':len(finals),'public_declarations':len(decls),'full_definitions':19,'public_lines':len(raw.splitlines()),'public_bytes':len(raw.encode()),'public_sha256':hashlib.sha256(raw.encode()).hexdigest(),'audited_theorems':77397,'aggregate_jobs':3837}
(area/'verified-checks.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
