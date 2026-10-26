from pathlib import Path
import hashlib,json,re,subprocess
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-recursive-callback-one-20261026')
finals=json.loads((area/'final-strict.json').read_text())
for module,check in finals.items():
    data=(root/'lean/MicroCFTA'/f'{module}.lean').read_bytes(); report=json.loads((area/check/'report.json').read_text())
    assert report['exit_code']==0 and report['source_sha256']==hashlib.sha256(data).hexdigest(), module
    if module!='Audit':assert (area/check/'raw.log').read_bytes()==b''
    assert data.endswith(b'\n') and not data.endswith(b'\n\n') and all(line.rstrip()==line for line in data.splitlines()),module
for path in sorted(area.rglob('report.json')):
    if path.parent.name=='contract-evidence':continue
    report=json.loads(path.read_text()); raw=(path.parent/'raw.log').read_bytes()
    assert len(raw)==report['bytes'] and hashlib.sha256(raw).hexdigest()==report['sha256'],path
    cap='8589934592' if report['command'][0]=='nix-shell' and 'cabal test' in report['command'][-1] else '4294967296'
    assert report['cgroup_limits']=={'memory.max':cap,'memory.high':cap,'memory.swap.max':'0'},path
for check in ['install-suspended-mass-1','aggregate-audit-1','public-final-1']:
    assert json.loads((area/check/'report.json').read_text())['exit_code']==0,check
raw=(area/'public-final-1/raw.log').read_text();decls=json.loads((area/'public-declarations.json').read_text())
assert len(decls)==11 and raw.count('depends on axioms:')+raw.count('does not depend on any axioms')==11
assert len(re.findall(r'^(?:def|structure) MicroCFTA\.',raw,re.M))==12
assert not re.search(r'\b(?:sorryAx|sorry|admit|native_decide)\b',raw)
assert '⋯' not in raw and '...' not in raw
for axioms in re.findall(r'depends on axioms: \[([^\]]*)\]',raw):
    assert set(x.strip() for x in axioms.split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'}
assert '77474' in (area/'strict-audit-1/raw.log').read_text()
assert '3850 jobs' in (area/'aggregate-audit-1/raw.log').read_text()
base=(area/'base.txt').read_text().strip();git=lambda *args:subprocess.check_output(['git',*args],cwd=root)
assert not git('diff',base,'--','cfta','specftacular','specftacular-ghc')
h6='lean/MicroCFTA/SourceCurrentColdFiniteWarmCalls.lean'
assert git('show',base+':'+h6)==(root/h6).read_bytes()
assert hashlib.sha256((root/h6).read_bytes()).hexdigest()=='e4665b0bb522ec88f1925fe6bc360b76e9e4bdfbe6192210ac708a3097a20cc5'
audit=(root/'lean/MicroCFTA/Audit.lean').read_text()
for line in ['import MicroCFTA.SourcePruningEnumerationCallbackOneResources\n','import MicroCFTA.SourcePruningEnumerationSubtreeEffects\n']:
    assert audit.count(line)==1;audit=audit.replace(line,'',1)
assert audit.encode()==(area/'Audit-before.lean').read_bytes()
summary={'strict_sources':len(finals),'public_declarations':len(decls),'full_definitions':12,'public_lines':len(raw.splitlines()),'public_bytes':len(raw.encode()),'public_sha256':hashlib.sha256(raw.encode()).hexdigest(),'audited_theorems':77474,'aggregate_jobs':3850}
(area/'verified-checks.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))

upstream=area/'upstream-integration'
integration=json.loads((upstream/'integration.json').read_text())
assert integration['merge']==base and integration['main']==(area/'main.txt').read_text().strip()
assert not git('diff',integration['base'],base,'--','lean')
assert set(git('diff','--name-only',integration['base'],base).decode().splitlines())=={'cfta/src/Data/CFTA/Template.hs','cfta/CHANGELOG.md'}
for name in ['templates-native-2','format-1','aggregate-audit-1']:
    assert json.loads((upstream/name/'report.json').read_text())['exit_code']==0
native=(upstream/'templates-native-2/raw.log').read_text()
assert '26 examples, 0 failures' in native and native.count('+++ OK, passed 100 tests')==14
assert '0 examples, 0 failures' in (upstream/'templates-native-1/raw.log').read_text()
assert 'CLEAR' in (upstream/'review-main.txt').read_text()
for rel in ['cfta/src/Data/CFTA/Template.hs','cfta-generator/src/Data/CFTA/Sized.hs','cfta-generator/CHANGELOG.md']:
    assert git('show',integration['main']+':'+rel)==(root/rel).read_bytes()
for rel in ['cfta-generator/src/Data/CFTA/Sized.hs','cfta-generator/CHANGELOG.md']:
    assert git('show','af6369a9e0ecd70acf4da1dffec45c32e6ce7b7b:'+rel)==(root/rel).read_bytes()
assert (upstream/'Template.hs').read_bytes()==(root/'cfta/src/Data/CFTA/Template.hs').read_bytes()
print('Upstream source identity, merge preservation, actual native tests and pending repair integration verified.')
