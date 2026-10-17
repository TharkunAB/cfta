from pathlib import Path
import hashlib, json, re
root=Path(__file__).resolve().parents[3]
base=Path(__file__).resolve().parent
source=root/'lean/MicroCFTA/SourceCurrentAllocatedNativeWidthTrace.lean'
assert hashlib.sha256(source.read_bytes()).hexdigest()=='15f065e754fb0bc0a9bff8fc906e0a6a8e85813ab5f72d176ccc197abee6e677'
assert source.read_bytes()==(base/'width-trace-direct-3.source.lean').read_bytes()
assert (base/'width-trace-direct-3.log').read_bytes()==b''
assert (base/'root-strict-SourceCurrentAllocatedNativeWidthTrace.log').read_bytes()==b''
names=re.findall(r'^theorem ([^\s({:]+)', source.read_text(), re.M)
assert len(names)==7
public=(base/'width-trace-review-public.lean').read_text()
for name in names:
    full='MicroCFTA.SourceCurrentAllocatedNativeWidthTrace.'+name
    assert '#print axioms '+full+'\n' in public and '#check @'+full+'\n' in public
for stem,attempt,pairs in [('width-trace-review-public',1,7),('width-trace-review-kernels',8,2)]:
    path=base/(stem+'.lean')
    assert path.read_bytes()==(base/(stem+'-'+str(attempt)+'.source.lean')).read_bytes()
    text=path.read_text()
    assert text.count('#print axioms ')==pairs and text.count('#check @')==pairs
    for opt in ['explicit','fullNames','proofs','universes','deepTerms']:
        assert 'set_option pp.'+opt+' true\n' in text
    assert 'set_option pp.maxSteps 10000000\n' in text and 'set_option linter.all true\n' in text
    log=(base/(stem+'-'+str(attempt)+'.log')).read_text()
    assert not re.search(r'error(?:\(|:)|warning:|sorryAx', log)
    assert len(re.findall(r'depends on axioms:|does not depend on any axioms',log))==pairs
    for group in re.findall(r'depends on axioms:\s*\[(.*?)\]', log, re.S):
        for axiom in group.split(','):
            assert re.sub(r'\.\{[^}]*\}', '', axiom.strip()) in {'propext','Classical.choice','Quot.sound'}
assert 'Build completed successfully (1217 jobs).' in (base/'canonical-width-trace-1.log').read_text()
for path in [source,base/'width-trace-review-public.lean',base/'width-trace-review-kernels.lean',base/'width-trace-review-note.md']:
    raw=path.read_bytes()
    assert raw.endswith(b'\n') and not raw.endswith(b'\n\n'), path
manifest=base/'width-trace-review-manifest.json'
if manifest.exists():
    data=json.loads(manifest.read_text())
    assert len(data['files'])==data['file_count']
    for item in data['files']:
        path=root/item['path']
        assert path.stat().st_size==item['bytes'], path
        assert hashlib.sha256(path.read_bytes()).hexdigest()==item['sha256'], path
print('PASS: WidthTrace frozen; 7 public and 2 actual cold/checked/warm integration pairs; standard axioms; canonical1217.')
