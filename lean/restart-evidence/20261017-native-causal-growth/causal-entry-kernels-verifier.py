from pathlib import Path
import hashlib,json,re
ROOT=Path('/home/tritlo/Code/mcfta')
HERE=Path(__file__).resolve().parent
manifest=json.loads((HERE/'causal-entry-kernels-manifest.json').read_text())
for entry in manifest['entries']:
    data=(ROOT/entry['path']).read_bytes()
    assert len(data)==entry['bytes'],entry['path']
    assert hashlib.sha256(data).hexdigest()==entry['sha256'],entry['path']
stem='causal-entry-kernels-1'
record=json.loads((HERE/(stem+'.json')).read_text())
assert record['exit_code']==0
source=(HERE/record['source']).read_text()
log=(HERE/record['log']).read_text()
assert hashlib.sha256(source.encode()).hexdigest()==record['sha256']
assert record['command'][-1]==str(HERE/record['source'])
assert '-Dlinter.all=true' in record['command']
assert json.loads((HERE/record['limits']).read_text())=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
assert not re.search(r'\b(?:error|warning)(?:\(|:)|sorryAx|\bsorry\b|failed to pretty print',log,re.I)
for setting in ['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']:
    assert 'set_option '+setting in source,setting
names=re.findall(r'^#check @([^\s]+)',source,re.M)
assert len(names)==1
assert re.findall(r'^#print (?!axioms )([^\s]+)',source,re.M)==names
assert re.findall(r'^#print axioms ([^\s]+)',source,re.M)==names
results=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S)
assert len(results)==1 and results[0][0]==names[0]
assert {re.sub(r'\.\{[^}]*\}','',name.strip()) for name in results[0][1].split(',')}=={'propext','Classical.choice','Quot.sound'}
assert (HERE/'causal-entry-kernels.lean').read_bytes()==(HERE/(stem+'.source.lean')).read_bytes()
assert (ROOT/'lean/MicroCFTA/SourceCurrentNativeCausalEntry.lean').read_bytes()==(HERE/'causal-entry-direct-2.source.lean').read_bytes()
assert not (HERE/'causal-entry-direct-2.log').read_bytes()
assert json.loads((HERE/'causal-entry-canonical-1.json').read_text())['exit_code']==0
assert 'Build completed successfully' in (HERE/'causal-entry-canonical-1.log').read_text()
print(f'PASS {len(manifest["entries"])} immutable entries; one initial-only conjunction integration pair; std3/eightoptions/fullprinting/actual4GiB4GiBzeroSwap')
