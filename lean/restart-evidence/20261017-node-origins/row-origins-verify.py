from pathlib import Path
import hashlib, json, re
ROOT = Path('/home/tritlo/Code/mcfta')
HERE = Path(__file__).resolve().parent
manifest = json.loads((HERE/'row-origins-manifest.json').read_text())
for entry in manifest['entries']:
    data = (ROOT/entry['path']).read_bytes()
    assert len(data) == entry['bytes'], entry
    assert hashlib.sha256(data).hexdigest() == entry['sha256'], entry
old = json.loads((HERE/'row-origins-WIP-manifest.json').read_text())
for entry in old['entries']:
    data = (ROOT/entry['path']).read_bytes()
    assert len(data) == entry['bytes'] and hashlib.sha256(data).hexdigest() == entry['sha256'], entry
for name in ['exposure-safe-direct-1','row-origins-direct-6','row-origins-kernel-strict-1']:
    metadata = json.loads((HERE/(name+'.json')).read_text())
    assert metadata['exit_code'] == 0
    assert not (HERE/(name+'.log')).read_bytes()
    data = (HERE/metadata['source']).read_bytes()
    assert hashlib.sha256(data).hexdigest() == metadata['source_sha256']
allowed = {'propext','Classical.choice','Quot.sound'}
counts = []
for name, expected in [('row-origins-public-2',34),('row-origins-kernels-4',1)]:
    source = (HERE/(name+'.source.lean')).read_text()
    log = (HERE/(name+'.log')).read_text()
    metadata = json.loads((HERE/(name+'.json')).read_text())
    assert metadata['exit_code'] == 0
    assert not re.search(r'\b(?:error|warning)(?:\(|:)|sorryAx',log)
    targets = re.findall(r'^#check @([^\s]+)',source,re.M)
    axiom_targets = re.findall(r'^#print axioms ([^\s]+)',source,re.M)
    print_targets = re.findall(r'^#print (?!axioms )([^\s]+)',source,re.M)
    assert len(targets) == len(set(targets)) == expected
    assert targets == axiom_targets == print_targets
    results = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|(does not depend on any axioms))",log,re.S)
    assert [r[0] for r in results] == targets
    for target, axioms, empty in results:
        for axiom in axioms.split(','):
            if axiom.strip():
                assert re.sub(r'\.\{[^}]*\}', '',axiom.strip()) in allowed, (target,axiom)
    counts.append(expected)
for name, jobs in [('exposure-safe-canonical-1',1080),('row-origins-canonical-1',1131)]:
    log = (HERE/(name+'.log')).read_text()
    assert log.startswith('4294967296\n4294967296\n0\n')
    assert f'Build completed successfully ({jobs} jobs).' in log
print(f'PASS {len(manifest["entries"])} entries; old WIP 14; public {counts[0]} + integration {counts[1]}; strict empty; standard axioms only')
