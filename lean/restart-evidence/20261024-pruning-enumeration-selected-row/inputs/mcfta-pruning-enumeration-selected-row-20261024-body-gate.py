import hashlib
import json
import re
from datetime import datetime
from pathlib import Path
from zoneinfo import ZoneInfo

prefix = Path('/tmp/mcfta-pruning-enumeration-selected-row-20261024')
owner = Path(str(prefix) + '-proposal')
root = Path('/home/tritlo/Code/mcfta')

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def load(name):
    return json.loads((owner / name).read_text())

frozen = load('FROZEN.json')
pins = load('pins.json')
assert sha(owner / 'FROZEN.json') == 'e7755ad1b228886e39988e67fe7fe2b9934e5165ab801357f4d83de66e3cea92'
assert sha(owner / 'pins.json') == frozen['pins_sha256'] == 'b29c9ec6b2088f3edd2332828ddebd84ca8bd815fed76c2ccaadaec6c4ce6ce6'
assert len(pins) == 90 and (owner / 'pins.json').stat().st_size == frozen['pins_bytes']
assert {p.relative_to(owner).as_posix() for p in owner.rglob('*') if p.is_file()} == set(pins) | {'pins.json', 'FROZEN.json'}
for name, pin in pins.items():
    assert not Path(name).is_absolute() and '..' not in Path(name).parts
    path = owner / name
    assert not path.is_symlink() and path.stat().st_size == pin['bytes'] and sha(path) == pin['sha256']
contracts = load('contracts.json')
assert len(contracts) == 14 and sum(len(s.splitlines()) for s in contracts.values()) == 156
for name, literal in contracts.items():
    assert isinstance(literal, str) and (owner / name).read_text() == literal
assert len(load('scoped-types.json')['entries']) == 143
packets = load('obtain-inventory.json')['packets']
assert len(packets) == 4 and sum(len(p['fields']) for p in packets) == 43
assert load('induction.json')['induction_count'] == 0
sources = load('source-index.json')['sources']
cut_count = cut_lines = 0
for source in sources:
    path = Path(source['path'])
    data = path.read_bytes()
    assert data == (owner / source['snapshot']).read_bytes()
    assert len(data) == source['bytes'] and sha(path) == source['sha256']
    for cut in source['cuts']:
        assert 1 <= cut['start'] <= cut['end'] <= len(data.splitlines())
        part = b''.join(data.splitlines(keepends=True)[cut['start'] - 1:cut['end']])
        assert part == (owner / cut['snapshot']).read_bytes()
        assert len(part) == cut['bytes'] and hashlib.sha256(part).hexdigest() == cut['sha256']
        cut_count += 1
        cut_lines += len(part.splitlines())
routes = load('import-routes.json')
for source in routes['defining_import_sources']:
    path = Path(source['path'])
    assert path.stat().st_size == source['bytes'] and sha(path) == source['sha256']
edges = []
for route in routes['routes'] + routes['existing_instance_routes']:
    modules = route['route']
    assert modules[0] in routes['direct_imports']
    for first, second in zip(modules, modules[1:]):
        text = (root / 'lean' / (first.replace('.', '/') + '.lean')).read_text()
        assert second in re.findall(r'^import (\S+)', text, re.M), (first, second)
        edges.append((first, second))
assert (len(sources), cut_count, cut_lines, len(routes['defining_import_sources']), len(edges), len(set(edges))) == (21, 36, 577, 45, 82, 42)
source_review = Path(str(prefix) + '-source-review.md')
review = Path(str(prefix) + '-declaration-review.md')
script_review = Path(str(prefix) + '-seal-script-review.md')
assert sha(source_review) == '8d0c96a5886f6397d60f85c73ccf22b4845a873fe358e88339bfba02f62c2ad7'
assert sha(review) == '2c469158f26db42d5f5c2b51edf4b099407bab74da0ab1cbe9d84a98c2b0d05f'
assert script_review.is_file()
destination = prefix / 'body-gate.json'
assert not destination.exists()
report = dict(status='ROOT_EXACT_SOURCE_BODY_GATE_PASS',
    recorded_at=datetime.now(ZoneInfo('Europe/Stockholm')).isoformat(),
    body_or_compiler_started=False, owner=str(owner), frozen_sha256=sha(owner / 'FROZEN.json'),
    pins_sha256=sha(owner / 'pins.json'), contracts=contracts,
    review_sha256=sha(review), source_review_sha256=sha(source_review),
    seal_script_review_sha256=sha(script_review), sources_live_checked=21,
    cuts_live_checked=36, cut_lines=577, defining_import_sources=45,
    adjacent_import_occurrences=82, adjacent_imports_unique=42,
    root_full_read=['all14 literal contracts156lines', 'all143 scoped types',
        'four obtains43fields and all inline API facts',
        'two case families/seven actual equations and full constructor binders',
        'schema/insertion/scope/budget/proof-route/provenance/self-review',
        'all36 cuts577lines and21 live source identities',
        '20 routes plus existing instance route and45 defining identities',
        'complete source/exact-declaration/adapter/final script reports',
        'all five465line scripts and both complete document templates'],
    hard_cap=260, new_local_instances=0, new_global_instances=0,
    new_helpers=0, new_types=0, induction_count=0, goal='ACTIVE_INCOMPLETE',
    boundary='Same actual selected checked row, genuine intervening native history and computed parent endpoint. Derived acceptance and own projection. Inherited arity remains an independent input. Direct ordered traversal reuse keeps exact unsupported-prefix and residual states. Universal resident origin and terminal native workers remain open.')
destination.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(dict(status=report['status'], sha256=sha(destination), recorded_at=report['recorded_at'])))
