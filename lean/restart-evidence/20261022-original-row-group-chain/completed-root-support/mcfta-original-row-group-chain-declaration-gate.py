import datetime
import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = ROOT / 'lean/restart-evidence/20261022-original-row-group-chain'
components = ['signature-plan', 'signature-audit', 'checkpoint-preparation', 'checkpoint-audit']
counts = {}
for name in components:
    source = Path('/tmp/mcfta-original-row-group-chain-' + name)
    pins = json.loads((source / 'pins.json').read_text())
    for pin in pins:
        data = (source / pin['path']).read_bytes()
        assert len(data) == pin['bytes'], pin['path']
        assert hashlib.sha256(data).hexdigest() == pin['sha256'], pin['path']
    counts[name] = len(pins)
    subprocess.run(['/usr/bin/python3', str(HERE / 'archive-extra.py'), str(source), name], check=True)

plan = HERE / 'signature-plan'
index = json.loads((plan / 'source-index.json').read_text())
cuts = 0
for source in index['sources']:
    data = Path(source['path']).read_bytes()
    assert data == (plan / source['snapshot']).read_bytes()
    assert len(data) == source['bytes']
    assert len(data.splitlines()) == source['lines']
    assert hashlib.sha256(data).hexdigest() == source['sha256']
    for cut in source['reviewed_ranges']:
        excerpt = b''.join(data.splitlines(keepends=True)[cut['start']-1:cut['end']])
        assert excerpt == (plan / cut['excerpt']).read_bytes()
        assert len(excerpt) == cut['bytes']
        assert hashlib.sha256(excerpt).hexdigest() == cut['sha256']
        cuts += 1
assert len(index['sources']) == 23 and cuts == 42
contracts = json.loads((plan / 'contracts.json').read_text())
for contract in contracts:
    data = (plan / contract['path']).read_bytes()
    assert len(data) == contract['bytes']
    assert len(data.splitlines()) == contract['lines']
    assert hashlib.sha256(data).hexdigest() == contract['sha256']
assert [item['lines'] for item in contracts] == [16, 9, 71, 48]
gate = dict(status='ROOT_DECLARATION_REVIEW_CLEAR', observed_at=datetime.datetime.now().astimezone().isoformat(),
    module='MicroCFTA.SourceCurrentOriginalRowGroupChain', public_names=['groups_complete'],
    private_names=['bucket_readback'], local_induction='complete',
    contract_sha256=hashlib.sha256((plan / 'contracts.json').read_bytes()).hexdigest(),
    contracts=contracts, intended_source_lines=[260, 330], source_hard_stop=350,
    live_sources=23, live_source_cuts=42, component_pins=counts,
    root_read='Whole four declarations, proof route, stitch equations, both independent reviews and all eight checkpoint scripts. Repository cuts were read in the preceding inventory review; installed cuts were read at this declaration gate. All current identities and exact excerpts verified.',
    independent_declaration_review='signature-audit/review.md',
    independent_checkpoint_review='checkpoint-audit/review.md',
    retained_scope=['fixed admitted source and ranked model', 'original available closed parent',
        'actual per-group equations through the same full returned state', 'all boundary packets',
        'global initial-domain allocation Trace', 'one initial global Room',
        'flattened physical union iff in every ambient environment', 'literal empty non-node and Mu row view'],
    open_scope=['generated parents', 'Haskell Mu and union row view', 'common-fuel executable outer traversal',
        'practical host widths', 'solver correspondence', 'whole Haskell pass refinement', 'convergence'],
    body_authorized=True, compiler_authorized=False, prepared_tool_execution_authorized=False,
    board_posts_authorized=False, whole_goal_complete=False)
assert gate['contract_sha256'] == 'ce5fc0d2d39bc3a19fd3186f825ffe35684cea2397c777078f3c6ecff7c2148d'
path = HERE / 'root-declaration-review.json'
assert not path.exists()
path.write_text(json.dumps(gate, indent=2) + '\n')
print(json.dumps({'status': gate['status'], 'source_hard_stop':350, 'body_authorized':True, 'components':counts}))
