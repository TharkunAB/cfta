import datetime
import hashlib
import json
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = ROOT / 'lean/restart-evidence/20261022-original-row-group-chain'
review_sha = sys.argv[1]
proposal = Path('/tmp/mcfta-original-row-group-chain-proposal')
audit = Path('/tmp/mcfta-original-row-group-chain-body-audit')
assert hashlib.sha256((audit / 'review.md').read_bytes()).hexdigest() == review_sha
for name in ['proposal', 'body-audit', 'full-audit', 'verifier-preparation']:
    path = Path('/tmp/mcfta-original-row-group-chain-' + name)
    assert (path / 'FROZEN.json').is_file()
    for pin in json.loads((path / 'pins.json').read_text()):
        data = (path / pin['path']).read_bytes()
        assert len(data) == pin['bytes'] and hashlib.sha256(data).hexdigest() == pin['sha256'], pin['path']
    subprocess.run(['/usr/bin/python3', str(HERE / 'archive-extra.py'), str(path), name], check=True)

source = (proposal / 'SourceCurrentOriginalRowGroupChain.lean').read_bytes()
source_sha = hashlib.sha256(source).hexdigest()
assert source_sha == '45ee19aba69aec9339203917841052791a389fe46f511ab9574105c8f3d254bb'
assert len(source.splitlines()) == 257 <= 350
plan = HERE / 'signature-plan'
assert source.startswith((plan / 'context.lean.txt').read_bytes())
positions = []
for name in ['private-header.lean.txt', 'public-header.lean.txt', 'local-induction.lean.txt']:
    fragment = (plan / name).read_bytes().rstrip(b'\n') + b' := by\n'
    assert source.count(fragment) == 1
    positions.append(source.index(fragment))
assert positions == sorted(positions)
assert re.findall(rb'(?m)^theorem ([A-Za-z_]+)', source) == [b'groups_complete']
assert re.findall(rb'(?m)^private theorem ([A-Za-z_]+)', source) == [b'bucket_readback']
assert not re.search(rb'\b(sorry|admit|axiom|unsafe|native_decide)\b|set_option', source)
index = json.loads((proposal / 'source-index.json').read_text())
cuts = 0
for item in index['sources']:
    data = Path(item['path']).read_bytes()
    assert data == (proposal / item['snapshot']).read_bytes()
    assert len(data) == item['bytes'] and hashlib.sha256(data).hexdigest() == item['sha256']
    for cut in item['reviewed_ranges']:
        excerpt = b''.join(data.splitlines(keepends=True)[cut['start']-1:cut['end']])
        assert excerpt == (proposal / cut['excerpt']).read_bytes()
        assert len(excerpt) == cut['bytes'] and hashlib.sha256(excerpt).hexdigest() == cut['sha256']
        cuts += 1
assert len(index['sources']) == 24 and cuts == 49
for name in ['prepare-selected-full.py', 'check-full-public.py']:
    destination = HERE / name
    assert not destination.exists()
    shutil.copyfile(HERE / 'full-preparation' / name, destination)
gate = dict(status='ROOT_SOURCE_REVIEW_CLEAR', observed_at=datetime.datetime.now().astimezone().isoformat(),
    source_sha256=source_sha, source_lines=257, source_hard_stop=350,
    root_whole_source_read=True, independent_whole_source_review='body-audit/review.md', independent_review_sha256=review_sha,
    all_four_contracts_exact=True, public_theorems=['groups_complete'], private_helpers=['bucket_readback'],
    full_tool_root_whole_lines=178, full_tool_independent_review='full-audit/review.md',
    verifier_template_root_whole_lines=277, verifier_execution_authorized=False,
    source_identities=24, source_api_cuts=49, first_strict_authorized=True,
    full_after_clean_strict_authorized=True, full_repeats_on_unchanged_source_authorized=False,
    official_install_authorized=False, no_haskell_changes=True, whole_goal_complete=False)
(HERE / 'root-source-review.json').write_text(json.dumps(gate, indent=2) + '\n')
print(json.dumps({'status':gate['status'], 'source_sha256':source_sha, 'source_lines':257, 'strict_authorized':True}))
