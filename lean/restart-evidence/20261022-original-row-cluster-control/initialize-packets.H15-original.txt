import datetime
import hashlib
import json
import shutil
from pathlib import Path

HERE = Path(__file__).resolve().parent
START = 'e8a0066c6088d87cc0b0ea9085a07ba2ff44913c'
assert (HERE / 'starting-head.txt').read_text().strip() == START
baseline = json.loads((HERE / 'starting-files.json').read_text())
assert len(baseline) == 85212
assert sum(p.startswith('lean/MicroCFTA/') and p.endswith('.lean') and
           p != 'lean/MicroCFTA/Audit.lean' for p in baseline) == 3630
assert sum(p.endswith('.hs') for p in baseline) == 298
assert sum(p.split('/')[0] in {'cfta', 'cfta-generator', 'cfta-ghc', 'decision-model'}
           for p in baseline) == 207
report = json.loads(Path('/tmp/mcfta-same-symbol-edge-comparison-local-publication.json').read_text())
assert report['status'] == 'LOCAL_PASS' and report['clean'] and report['filesystem_index_head_equal']
assert report['checkpoint'] == START and report['publication'] == 'PENDING_USER_APPROVAL'
assert report['network_commands_executed'] == 0
preserved = report['preservation']
assert len(preserved['frozen_manifests']) == 298
assert sum(p['checked'] for p in preserved['frozen_manifests'].values()) == 1392
assert len(preserved['frozen_entry_archives']) == 5
previous = Path('/tmp/mcfta-same-symbol-edge-comparison-domains-previous-local-checkpoint')
assert not previous.exists()
previous.mkdir()
names = []
for stem in ['support-1', 'seal-1', 'local-publication-1']:
    names += ['mcfta-same-symbol-edge-comparison-' + stem + suffix
              for suffix in ['.json', '.log', '.limits.json', '.peaks.txt', '.source.py', '.usage.json']]
names += ['mcfta-same-symbol-edge-comparison-' + tail for tail in [
    'local-publication.json', 'board-request.json', 'board-reply.json', 'board-readback.json']]
pins = {}
for name in names:
    source = Path('/tmp') / name
    assert source.is_file(), name
    shutil.copyfile(source, previous / name)
    pins[name] = hashlib.sha256(source.read_bytes()).hexdigest()
note = '''# Previous checkpoint publication status

H14 is committed locally at e8a0066c6088d87cc0b0ea9085a07ba2ff44913c.
Its proof commit is 8f6c9efc6db460d72eed3d87402cd8c3819b62e2.
Its local publisher performed no network command. FS=index=HEAD and the tree was clean.
The exact board post and readback state that publication remains pending.
Automatic approval review rejected the earlier H11 push before execution twice.
That review requires fresh direct approval of the destination and payload.
The configured destination was git@github.com:TharkunAB/cfta.git formalize.
No approval has arrived. Automatic goal continuation supplies no approval.
Do not retry the rejected push without direct user approval.
Local formalization can continue while publication remains pending.
'''
(previous / 'publication-blocker.md').write_text(note)
pins['publication-blocker.md'] = hashlib.sha256(note.encode()).hexdigest()
(previous / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
assert not (HERE / 'archived-components.json').exists()
(HERE / 'archived-components.json').write_text('{}\n')
timestamp = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
(HERE / 'current-progress.md').write_text(f'''# Comparison domain history from one initial cache

Updated: {timestamp}.

H14 is committed locally at {START}. Its proof and evidence remain unchanged.
The current pull reports Already up to date. All 85212 starting blobs and modes agree.
The next proof retains one initial domain cache and actual global allocation history.
One initial Room reservation supplies current-call Room through the finite inventory bound.
Actual H10 hit and H13 miss branches must return the same history at their actual after state.
The exact source/models/current cache packet remains explicit. No caller or cache is reset.
No new body has been checked at this cut. No future success or history is a premise.
H6 constructed_node_calls remains the strongest combined semantic theorem.
Stateful scan, physical pruning semantics, generated Mu parents and the public pass remain open.
Practical host width, convergence, solver contracts and Haskell refinement remain open.
No Haskell source or repair changes. The whole formalization goal remains active.
Remote publication remains pending fresh approval after automatic review rejected the push.
''')
print(json.dumps({'status': 'PASS', 'previous_local_files': len(names), 'proof_jobs': 0,
                  'baseline_files': len(baseline), 'older_non_audit_lean': 3630,
                  'haskell': 298, 'package': 207, 'expected_frozen_registries': 299,
                  'expected_frozen_entries': 1393, 'publication': 'PENDING_USER_APPROVAL'}))
