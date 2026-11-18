from pathlib import Path
import datetime
import gzip
import hashlib
import json
import shutil
import subprocess

ROOT = Path('/home/tritlo/Code/mcfta')
RUN = Path(__file__).parent
PACKET = ROOT / 'lean/restart-evidence/20261118-source-worker-seeds-components-checkpoint'
config = json.loads((RUN / 'checkpoint-config.json').read_text())
CODE = config['checked_code']
BASE = '7dd87b6642d3114e1d02713af04a5ed494f72059'
PUBLIC = Path(config['public_run'])
sha = lambda data: hashlib.sha256(data).hexdigest()
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT).decode().strip() == CODE
assert PACKET.is_dir()
for name, digest in json.loads((PUBLIC / 'source-pins.json').read_text()).items():
    assert sha((ROOT / name).read_bytes()) == digest, name
result = json.loads((PUBLIC / 'checked.json').read_text())
assert len(result['checks']) == config['public_gates']
assert all(item['exit'] == 0 and not item['nonstandard_axioms']
           and not item['diagnostics'] and not item['sorryAx'] for item in result['checks'])
assert result['checks'] == config['checks']
assert result['audited_theorems'] == config['audited_theorems']
assert result['individual_reports'] == config['explicit_reports']
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
sources = {str(p.relative_to(ROOT)): sha(p.read_bytes())
           for p in sorted((ROOT / 'lean/MicroCFTA').glob('*.lean'))}
tree = hashlib.sha256()
for name, digest in sorted(sources.items()):
    tree.update(name.encode() + b'\0' + digest.encode() + b'\n')
imports = [line.split()[1] for line in (ROOT / 'lean/MicroCFTA/Audit.lean').read_text().splitlines()
           if line.startswith('import ')]
assert len(sources) == config['source_files']
assert len(imports) == config['direct_audit_imports']
assert tree.hexdigest() == config['source_tree_sha256']
assert set(sources) == {name for name in json.loads((PUBLIC / 'source-pins.json').read_text())
                        if name.startswith('lean/MicroCFTA/') and name.endswith('.lean')}
commit = json.loads((RUN / 'SOURCE-COMMIT.json').read_text())
assert CODE == commit['source_commit'] and BASE == commit['parent']
pins = dict(sources)
for name in ['shell.nix', 'lean/lean-toolchain', 'lean/lakefile.toml', 'lean/lake-manifest.json']:
    pins[name] = sha((ROOT / name).read_bytes())
(PACKET / 'source-pins.json.gz').write_bytes(gzip.compress((json.dumps(pins, indent=2) + '\n').encode(), mtime=0))
patch = subprocess.check_output(['git', 'diff', BASE, CODE, '--', 'lean/MicroCFTA'], cwd=ROOT)
(PACKET / 'checked-code.patch.gz').write_bytes(gzip.compress(patch, mtime=0))
common = (RUN / 'checkpoint-note.md').read_text().replace('{{TIME}}', now).replace('{{TREE}}', tree.hexdigest()).replace('{{CODE}}', CODE)
board_prefix = config['board_prefix']
request = json.loads((RUN / (board_prefix + 'request.json')).read_text())
canonical = json.loads((RUN / (board_prefix + 'canonical.json')).read_text())
assert canonical.get('verified', True)
post = canonical.get('post', canonical)
assert post['id'] == request['request_id']
for actual, expected in [(post['author'], request['username']), (post['thread_id'], request['thread_id']),
                         (post['post_type'], request['post_type']), (post['content'], request['content']),
                         (post['metadata'], request['metadata'])]:
    assert actual == expected
assert type(post['sequence']) is int and post['sequence'] > 0
assert post['sequence'] == config['board_sequence']
assert post['id'] == config['board_post_id']
prior_documents = {name: subprocess.check_output(['git', 'show', CODE + ':' + name], cwd=ROOT)
                   for name in ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md']}
assert all((ROOT / name).read_bytes() == data for name, data in prior_documents.items())
assert '{{' not in common and '}}' not in common
documents = []
for name in ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md']:
    path = ROOT / name
    prior = prior_documents[name]
    assert path.read_bytes() == prior, name
    prefix = common.encode()
    path.write_bytes(prefix + prior)
    target = PACKET / 'document-prefixes' / (name + '.gz')
    target.parent.mkdir(exist_ok=True)
    target.write_bytes(gzip.compress(prefix, mtime=0))
    documents.append({'path': name, 'prior_commit': CODE, 'prior_sha256': sha(prior),
                      'prefix_sha256': sha(prefix), 'updated_sha256': sha(path.read_bytes()),
                      'prior_bytes_preserved_as_exact_suffix': path.read_bytes().endswith(prior)})
checkpoint = dict(config)
checkpoint.update({'at': now, 'prior_checkpoint': BASE, 'source_tree_sha256': tree.hexdigest(),
    'source_tree_digest_method': 'sorted UTF-8 relative path + NUL + lowercase SHA256 + newline',
    'documents': documents, 'standard_axiom_reports': result['checks'][-1]['axiom_groups'],
    'axiom_free_reports': result['checks'][-1]['axiom_free_reports'], 'haskell_changed': False,
    'goal_active': False, 'work_authorized_by_explicit_user_resume': True,
    'persistent_goal_control_status': 'paused', 'goal_completion_claimed': False, 'board_post_id': post['id'], 'board_sequence': post['sequence']})
(PACKET / 'checkpoint.json').write_text(json.dumps(checkpoint, indent=2) + '\n')
(PACKET / 'README.md').write_text(f"""# Worker resources and preparation preservation

{common}

Seven fresh public reports and seven private helpers add 14 theorem declarations.
The five selected modules have no new definition or proof-limit change.
All 264 resource-owner reports remain inherited. The old SeedClosure block
keeps all 23529 bytes at offset 61. Audit keeps its entire 434278-byte old block
at offset 287. All other 6277 old Source files are byte-exact.

The actual Source commit used controller985. Root independently verified
the unused supplement39 after the commit. Both controls and their distinct
provenance remain archived. The actual private checks were 23742 and 33636.
The failed84470 run and all scope and filename repairs remain. The original
legacy narrowing header was rejected before compilation. It is neither
byte-equal nor alpha-equivalent to the selected current-source header.

The prior checkpoint is bound by committed manifest, Source and toolchain pins.
It is not copied recursively. RawFold is unverified in this checkpoint. Its separate first check failed a
naming linter and receives zero credit. Future Work59, controllers and runtime are excluded.

These are concrete worker attachment components. The complete ordered worker
phase induction, all query admissions and Seeds transport remain open. The
full goal stays ONE finite accepted completion of the SAME original emitted
root under ONE assignment for all historical obligations. Native inhabitance,
Type/Marker compatibility, guard truth and Haskell correspondence remain open.
No Haskell or runtime code changed.

The archive omits compiled objects and links. Use --current-tree only at
this exact Source and document state.
""")
for name in ['assemble.py', 'finalize.py', 'verify.py', 'archive-roots.json', 'checkpoint-config.json', 'skipped-published-roots.json', 'selection-review.json']:
    shutil.copyfile(RUN / name, PACKET / name)
(PACKET / 'checkpoint-note.md.gz').write_bytes(gzip.compress((RUN / 'checkpoint-note.md').read_bytes(), mtime=0))
print(json.dumps({'checked_code': CODE, 'source_tree_sha256': tree.hexdigest(),
                  'source_files': len(sources), 'direct_audit_imports': len(imports)}))
