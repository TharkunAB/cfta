from pathlib import Path
import datetime
import gzip
import hashlib
import json
import shutil
import subprocess

ROOT = Path('/home/tritlo/Code/mcfta')
RUN = Path(__file__).parent
PACKET = ROOT / 'lean/restart-evidence/20261117-third-query-six-seed-checkpoint'
config = json.loads((RUN / 'checkpoint-config.json').read_text())
CODE = config['checked_code']
BASE = 'c894b4e3fda56e1f8c275f02653f0bba3be7167a'
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
(PACKET / 'README.md').write_text(f"""# Third-history source inventory and six cache seeds

{common}

Source pins and toolchain identify the checked proof bytes. Original supplied
fuels and all actual old/middle/third histories remain. The public joint FIRST
is exact b4. Three new modules and three complete owner EOF appends add
13 theorems:7 public and6 private, with0 definitions. Seven fresh explicit reports
plus496 inherited give503 combined. All 264resource reports remain inherited.
Parser 29139 and combined import-order 54344failures remain. The only source
repair renames two private Node identifiers; all original FIRSTs and public
Node proof bytes remain exact. Check 32348 and final 37551 are preserved.

This proves source Mu inventory at middleSnapshot and six INITIAL cache laws
qualified by one fixed full third horizon. It does not prove third execute-outcome
or all-prefix inventory. Arbitrary query sequences, native inhabitance and ONE accepted
finite completion for every historical obligation remain open. Lossless input
archives omit compiled objects and links. Old document bytes remain suffixes.
Use --current-tree only at this exact Source and document state.
""")
for name in ['assemble.py', 'finalize.py', 'verify.py', 'archive-roots.json', 'checkpoint-config.json', 'skipped-published-roots.json', 'selection-review.json']:
    shutil.copyfile(RUN / name, PACKET / name)
(PACKET / 'checkpoint-note.md.gz').write_bytes(gzip.compress((RUN / 'checkpoint-note.md').read_bytes(), mtime=0))
print(json.dumps({'checked_code': CODE, 'source_tree_sha256': tree.hexdigest(),
                  'source_files': len(sources), 'direct_audit_imports': len(imports)}))
