from pathlib import Path
import datetime
import gzip
import hashlib
import json
import shutil
import subprocess

ROOT = Path('/home/tritlo/Code/mcfta')
RUN = Path('/tmp/mcfta-mixed-open-alias-checkpoint-20261114-1521')
PACKET = ROOT / 'lean/restart-evidence/20261114-mixed-open-alias-and-native-replay'
config = json.loads((RUN / 'checkpoint-config.json').read_text())
CODE = config['checked_code']
BASE = '1750d9d8fc067cd9472dd4bd0800e812ea7c5e55'
PUBLIC = Path(config['public_run'])
sha = lambda data: hashlib.sha256(data).hexdigest()
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT).decode().strip() == CODE
assert PACKET.is_dir()
for name, digest in json.loads((PUBLIC / 'source-pins.json').read_text()).items():
    assert sha((ROOT / name).read_bytes()) == digest, name
result = json.loads((PUBLIC / 'checked.json').read_text())
assert len(result['checks']) == config['public_gates']
assert all(item['exit'] == 0 and not item['nonstandard_axioms'] for item in result['checks'])
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
pins = dict(sources)
for name in ['shell.nix', 'lean/lean-toolchain', 'lean/lakefile.toml', 'lean/lake-manifest.json']:
    pins[name] = sha((ROOT / name).read_bytes())
(PACKET / 'source-pins.json.gz').write_bytes(gzip.compress((json.dumps(pins, indent=2) + '\n').encode(), mtime=0))
patch = subprocess.check_output(['git', 'diff', BASE, CODE, '--', 'lean/MicroCFTA'], cwd=ROOT)
(PACKET / 'checked-code.patch.gz').write_bytes(gzip.compress(patch, mtime=0))
common = (RUN / 'checkpoint-note.md').read_text().replace('{{TIME}}', now).replace('{{TREE}}', tree.hexdigest()).replace('{{CODE}}', CODE)
documents = []
for name in ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md']:
    path = ROOT / name
    prior = subprocess.check_output(['git', 'show', CODE + ':' + name], cwd=ROOT)
    assert path.read_bytes() == prior, name
    prefix = common.encode()
    path.write_bytes(prefix + prior)
    target = PACKET / 'document-prefixes' / (name + '.gz')
    target.parent.mkdir(exist_ok=True)
    target.write_bytes(gzip.compress(prefix, mtime=0))
    documents.append({'path': name, 'prior_commit': CODE, 'prior_sha256': sha(prior),
                      'prefix_sha256': sha(prefix), 'updated_sha256': sha(path.read_bytes()),
                      'prior_bytes_preserved_as_exact_suffix': path.read_bytes().endswith(prior)})
board_prefix = config['board_prefix']
request = json.loads((RUN / (board_prefix + 'request.json')).read_text())
canonical = json.loads((RUN / (board_prefix + 'canonical.json')).read_text())
assert canonical['verified']
post = canonical['post']
assert post['id'] == request['request_id']
for actual, expected in [(post['author'], request['username']), (post['thread_id'], request['thread_id']),
                         (post['post_type'], request['post_type']), (post['content'], request['content']),
                         (post['metadata'], request['metadata'])]:
    assert actual == expected
checkpoint = dict(config)
checkpoint.update({'at': now, 'prior_checkpoint': BASE, 'source_tree_sha256': tree.hexdigest(),
    'source_tree_digest_method': 'sorted UTF-8 relative path + NUL + lowercase SHA256 + newline',
    'documents': documents, 'standard_axiom_reports': result['checks'][-1]['axiom_groups'],
    'axiom_free_reports': result['checks'][-1]['axiom_free_reports'], 'haskell_changed': False,
    'goal_active': True, 'board_post_id': post['id'], 'board_sequence': post['sequence']})
(PACKET / 'checkpoint.json').write_text(json.dumps(checkpoint, indent=2) + '\n')
(PACKET / 'README.md').write_text(f'''# Mixed source aliases and actual native preparation

Checked source: {CODE}. Prior compact checkpoint: {BASE}.

The current source's original recursive universe is preserved by both actual
mixed-domain aliases. Every successful native fuel returns that exact universe
and the selected alias's exact final machine. Initial boundary ownership and
actual alias atom checks are also checked. Exact successful native value, entry
and preparation replay preserve the actual reached values, cores and heaps.
Pointwise preparation resources retain all existing initial requirements.

The earlier sufficiently-large-budget literal-identity worker resource theorem
and same-source initializer bridge remain checked. These results do not prove
one finite accepted original-root term with one compatible assignment per emitted
branch. Generated-Type closure and every-budget stopped worker-output history
remain open. All original typing, language, depth, preprocessing, stream, size,
count, weight, rank, host and compiled Haskell obligations stay in scope.

The checked public source suffices to reproduce these Lean results. Logs are
derived records. This archive also retains failed inputs, proof repairs and
marked drafts absent from the final source. It contains no compiled objects or
copied import overlays. Immutable older archives remain unchanged.

Use the pinned checkout and Nix shell. The saved public drivers list exact module,
strict and independent-import commands. Run jobs serially with the recorded
4 GiB memory cap and zero swap. Verify source-pins.json.gz before rerunning.
From lean/, run lake build MicroCFTA.Audit and lake env lean -j1
-DwarningAsError=true MicroCFTA/Audit.lean inside the pinned Nix shell.
Private absolute /tmp paths are historical input locations. Recreate output
paths and regenerate their pins when rerunning private attempts elsewhere.
They are not build dependencies of the public source.

Strict Audit checks {result['audited_theorems']:,} imported theorem axiom
dependencies and {result['individual_reports']} separate reports. The count
records coverage of those dependencies. It does not prove the full objective.

archived-inputs.json maps losslessly saved bytes to original paths and hashes.
manifest.json covers every payload, including nested manifests. Only the exact
root manifest.json is excluded. verify.py checks decompressed identities, the
code patch, document reconstruction, source digest and all payload hashes.
Use --current-tree only at the pinned source and checkpoint document state.
The source tree digest is {tree.hexdigest()}.
''')
for name in ['assemble.py', 'finalize.py', 'verify.py', 'archive-roots.json', 'checkpoint-config.json']:
    shutil.copyfile(RUN / name, PACKET / name)
(PACKET / 'checkpoint-note.md.gz').write_bytes(gzip.compress((RUN / 'checkpoint-note.md').read_bytes(), mtime=0))
print(json.dumps({'checked_code': CODE, 'source_tree_sha256': tree.hexdigest(),
                  'source_files': len(sources), 'direct_audit_imports': len(imports)}))
