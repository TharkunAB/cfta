from pathlib import Path
import datetime
import gzip
import hashlib
import json
import shutil
import subprocess

ROOT = Path('/home/tritlo/Code/mcfta')
WORK = Path(__file__).resolve().parent
PACKET = ROOT / 'lean/restart-evidence/20261118-no-mu-whole-worker-endpoint-inventory-checkpoint'
config = json.loads((WORK / 'checkpoint-config.json').read_text())
CODE = config['checked_code']
BASE = config['prior_checkpoint']
PUBLIC = Path(config['public_run'])
sha = lambda data: hashlib.sha256(data).hexdigest()
git = lambda *args: subprocess.check_output(['git', *args], cwd=ROOT)
assert git('rev-parse', 'HEAD').decode().strip() == CODE
assert PACKET.is_dir()
for name, digest in json.loads((PUBLIC / 'source-pins.json').read_text()).items():
    assert sha((ROOT / name).read_bytes()) == digest, name
result = json.loads((PUBLIC / 'checked.json').read_text())
assert result == json.loads((PUBLIC / 'results.json').read_text())
assert result['checks'] == config['checks']
assert [e['total_axiom_reports'] for e in result['checks']] == [759, 27, 354, 759, 759]
assert [e['declaration_checks'] for e in result['checks']] == [0, 3, 0, 0, 0]
assert all(not e['exit'] and not e['nonstandard_axioms'] and not e['diagnostics'] and not e['sorryAx'] for e in result['checks'])
assert result['audited_theorems'] == config['audited_theorems'] == 100395
sources = {str(p.relative_to(ROOT)): sha(p.read_bytes()) for p in sorted((ROOT / 'lean/MicroCFTA').glob('*.lean'))}
tree = hashlib.sha256()
for name, digest in sorted(sources.items()):
    tree.update(name.encode() + b'\0' + digest.encode() + b'\n')
assert len(sources) == 6293 and tree.hexdigest() == config['source_tree_sha256']
assert sum(line.startswith('import ') for line in (ROOT / 'lean/MicroCFTA/Audit.lean').read_text().splitlines()) == 5293
source = json.loads((WORK / 'SOURCE-COMMIT.json').read_text())
assert CODE == source['source_commit'] and BASE == source['parent']
pins = dict(sources)
for name in ['shell.nix', 'lean/lean-toolchain', 'lean/lakefile.toml', 'lean/lake-manifest.json']:
    pins[name] = sha((ROOT / name).read_bytes())
(PACKET / 'source-pins.json.gz').write_bytes(gzip.compress((json.dumps(pins, indent=2) + '\n').encode(), mtime=0))
(PACKET / 'checked-code.patch.gz').write_bytes(gzip.compress(git('diff', BASE, CODE, '--', 'lean/MicroCFTA'), mtime=0))
request = json.loads((ROOT / config['board_request_path']).read_text())
canonical = json.loads((ROOT / config['board_canonical_path']).read_text())
assert canonical['verified']
post = canonical.get('post', canonical)
assert post['id'] == request['request_id'] == config['board_post_id']
assert post['sequence'] == config['board_sequence']
for key, value in [('author', request['username']), ('thread_id', request['thread_id']), ('post_type', request['post_type']), ('content', request['content']), ('metadata', request['metadata'])]:
    assert post[key] == value
assert post['metadata']['source_commit'] == CODE and not post['metadata']['joint_finite_completion_proved']
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
note = (WORK / 'checkpoint-note.md').read_text()
values = {'TIME': now, 'TREE': tree.hexdigest(), 'CODE': CODE, 'THEOREMS': 100395, 'PINS': 12777,
          'REMOVED': config['removed_regular_bytes'], 'SYMLINKS': config['removed_symlinks'], 'CLEANUP': config['known_cumulative_tmp_removed_bytes'],
          'BOARD': post['sequence'], 'USAGE': config['current_primary_usage_percent'], 'USAGE_TIME': config['current_primary_usage_checked_at']}
for key, value in values.items():
    note = note.replace('{{' + key + '}}', str(value))
assert '{{' not in note and '}}' not in note
old_docs = {name: git('show', CODE + ':' + name) for name in ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md']}
assert all((ROOT / name).read_bytes() == data for name, data in old_docs.items())
documents = []
for name, prior in old_docs.items():
    path = ROOT / name
    prefix = note.encode()
    path.write_bytes(prefix + prior)
    target = PACKET / 'document-prefixes' / (name + '.gz')
    target.parent.mkdir(exist_ok=True)
    target.write_bytes(gzip.compress(prefix, mtime=0))
    documents.append({'path': name, 'prior_commit': CODE, 'prior_sha256': sha(prior), 'prefix_sha256': sha(prefix),
                      'updated_sha256': sha(path.read_bytes()), 'prior_bytes_preserved_as_exact_suffix': path.read_bytes().endswith(prior)})
checkpoint = dict(config)
checkpoint.update(at=now, documents=documents, source_tree_digest_method='sorted UTF-8 relative path + NUL + lowercase SHA256 + newline',
                  standard_axiom_reports=result['checks'][-1]['axiom_groups'], axiom_free_reports=result['checks'][-1]['axiom_free_reports'],
                  prior_immutable_archive=config['prior_immutable_archive'], prior_manifest_sha256=config['prior_manifest_sha256'])
(PACKET / 'checkpoint.json').write_text(json.dumps(checkpoint, indent=2) + '\n')
(PACKET / 'README.md').write_text('# Original-budget no-Mu worker inventory\n\n' + note + '\nUse --current-tree only at this exact Source and document state.\n')
for name in ['assemble.py', 'finalize.py', 'verify.py', 'verify-input-closure.py', 'archive-files.json', 'input-maps.json', 'ancestor-links.json', 'checkpoint-config.json', 'selection-review.json']:
    shutil.copyfile(WORK / name, PACKET / name)
(PACKET / 'checkpoint-note.md.gz').write_bytes(gzip.compress((WORK / 'checkpoint-note.md').read_bytes(), mtime=0))
print(json.dumps({'checked_code': CODE, 'source_tree_sha256': tree.hexdigest(), 'source_files': len(sources), 'direct_audit_imports': 5293}))
