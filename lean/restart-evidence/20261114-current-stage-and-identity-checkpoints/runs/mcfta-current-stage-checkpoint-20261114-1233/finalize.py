from pathlib import Path
import datetime
import gzip
import hashlib
import json
import shutil
import subprocess

ROOT = Path('/home/tritlo/Code/mcfta')
RUN = Path('/tmp/mcfta-current-stage-checkpoint-20261114-1233')
PACKET = ROOT / 'lean/restart-evidence/20261114-current-stage-and-identity-checkpoints'
CODE = 'ccc7f3dc59f50966b90fec1ae49eda7bc54cfc3e'
BASE = 'f2e625838efa2c444487eba46d3a58c9f622424c'
PUBLIC = Path('/tmp/mcfta-identity-prefix-any-budget-publication-20261114-1230')
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT).decode().strip() == CODE
assert PACKET.is_dir()
for path, digest in json.loads((PUBLIC / 'source-pins.json').read_text()).items():
    assert hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == digest, path
final = json.loads((PUBLIC / 'checked.json').read_text())
assert len(final['checks']) == 5 and all(item['exit'] == 0 for item in final['checks'])
assert final['audited_theorems'] == 95968 and final['individual_reports'] == 85
assert final['checks'][-1]['axiom_groups'] == 83
assert final['checks'][-1]['axiom_free_reports'] == 2
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
sources = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
           for p in sorted((ROOT / 'lean/MicroCFTA').glob('*.lean'))}
tree = hashlib.sha256()
for path, digest in sorted(sources.items()):
    tree.update(path.encode() + b'\0' + digest.encode() + b'\n')
tree_hash = tree.hexdigest()
pins = dict(sources)
for path in ['shell.nix', 'lean/lean-toolchain', 'lean/lakefile.toml', 'lean/lake-manifest.json']:
    pins[path] = hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
(PACKET / 'source-pins.json.gz').write_bytes(gzip.compress((json.dumps(pins, indent=2) + '\n').encode(), mtime=0))
patch = subprocess.check_output(['git', 'diff', BASE, CODE, '--', 'lean/MicroCFTA'], cwd=ROOT)
(PACKET / 'checked-code.patch.gz').write_bytes(gzip.compress(patch, mtime=0))
common = (RUN / 'checkpoint-note.md').read_text().replace('{{TIME}}', now).replace('{{TREE}}', tree_hash)
extra = """## Implementation findings for this checkpoint

No Haskell, Cabal, test or Liquid Haskell annotation changed. No new Haskell
implementation defect or fix was established. Record each future fix here.

The callback alias needed its existing width index explicitly. Root's first
private axiom reports used the wrong namespace. The all-budget proof needed
namespace opens, the actual private consumer's Node equality instance, narrower
section-instance scope and one false-Boolean simplification. An ambiguous
preparation assertion failed before Lean ran. All failed inputs and repairs are
preserved without proof credit; no final public premise was added.

The mixed-reference proof still fails and has no credit. Its reserved universe
identifier, binder syntax and branch rewriting required repairs. Later native
spine/congruence obligations remain. Resource invariants alone do not establish
Holds for the bucket removed by a repeated clear, or one finite joint witness.
No Haskell defect follows merely from an unfinished Lean proof.

"""
documents = []
for name in ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md']:
    path = ROOT / name
    old = subprocess.check_output(['git', 'show', f'{CODE}:{name}'], cwd=ROOT)
    assert path.read_bytes() == old, name
    prefix = (common + (extra if name == 'FINDINGS.md' else '')).encode()
    path.write_bytes(prefix + old)
    assert path.read_bytes().endswith(old)
    target = PACKET / 'document-prefixes' / (name + '.gz')
    target.parent.mkdir(exist_ok=True)
    target.write_bytes(gzip.compress(prefix, mtime=0))
    documents.append({'path': name, 'prior_commit': CODE,
                      'prior_sha256': hashlib.sha256(old).hexdigest(),
                      'prefix_sha256': hashlib.sha256(prefix).hexdigest(),
                      'updated_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                      'prior_bytes_preserved_as_exact_suffix': True})
imports = [line.split()[1] for line in (ROOT / 'lean/MicroCFTA/Audit.lean').read_text().splitlines()
           if line.startswith('import ')]
assert len(sources) == 5942 and len(imports) == 4940
request = json.loads((RUN / 'board-request.json').read_text())
canonical = json.loads((RUN / 'board-canonical.json').read_text())
post = canonical['post']
assert canonical['verified']
assert post['id'] == request['request_id']
for actual, wanted in [(post['author'], request['username']),
                       (post['thread_id'], request['thread_id']),
                       (post['post_type'], request['post_type']),
                       (post['content'], request['content']),
                       (post['metadata'], request['metadata'])]:
    assert actual == wanted
checkpoint = {'at': now, 'checked_code': CODE, 'prior_checkpoint': BASE,
              'source_files': len(sources), 'direct_audit_imports': len(imports),
              'audited_theorems': 95968, 'explicit_reports': 85,
              'standard_axiom_reports': 83, 'axiom_free_reports': 2,
              'source_tree_sha256': tree_hash,
              'source_tree_digest_method': 'sorted UTF-8 relative path + NUL + lowercase SHA256 + newline',
              'documents': documents, 'haskell_changed': False,
              'exact_original_mu_identity_proved': True,
              'after_growth_original_mu_identity_proved': True,
              'actual_identity_prefix_resources_proved': True,
              'actual_root_narrow_identity_proved': True,
              'all_budget_supported_identity_prefix_resources_proved': True,
              'callback_generalization_checked': True,
              'captured_child_generalization_checked': True,
              'whole_identity_worker_resources_proved': False,
              'all_fuel_output_history_proved': False,
              'joint_finite_completion_proved': False,
              'compiled_haskell_correspondence_proved': False,
              'goal_active': True, 'board_post_id': post['id'],
              'board_sequence': post['sequence']}
(PACKET / 'checkpoint.json').write_text(json.dumps(checkpoint, indent=2) + '\n')
(PACKET / 'README.md').write_text(f'''# Source-universe identity and actual identity-prefix resources

Checked source: {CODE}. Prior checkpoint: {BASE}.

The exact observed initial root narrowing now derives source-heap growth.
Supported actual identity prefixes preserve the existing state/order/resource
contracts at every common budget. Callback and captured-child completion now
retain the actual narrowing index with all configured contracts preserved. Whole-worker output history and one finite common original-root
completion remain open. Compiled Haskell correspondence is not proved.

The checked source is sufficient to reproduce these Lean proof results. Logs
record derived results. This packet also preserves failed inputs, repairs and
marked drafts absent from the final code. It contains no compiled objects or
copied import overlays.

Use the pinned checkout and Nix shell. Archived publication drivers contain
the exact build, strict-check and independent-import commands. Run jobs serially
with the recorded 4 GiB cap. Verify source-pins.json.gz before rerunning.
Run lake build MicroCFTA.Audit and lake env lean -j1 -DwarningAsError=true
MicroCFTA/Audit.lean from lean/ inside the pinned Nix shell. Recreate /tmp output
directories and regenerate an archived driver's absolute-path source pins if
the original private paths no longer exist; do not treat those paths as build
dependencies of the public source.

The latest strict Audit checks 95,968 imported project theorems and separately
85 explicit reports: 83 standard-axiom and two axiom-free reports. The counts
do not establish the complete objective.

archived-inputs.json maps saved bytes to original paths and hashes. manifest.json
covers every payload file, including nested manifest.json files. It excludes
only the exact root manifest.json file. Verify source byte identities after
decompression. The source tree digest is {tree_hash}.
''')
for name in ['assemble.py', 'finalize.py', 'checkpoint-note.md', 'archive-roots.json']:
    if name == 'checkpoint-note.md':
        (PACKET / (name + '.gz')).write_bytes(gzip.compress((RUN / name).read_bytes(), mtime=0))
    else:
        shutil.copyfile(RUN / name, PACKET / name)
print(json.dumps({'at': now, 'source_tree_sha256': tree_hash,
                  'source_files': len(sources), 'document_prefix_bytes': len(common.encode())}))
