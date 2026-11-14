from pathlib import Path
import datetime
import gzip
import hashlib
import json
import shutil
import subprocess

ROOT = Path('/home/tritlo/Code/mcfta')
RUN = Path('/tmp/mcfta-source-identity-worker-checkpoint-20261114-1447')
PACKET = ROOT / 'lean/restart-evidence/20261114-source-identity-worker-resources'
CODE = '981f461db13af128f127c5ce4e62e39e86e6d474'
BASE = '31c38ed79d8c23be8a979750b77c986ca79f5338'
PUBLIC = Path('/tmp/mcfta-off-diagonal-body-readback-publication-20261114-1443')
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT).decode().strip() == CODE
assert PACKET.is_dir()
for path, digest in json.loads((PUBLIC / 'source-pins.json').read_text()).items():
    assert hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == digest, path
final = json.loads((PUBLIC / 'checked.json').read_text())
assert len(final['checks']) == 5 and all(item['exit'] == 0 for item in final['checks'])
assert final['audited_theorems'] == 96017 and final['individual_reports'] == 91
assert final['checks'][-1]['axiom_groups'] == 89
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

No Haskell/Cabal/test/Liquid Haskell annotation changed. No new implementation
fix was established. Record every future Haskell fix here for external readers.

The mixed-domain reference proof needed actual branch normalization, explicit
bind continuations, a local source-body reduction and exact heap projection.
The off-diagonal control/readback needed explicit reference selection, the exact
Mu continuation, substitution/list normalization and strict lint repairs.
All failed inputs and actual successful repairs are preserved without giving
failed attempts proof credit. Existing checked source declarations remain exact.

Root publication preparation failed before Lean because a section span retained
one extra newline and a capped peak log had already created a directory. The
proof bytes did not change. A partial private MicroCFTA module path then masked
normal compiled modules. Publishing the checked necessary lower dependency
resolved that import setup. Neither setup failure establishes a Haskell defect.
The full body wrapper subsequently reached its proof check and FAILS. The
original public target remains open with no added provider premises.

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
assert len(sources) == 5945 and len(imports) == 4943
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
              'audited_theorems': 96017, 'explicit_reports': 91,
              'standard_axiom_reports': 89, 'axiom_free_reports': 2,
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
              'whole_identity_worker_resources_proved': True,
              'current_source_identity_bridge_proved': True,
              'mixed_reference_alias_proved': True,
              'off_diagonal_body_readback_proved': True,
              'mixed_body_alias_proved': False,
              'all_fuel_output_history_proved': False,
              'joint_finite_completion_proved': False,
              'compiled_haskell_correspondence_proved': False,
              'goal_active': True, 'board_post_id': post['id'],
              'board_sequence': post['sequence']}
(PACKET / 'checkpoint.json').write_text(json.dumps(checkpoint, indent=2) + '\n')
(PACKET / 'README.md').write_text(f'''# Same-source initialization and actual identity-worker resources

Checked source: {CODE}. Prior checkpoint: {BASE}.

The same accepted current-source initializer derives the actual literal-identity
worker's inputs. At each finite recursion depth, one sufficiently large common
budget gives a stable exact result and full output resources, pending references
and dependency stratification. No supplied future output/callback provider or
alternate initializer is an input. This is resource closure.

The contextual mixed-domain ref(U)/U result returns the same original U. The
actual off-diagonal body readback is checked. The full body alias remains open.
Every-budget worker partial-output history, one finite accepted original-root
term with one assignment, and compiled Haskell correspondence remain open.

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

The latest strict Audit checks 96,017 imported project theorems and separately
91 explicit reports: 89 standard-axiom and two axiom-free reports. The counts
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
