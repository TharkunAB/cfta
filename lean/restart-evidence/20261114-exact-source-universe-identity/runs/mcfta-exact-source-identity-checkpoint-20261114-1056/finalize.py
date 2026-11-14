from pathlib import Path
import datetime
import gzip
import hashlib
import json
import shutil
import subprocess

ROOT = Path('/home/tritlo/Code/mcfta')
RUN = Path('/tmp/mcfta-exact-source-identity-checkpoint-20261114-1056')
PACKET = ROOT / 'lean/restart-evidence/20261114-exact-source-universe-identity'
CODE = 'f1fec5d6fa0098bc453dcdee417d1b7aa6a7be68'
BASE = '43ffe583f8f3f4b035d8a7ede419b873e5b8e112'
PUBLIC = Path('/tmp/mcfta-identity-prefix-resources-publication-20261114-1118')
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT).decode().strip() == CODE
assert PACKET.is_dir()
for path, digest in json.loads((PUBLIC / 'source-pins.json').read_text()).items():
    assert hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == digest, path
final = json.loads((PUBLIC / 'checked.json').read_text())
assert len(final['checks']) == 5 and all(item['exit'] == 0 for item in final['checks'])
assert final['audited_theorems'] == 95945 and final['individual_reports'] == 81
assert final['checks'][-1]['axiom_groups'] == 79
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
extra = '''## Implementation findings for this checkpoint

No Haskell implementation defect or fix was established. No Haskell, Cabal,
test or Liquid Haskell annotation changed. Keep each future implementation fix
here so an external reader can apply it to the implementation.

The proof repairs concern Lean elaboration or linting only. The exact-source
identity draft needed a direct marker inequality proof. The probe packet draft
needed explicit local-definition conversions. The independent-import harness
needed all imports before commands. The first mapped-body setup failed before
Lean ran because it expected inline axiom reports that the draft did not have;
the repaired harness appends reports. The identity-prefix proof needed one
ExceptT.mk unfolding and narrower scope for an unused private-helper equality
instance. Every failed input and repair remains archived without PASS credit.
The final public headers did not gain semantic premises.

The actual repeated-clear satisfaction theorem still needs Holds for the
removed bucket. Resource/order preservation does not establish that premise.
A Liquid Haskell contract for clear/recompletion must preserve one shared
assignment and account for those removed constraints. A declared assumption
does not verify the implementation. No such contract was checked here.

'''
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
assert len(sources) == 5938 and len(imports) == 4936
request = json.loads((RUN / 'board-growth-prefix-request.json').read_text())
canonical = json.loads((RUN / 'board-growth-prefix-canonical.json').read_text())
post = canonical['item']
assert canonical['verified_payload']
assert post['id'] == request['request_id']
for actual, wanted in [(post['author'], request['username']),
                       (post['thread_id'], request['thread_id']),
                       (post['post_type'], request['post_type']),
                       (post['content'], request['content']),
                       (post['metadata'], request['metadata'])]:
    assert actual == wanted
checkpoint = {'at': now, 'checked_code': CODE, 'prior_checkpoint': BASE,
              'source_files': len(sources), 'direct_audit_imports': len(imports),
              'audited_theorems': 95945, 'explicit_reports': 81,
              'standard_axiom_reports': 79, 'axiom_free_reports': 2,
              'source_tree_sha256': tree_hash,
              'source_tree_digest_method': 'sorted UTF-8 relative path + NUL + lowercase SHA256 + newline',
              'documents': documents, 'haskell_changed': False,
              'exact_original_mu_identity_proved': True,
              'after_growth_original_mu_identity_proved': True,
              'actual_identity_prefix_resources_proved': True,
              'whole_identity_worker_resources_proved': False,
              'all_fuel_output_history_proved': False,
              'joint_finite_completion_proved': False,
              'compiled_haskell_correspondence_proved': False,
              'goal_active': True, 'board_post_id': post['id'],
              'board_sequence': post['sequence']}
(PACKET / 'checkpoint.json').write_text(json.dumps(checkpoint, indent=2) + '\n')
(PACKET / 'README.md').write_text(f'''# Source-universe identity and actual identity-prefix resources

Checked source: {CODE}. Prior checkpoint: {BASE}.

The source-created universe is now the exact result of the native ref(U)/Mu(U)
request, including after structurally valid source-heap growth. The actual
identity enumeration prefix preserves the existing state/order/resource
contracts. Whole-worker output history and one finite common original-root
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

The latest strict Audit checks 95,945 imported project theorems and separately
81 explicit reports: 79 standard-axiom and two axiom-free reports. The counts
do not establish the complete objective.

archived-inputs.json maps saved bytes to original paths and hashes. manifest.json
covers every payload file, including nested manifest.json files. It excludes
only the exact root manifest.json file. Verify source byte identities after
decompression. The source tree digest is {tree_hash}.
''')
for name in ['assemble.py', 'finalize.py', 'checkpoint-note.md', 'archive-roots.json']:
    shutil.copyfile(RUN / name, PACKET / name)
print(json.dumps({'at': now, 'source_tree_sha256': tree_hash,
                  'source_files': len(sources), 'document_prefix_bytes': len(common.encode())}))
