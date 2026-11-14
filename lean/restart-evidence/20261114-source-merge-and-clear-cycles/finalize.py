from pathlib import Path
import datetime
import gzip
import hashlib
import json
import shutil
import subprocess

ROOT = Path('/home/tritlo/Code/mcfta')
RUN = Path('/tmp/mcfta-source-merge-cycle-checkpoint-20261114-0948')
PACKET = ROOT / 'lean/restart-evidence/20261114-source-merge-and-clear-cycles'
CODE = 'b5af50adbe71b5d23480e4226ffb523c22a67730'
BASE = '7ed3bffa220e3800ca2d7449c891e23a29af7c29'
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT).decode().strip() == CODE
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
extra = '''## Findings for implementation specifications

No Haskell implementation defect or fix was established in this checkpoint.
The Haskell, Cabal and test sources remain unchanged. Record every future
implementation fix here so another reader can apply it to the implementation.

The repeated-clear meaning law still requires Holds for the removed suspended
bucket. Post-clear satisfaction alone does not supply those facts. The new
proper-cycle laws prove one obstruction survives actual selected clear. They
do not establish every reachable mixed fragment/path case. A Liquid Haskell
contract must retain this distinction when it specifies checkRepeated.

The default Haskell worker uses noExpansionPreference. spaceOrder controls the
edge traversal and canonical ties. The new erasure law quantifies over a fixed
arbitrary edge function. The old configured OuterNarrow wrapper remains a
different configuration. No implementation behavior changed to obtain erasure.

The first unproved cycle draft placed the membership condition on only the left
side of an iff. Its literal conclusion was false for an empty vertex list.
Parentheses now restrict the complete iff to listed vertices. The false draft
and full failed check remain archived without proof credit. Two unused simp
arguments and one unavailable list lemma were also repaired. The source-merge
draft needed namespace qualifications. The native-return draft needed a local
identifier correction and explicit final-machine unfolding. Those proof repairs
add no semantic premises. They are not Haskell fixes.

'''
documents = []
for name in ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md']:
    path = ROOT / name
    old = subprocess.check_output(['git', 'show', f'{CODE}:{name}'], cwd=ROOT)
    assert path.read_bytes() == old, name
    prefix = (common + (extra if name == 'FINDINGS.md' else '')).encode()
    updated = prefix + old
    assert updated.endswith(old)
    path.write_bytes(updated)
    target = PACKET / 'document-prefixes' / (name + '.gz')
    target.parent.mkdir(exist_ok=True)
    target.write_bytes(gzip.compress(prefix, mtime=0))
    documents.append({'path': name, 'prior_commit': CODE,
                      'prior_sha256': hashlib.sha256(old).hexdigest(),
                      'prefix_sha256': hashlib.sha256(prefix).hexdigest(),
                      'updated_sha256': hashlib.sha256(updated).hexdigest(),
                      'prior_bytes_preserved_as_exact_suffix': True})
audit = (ROOT / 'lean/MicroCFTA/Audit.lean').read_text().splitlines()
imports = [line.split()[1] for line in audit if line.startswith('import ')]
assert len(sources) == 5930 and len(imports) == 4928
final = json.loads(Path('/tmp/mcfta-selected-clear-cycle-publication-20261114-0944/checked.json').read_text())
assert final['audited_theorems'] == 95836 and final['individual_reports'] == 60
assert final['checks'][-1]['axiom_groups'] == 58 and final['checks'][-1]['axiom_free_reports'] == 2
checkpoint = {'at': now, 'checked_code': CODE, 'prior_checkpoint': BASE,
              'source_files': len(sources), 'direct_audit_imports': len(imports),
              'audited_theorems': 95836, 'explicit_reports': 60,
              'standard_axiom_reports': 58, 'axiom_free_reports': 2,
              'source_tree_sha256': tree_hash,
              'source_tree_digest_method': 'sorted UTF-8 relative path + NUL + lowercase SHA256 + newline',
              'documents': documents, 'haskell_changed': False,
              'exact_original_mu_identity_proved': False,
              'joint_finite_completion_proved': False,
              'compiled_haskell_correspondence_proved': False,
              'goal_active': True,
              'board_post_id': '8f51cb53-6c52-4e35-8b38-7b9313bbd0ca',
              'board_sequence': 1301}
(PACKET / 'checkpoint.json').write_text(json.dumps(checkpoint, indent=2) + '\n')
(PACKET / 'README.md').write_text(f'''# Actual source merge, native return and cycle obstruction

Checked source: {CODE}. Prior checkpoint: {BASE}.

The checked source is sufficient to reproduce the proof results. The logs record
derived results. This packet also preserves failed inputs, repairs and marked
drafts that the final code does not contain. It contains no compiled objects.

Use the pinned checkout and Nix shell. The archived publication drivers give
the exact build, strict check and independent-import commands. Run them serially
with the recorded 4 GiB cap. Verify source-pins.json.gz before a rerun.

The latest strict Audit reports 95,836 imported project theorems and separately
60 explicit reports: 58 standard-axiom and two axiom-free reports. These counts
do not establish the complete objective. The finite common original-root term,
exact native Mu identity and compiled Haskell correspondence remain open.

The identity-path packet contains two UNCOMPILED prerequisite candidates and
an UNPROVED exact-identity header. Read its findings before the next proof.

archived-inputs.json maps saved bytes to their original paths and hashes.
manifest.json covers every payload file, including nested manifest.json files.
It excludes only the exact root manifest.json file.
''')
for name in ['assemble.py', 'finalize.py', 'checkpoint-note.md']:
    shutil.copyfile(RUN / name, PACKET / name)
print(json.dumps({'at': now, 'source_tree_sha256': tree_hash,
                  'source_files': len(sources), 'document_prefix_bytes': len(common.encode())}))
