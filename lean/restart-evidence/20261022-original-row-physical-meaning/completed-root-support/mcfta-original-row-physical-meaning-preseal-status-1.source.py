import datetime
import difflib
import hashlib
import json
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
here = root / 'lean/restart-evidence/20261022-original-row-physical-meaning'
proof = (here / 'proof-commit.txt').read_text().strip()
verified = json.loads((here / 'verification.json').read_text())
assert verified['status'] == 'PASS' and verified['actual_jobs'] == 3 and verified['failed_jobs'] == 0
assert verified['both_proof_verification_modes'] and verified['baseline_files'] == 89667
assert (here / 'NEXT-TARGET.md').is_file()
first = Path('/tmp/mcfta-original-row-physical-meaning-source-precheck-1.source.py')
second = Path('/tmp/mcfta-original-row-physical-meaning-source-precheck-2.source.py')
assert json.loads(first.with_name(first.name.replace('.source.py', '.json')).read_text())['exit_code'] == 1
assert json.loads(second.with_name(second.name.replace('.source.py', '.json')).read_text())['exit_code'] == 0
patch = ''.join(difflib.unified_diff(first.read_text().splitlines(True), second.read_text().splitlines(True),
    fromfile=first.name, tofile=second.name))
assert '-for path, pin in json.loads' in patch and "+    path = pin['path']" in patch
assert not (here / 'metadata-precheck-repair.patch').exists()
(here / 'metadata-precheck-repair.patch').write_text(patch)
failures = []
for path in Path('/tmp').glob('mcfta-original-row-physical-meaning-*.json'):
    item = json.loads(path.read_text())
    if isinstance(item, dict) and 'wrapper' in item and 'exit_code' in item and item['exit_code']:
        failures.append(path.name)
assert failures == ['mcfta-original-row-physical-meaning-source-precheck-1.json']
(here / 'metadata-repairs.md').write_text('''# Root metadata repair

One root Python source-precheck job failed before any gate write or Lean command.
The helper assumed a mapping for source-proposal/pins.json. The file contains a list.
The repair reads each list item's path. No semantic check or assertion was removed.
The repaired precheck passes. The exact helper delta is metadata-precheck-repair.patch.
The failed and successful helpers, raw logs, receipts, usage and cap records remain
in the external mcfta-original-row-physical-meaning-source-precheck-{1,2} files.
The final one-shot completed-root-support archive must include these files.
This is one root metadata failure, separate from the three successful Lean/Lake jobs.
Reviewer-only diagnostics remain in their own frozen review packages.
''')
note = root / 'lean/notes-current-original-row-physical-meaning.md'
addition = '''
One root metadata precheck failed before Lean ran. Its pin-list schema repair
and exact records remain in this checkpoint. Read metadata-repairs.md.
Read NEXT-TARGET.md for the reviewed identity-deletion adapter route.
Only a fresh baseline and exact next declaration proposal are authorized.
'''
assert 'One root metadata precheck failed before Lean ran.' not in note.read_text()
note.write_text(note.read_text() + addition)
timestamp = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
(here / 'preseal-previous-current-progress.md').write_bytes((here / 'current-progress.md').read_bytes())
(here / 'current-progress.md').write_text(f'''# Original-row physical meaning: pre-seal status

Updated: {timestamp}. Proof commit: {proof}.

The selected108-line theorem, clean strict1, sole FULL1 and Audit1 are accepted.
Audit has3635 jobs and75453 theorem dependencies. All three actual proof jobs pass.
Root and independent review read all112 checked TYPE lines. Printed bytes agree.
TYPE has no private markers/helper names. Actual axioms are the standard three.
The complete body remains retained and checked programmatically.
Normal and live saved-evidence checks pass from cwd=/ with explicit root.
Preservation passes for89667 baseline files/modes,3633 older non-Audit Lean sources,
298 Haskell files,207 package files and302 frozen registries/1396 entries/five overrides.
Nine document prefixes retain exact inverses. FINDINGS keeps the Haskell index FIRST.
There is no Haskell repair. The original Audit retains its exact sole-import inverse.
One failed root metadata precheck and its pin-schema repair remain separate.
Final independent document review, support archive and seal are pending at this cut.
The local publisher must verify the seal and filesystem=index=HEAD.
NEXT-TARGET.md permits only a fresh baseline and exact identity-deletion declarations.
The adapter uses SAME completed H15 outputs; later cluster semantics retain width/Room.
Parent model admission stays explicit. Physical scan preservation is still open.
Generated parents, grouping, Mu/full pass, practical width, solver composition,
convergence and Haskell correspondence remain open. H6 stays strongest combined.
The whole goal stays active. Remote push needs the pending fresh direct approval.
No network publication ran.
''')
publisher = here / 'final-publication.py'
assert not (here / 'publication-gate.json').exists()
(here / 'publication-gate.json').write_text(json.dumps(dict(status='ROOT_ACCEPTED',
    proof_commit=proof, publication_scope='LOCAL_ONLY', network_publication='PENDING_USER_APPROVAL',
    publisher_sha256=hashlib.sha256(publisher.read_bytes()).hexdigest(),
    reason='Automatic approval review requires fresh direct destination and payload approval.',
    pending_exact_payload='47c597a8e3..562120d456', destination='git@github.com:TharkunAB/cfta.git',
    branch='formalize', whole_goal_complete=False), indent=2) + '\n')
print(json.dumps(dict(status='PASS', proof_commit=proof, root_metadata_failures=failures,
    next_target='deletion_sound', final_seal_pending=True)))
