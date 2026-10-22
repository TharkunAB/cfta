import datetime
import hashlib
import json
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
here = root / 'lean/restart-evidence/20261022-original-row-deletion-soundness'
proof = (here / 'proof-commit.txt').read_text().strip()
verified = json.loads((here / 'verification.json').read_text())
assert verified['status'] == 'PASS' and verified['actual_jobs'] == 3 and verified['failed_jobs'] == 0
assert verified['both_proof_verification_modes'] and verified['baseline_files'] == 90717
assert (here / 'NEXT-TARGET.md').is_file()
failures = []
for path in Path('/tmp').glob('mcfta-original-row-deletion-soundness-*.json'):
    item = json.loads(path.read_text())
    if isinstance(item, dict) and 'wrapper' in item and 'exit_code' in item and item['exit_code']:
        failures.append(path.name)
assert failures == [], failures
assert not (here / 'metadata-status.md').exists()
(here / 'metadata-status.md').write_text('''# Metadata execution status

No root capped metadata command failed before this pre-seal status.
The first strict source, sole FULL and Audit commands all pass.
Owner and reviewer static preparation diagnostics remain in their frozen packages.
They include the owner let-header assembly check and reviewer schema inspections.
The independent source-review capacity interruption did not execute a proof command.
These preparation events are separate from root metadata and Lean/Lake jobs.
The one-shot completed-root-support archive must retain all current root receipts.
''')
note = root / 'lean/notes-current-original-row-deletion-soundness.md'
addition = '''
Audit replays the old inputs unused-variable warning from
InternedFreshOrdinaryClosedCompletion. The selected strict and FULL logs are clean.
No root capped metadata command failed before the pre-seal status.
Read metadata-status.md for the separate owner and reviewer preparation events.
Read NEXT-TARGET.md for the reviewed next scan-language construction route.
Only a fresh baseline and exact next declarations are authorized by that plan.
'''
assert 'Audit replays the old inputs unused-variable warning' not in note.read_text()
note.write_text(note.read_text() + addition)
timestamp = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
(here / 'preseal-previous-current-progress.md').write_bytes((here / 'current-progress.md').read_bytes())
(here / 'current-progress.md').write_text(f'''# Original-row deletion soundness: pre-seal status

Updated: {timestamp}. Proof commit: {proof}.

The selected105-line theorem, clean strict1, sole FULL1 and Audit1 are accepted.
Audit has3636 jobs and75454 theorem dependencies. All three proof commands pass.
Audit replays the old inputs warning. No new source warning or repair occurred.
Root and independent review read all256 checked TYPE lines. Printed bytes agree.
TYPE has no private markers or helpers. Actual axioms are the standard three.
The complete body remains retained and checked programmatically.
Normal and live saved-evidence checks pass from cwd=/ with explicit root.
Preservation passes for90717 baseline files/modes,3634 older non-Audit Lean sources,
298 Haskell files,207 package files and303 frozen registries/1397 entries/five overrides.
Nine document prefixes retain exact inverses. FINDINGS keeps the Haskell index FIRST.
No Haskell repair is required. The original Audit has its exact sole-import inverse.
No root capped metadata command failed before this cut.
Final independent document review, support archive and seal remain pending.
The local publisher must verify the seal and filesystem=index=HEAD.
NEXT-TARGET permits a fresh baseline and exact cluster-language declaration proposal.
The proposed concrete strengthened construction must keep the SAME H15 witnesses,
full current packets, genuine width/global Room/Trace and same-model parent admission.
The scan language invariant is still open. No new scan execution is proved by H19.
Grouping, reconstruction, generated parents, Mu/full pass, practical width,
solver composition, convergence and Haskell correspondence remain open.
H6 remains the strongest combined result. The whole goal stays active.
Remote push still requires the pending fresh direct destination/payload approval.
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
    next_target='cluster_complete_with_language', final_seal_pending=True)))
