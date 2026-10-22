import datetime
import json
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
here = root / 'lean/restart-evidence/20261022-original-row-cluster-completion'
proof = (here / 'proof-commit.txt').read_text().strip()
verified = json.loads((here / 'verification.json').read_text())
assert verified['status'] == 'PASS' and verified['actual_jobs'] == 5 and verified['failed_jobs'] == 2
assert verified['both_proof_verification_modes'] and verified['baseline_files'] == 88001
assert (here / 'NEXT-TARGET.md').is_file()
note = root / 'lean/notes-current-original-row-cluster-completion.md'
addition = '''
Strict1 failed at the missing nodeEdges namespace and reserved local prefix names.
Strict2 failed at ITE reduction order and the empty-cluster length reflexivity goal.
The exact repairs retain the approved context and declarations. All four source
variants, including the original340-line draft, three patches and all raw checks remain.
Read metadata-repairs.md in this checkpoint for the one root metadata failure
and its missing-baseline-archive repair. Reviewer-only diagnostics are separate.
Read NEXT-TARGET.md in this checkpoint for the exact next semantic bridge.
Only a fresh baseline and exact statement proposal are authorized next.
'''
assert 'Strict1 failed at the missing' not in note.read_text()
note.write_text(note.read_text() + addition)
timestamp = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
(here / 'post-audit-current-progress.md').write_bytes((here / 'current-progress.md').read_bytes())
(here / 'current-progress.md').write_text(f'''# Original-row cluster completion: pre-seal status

Updated: {timestamp}. Proof commit: {proof}.

The selected345-line theorem, clean strict3, sole FULL and aggregate Audit are accepted.
Audit has3634 jobs and75451 theorem dependencies. Five actual jobs include two failures.
Normal and live saved-evidence checks pass from cwd=/ with explicit root.
The88001-file baseline,3632 older non-Audit Lean sources,298 Haskell files,
207 active package files and301 older frozen registries/1395 entries remain preserved.
Nine additive doc prefixes retain exact inverses. FINDINGS keeps the Haskell index FIRST.
The original Audit archive is exact; its only source edit is the new import.
All failed inputs, repair patches and metadata diagnostics remain.
Final independent document review, support archive and seal are pending at this pre-seal cut.
The local publisher must rerun the seal checks and verify filesystem=index=HEAD.
NEXT-TARGET.md authorizes only a fresh baseline and pure row-meaning statement proposal.
Physical pruning semantics, grouping/generated parents/Mu/full pass and Haskell refinement remain.
H6 remains the strongest combined semantic theorem. The whole goal stays active.
Remote push still needs the pending fresh direct approval. No network publication ran.
''')
(here / 'publication-gate.json').write_text(json.dumps(dict(status='ROOT_ACCEPTED',
    proof_commit=proof, publication_scope='LOCAL_ONLY', network_publication='PENDING_USER_APPROVAL',
    reason='Automatic approval review requires fresh direct destination and payload approval.',
    pending_exact_payload='47c597a8e3..562120d456', destination='git@github.com:TharkunAB/cfta.git',
    branch='formalize', whole_goal_complete=False), indent=2) + '\n')
print(json.dumps(dict(status='PASS', proof_commit=proof, next_target='row_inputs_meaning', final_seal_pending=True)))
