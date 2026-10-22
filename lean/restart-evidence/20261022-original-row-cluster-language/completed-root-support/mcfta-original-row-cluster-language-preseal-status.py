import datetime
import hashlib
import json
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
here = root / 'lean/restart-evidence/20261022-original-row-cluster-language'
def sha(data):
    return hashlib.sha256(data).hexdigest()
proof = (here / 'proof-commit.txt').read_text().strip()
verified = json.loads((here / 'verification.json').read_text())
assert verified['status'] == 'PASS' and verified['actual_jobs'] == 4 and verified['failed_jobs'] == 0
assert verified['warned_source_exit_zero_jobs'] == 1 and verified['rejected_public_type_jobs'] == 0
assert verified['both_proof_verification_modes'] and verified['baseline_files'] == 91951
assert verified['audit_build_jobs'] == 3637 and verified['audit_dependencies'] == 75482
package = here / 'next-grouping-inventory'
pins = json.loads((package / 'pins.json').read_text())
assert isinstance(pins, list) and len(pins) == 37
for pin in pins:
    raw = (package / pin['path']).read_bytes()
    assert sha(raw) == pin['sha256'] and len(raw) == pin['bytes']
index = json.loads((package / 'source-index.json').read_text())
assert len(index['sources']) == index['source_count'] == 11
cuts = 0
for item in index['sources']:
    raw = Path(item['actual_path']).read_bytes()
    assert sha(raw) == item['sha256'] and raw == (package / item['snapshot']).read_bytes()
    for cut in item['ranges']:
        excerpt = b''.join(raw.splitlines(True)[cut['start'] - 1:cut['end']])
        assert sha(excerpt) == cut['sha256'] and excerpt == (package / cut['snapshot']).read_bytes()
        cuts += 1
assert cuts == index['range_count'] == 22
failures = []
for path in sorted(Path('/tmp').glob('mcfta-original-row-cluster-language-*.json')):
    item = json.loads(path.read_text())
    if isinstance(item, dict) and 'wrapper' in item and item.get('exit_code', 0) != 0:
        failures.append(path.name)
assert failures == ['mcfta-original-row-cluster-language-activate-full-1.json']
assert all(not (here / name).exists() for name in ['metadata-status.md', 'NEXT-TARGET.md',
    'next-grouping-root-inventory.json', 'publication-gate.json', 'preseal-previous-current-progress.md'])
(here / 'next-grouping-root-inventory.json').write_text(json.dumps(dict(
    status='SOURCE_INVENTORY_RETAINED_FRESH_REVIEW_REQUIRED',
    root_read_note_and_bridge=True, root_verified_live_source_and_range_bytes=True,
    sources=11, cuts=22, root_claims_complete_math_API_review=False,
    exact_declarations_independent_review_body_and_compiler_gates_pending=True,
    next_body_or_compiler_authorized=False, whole_goal_complete=False), indent=2) + '\n')
(here / 'NEXT-TARGET.md').write_text('''# Next target: literal symbol-grouping bridge

H20 cluster_complete passes clean strict2, sole FULL1 and Audit1.
Its393-line source has SHA e1c54fe63f95392a928cf539b108a061b64101596a3fc6bfc5c09b72a030eba8.
It constructs one original symbol-group scan and proves physical kept-union iff.
It retains the same populated state packet, genuine initial Room and global Trace.

Read next-grouping-inventory/note.md and bridge.md as SOURCE-ONLY inventory.
The inventory has11 primary sources and22 exact cuts. Its equations are unproved.
Haskell prepends singletons and reverses each final bucket. Existing generic
SourceCurrentMergeGrouping.fromRows appends singletons in input order.
The proposed next slice proves the optional-bucket reverse bridge and iterator transport.
Use the symbol key alone. The specialized merge key also contains child count.
Preserve None versus Some, input order and all repeated occurrences.
Do not fix HashMap group order or claim heap equality across iterator orders.
Actual HashMap storage/iteration refinement remains an explicit open boundary.

Start a fresh baseline. Read the primary APIs and obtain independent review.
Propose exact module context, every public/private/local statement and a total line budget.
Review those declarations before any body or compiler command. Keep old modules unchanged.
This inventory authorizes no new Lean declaration, body, helper or check.
A later concrete group traversal must carry H20's actual returned wrapper,
fixed source/model/parent/width/initialDomains and same global allocation Trace.
Do not reset histories or assume future completion, Room or language equality.

Grouping execution, reconstruction, generated parents, Mu/full pass, practical width,
external solver composition, Haskell refinement and convergence remain open.
H6 constructed_node_calls remains the strongest combined trace theorem.
The whole goal stays active. The approved12-commit push is complete.
Newer local work requires fresh exact-payload approval before a push.
''')
(here / 'metadata-status.md').write_text('''# Metadata execution status

One root capped metadata command failed before this cut: FULL activation1.
It stopped at the strict empty-log gate after strict1 returned one linter warning.
No helper was copied and no FULL Lean command ran in that attempt.
The six original metadata artifacts remain in source-proposal-v2 and root support.
This is separate from the four actual Lean/Lake commands, which all exit zero.
Strict1 has one unused-simp warning. The exact one-line repair yields clean strict2.
The sole FULL1 and Audit1 pass. No PUBLIC TYPE rejection occurred.
Owner and reviewer static preparation diagnostics remain in their frozen packages.
They are not root capped metadata failures or additional proof commands.
The one-shot support archive must retain every current root receipt.
''')
note = root / 'lean/notes-current-original-row-cluster-language.md'
addition = '''
Audit replays the old inputs unused-variable warning from
InternedFreshOrdinaryClosedCompletion. Selected strict2 and FULL1 are clean.
The earlier strict1 warning, exact repair and stopped Python activation remain.
Read metadata-status.md for the separate metadata and preparation records.
Read NEXT-TARGET.md for the source-only grouping inventory and fresh review gates.
No next mathematical body or compiler command is authorized by that inventory.
'''
assert 'Audit replays the old inputs unused-variable warning' not in note.read_text()
note.write_text(note.read_text() + addition)
timestamp = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
(here / 'preseal-previous-current-progress.md').write_bytes((here / 'current-progress.md').read_bytes())
(here / 'current-progress.md').write_text(f'''# Original-row cluster language: pre-seal status

Updated: {timestamp}. Proof commit: {proof}.

The393-line cluster_complete constructs one modeled original symbol-group scan.
For every ambient environment and finite term, kept and original filtered rows
have the same physical union language. Every earlier H17 packet output remains.
The source/model/parent admission, genuine width/global Room and global Trace stay fixed.
Strict1 warned once. The one-line unused-simp repair passes clean strict2.
Sole FULL1 and Audit1 pass. Audit has3637 jobs and75482 theorem dependencies.
All four actual Lean/Lake commands exit zero. No PUBLIC TYPE was rejected.
Root and independent review read all725 checked TYPE lines. Printed bytes agree.
Both private helpers and four private markers are absent. Actual axioms are the standard three.
The complete proof body remains retained and checked programmatically.
Audit replays the old inputs warning. One stopped FULL-activation Python failure remains separate.
Standalone normal/live evidence checks pass from cwd=/ with explicit root before document writes.
Preservation covers91951 baseline files/modes,3635 older non-Audit Lean sources,
298 Haskell files,207 package files and304 registries/1398 entries/five overrides.
All nine document prefixes have exact inverses. FINDINGS keeps its Haskell index FIRST.
No new Haskell repair is required. The Audit edit has its exact sole-import inverse.
Final document review, support archive, mandatory final verification and seal are pending.
The local publisher must check the seal and filesystem=index=HEAD.
NEXT-TARGET retains only source inventory for a literal symbol-grouping bridge.
A fresh baseline and exact declaration review must precede any future body or check.
Grouping execution, reconstruction, generated parents, Mu/full pass, practical width,
solver composition, Haskell refinement and convergence remain open.
H6 remains the strongest combined trace result. The whole goal stays active.
The approved12-commit push through562120d456 is complete. Newer payloads need fresh approval.
This checkpoint remains local. No network publication ran for its newer work.
''')
publication = json.loads((here / 'checkpoint-preparation/publication-gate.template.json').read_text())
publication.update(status='ROOT_ACCEPTED', proof_commit=proof,
    publisher_sha256=sha((here / 'final-publication.py').read_bytes()))
assert publication['publication_scope'] == 'LOCAL_ONLY'
(here / 'publication-gate.json').write_text(json.dumps(publication, indent=2) + '\n')
print(json.dumps(dict(status='PASS', proof_commit=proof, retained_root_metadata_failures=failures,
    next_inventory_only=True, final_seal_pending=True)))
