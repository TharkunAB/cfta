import hashlib
import json
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
here = root / 'lean/restart-evidence/20261023-original-row-reconstruction'
proof = (here / 'proof-commit.txt').read_text().strip()
assert len(proof) == 40
assert json.loads((here / 'proof-evidence-normal.json').read_bytes())['status'] == 'PASS'
assert json.loads((here / 'proof-evidence-live.json').read_bytes())['status'] == 'PASS'
api_source = root / 'lean/MicroCFTA/FlatMemoThunk.lean'
api_bytes = api_source.read_bytes()
api_text = api_bytes.decode()
api_start = api_text.index('/-- Every table entry identifies its original request')
api_end = api_text.index('/-- A hit returns the original thunk.')
api_cut = api_text[api_start:api_end].encode()
(here / 'root-next-flat-memo-api.txt').write_bytes(api_cut)
(here / 'root-next-flat-memo-api.json').write_text(json.dumps(dict(
    source='lean/MicroCFTA/FlatMemoThunk.lean', source_sha256=hashlib.sha256(api_bytes).hexdigest(),
    start=api_text[:api_start].count('\n') + 1, end=api_text[:api_end].count('\n'),
    snapshot='root-next-flat-memo-api.txt', cut_sha256=hashlib.sha256(api_cut).hexdigest(),
    scope='Root read the complete Valid structure, empty_valid and Valid.map API and proof. No next declaration approval.'), indent=2) + '\n')
target = here / 'NEXT-TARGET.md'
assert not target.exists()
target.write_text(f'''# Next target: populated wrapper model transport

H23 proves ordinary original-row reconstruction at {proof}.
The selected210-line source has SHA69ed5b8d01f7bcd1d21aa4a66206c9f0bc9480c728c695bfafd7e8222621e435.
Strict1 failed with two parsing errors. Its exact input and log remain.
The syntax-only parenthesis repair passes strict2 and the sole FULL1.
Audit1 passes with3640 jobs and75501 theorem dependency checks.
Root and independent review cover the complete1951-line checked public TYPE.
Both raw TYPE views are byte-identical. Only the three standard axioms occur.
The whole formalization goal stays ACTIVE. H6 remains strongest combined.

Read next-admission-inventory/note.md and proposed-next-contract.txt.
Then read next-admission-audit/review.md and both additional complete-field cuts.
The inventory pins12 live Lean identities and one historical proposed header.
Root and independent review cover all16 indexed cuts and both supplements.
The separate root-next-flat-memo-api snapshot records the stored-cell API.
The historical header predates the syntax repair. Its scope conclusions still apply.
This is a source-only plan. No next declaration, body or compiler is authorized.
After H23 publication, start a fresh baseline. Review exact public, private and
local declarations and a total source budget before proof implementation.

Keep one actual populated Wrapper unchanged. Use two concrete finite input
interpretations connected by ContextRebase.Agreement, with the same holds.
Require old Stable and genuine old EdgeInputs for the canonical empty-domain
request captured in every returned wrapper memo cell. Derive new Stable.
Preserve all physical records, phases, keys, counters and canonical witnesses.
Retain both contextual soundness and bounded completeness, including ranks.
Use existing edge_law and empty_seen. Do not supply the desired new result law.
FlatMemoThunk.Valid.checked exposes each actual stored cell and handle.
Valid.map alone lacks the stored-cell hypothesis needed to use that admission.

Then derive admission from actual fresh pair publications and preserve older cells.
Native Covered is a separate invariant for native memo requests in all phases.
AdmissionExecution follows actual reached controls but still needs RequestsThrough.
Do not confuse native seen-pair admission with the separate wrapper pair memo.
An arbitrary populated start needs a genuine initial coverage certificate.
The fixed arbitrary H23 model does not supply a concrete Inventory.At certificate.
Existing grown-inventory and InventoryRebase producers admit closed resident roots
when their actual incoming concrete inventory and coverage requirements hold.
Keep old-source global Trace literal. New-source Trace, Room, WordRanges and
fresh-result word-key safety are separate resource obligations.

Generated-parent traversal, an outer group interpreter, Mu/union view alignment,
the public pass, Haskell refinement, practical width and convergence remain open.
No Haskell repair is added. FINDINGS keeps its repair index FIRST.
Keep all prior proofs, counterexamples, drafts and the optimized interned core.
The user authorizes pushes to origin/formalize. Publish H23 after seal and local
verification. The local publisher has no network command; root performs the push.
Do not post to the board. Do not update memory or create an ADR.
''')
with (here / 'current-progress.md').open('a') as stream:
    stream.write('\n## Integrated proof and restart route\n\n'
        f'Audit1 passes with3640jobs and75501dependencies. Proof checkpoint:{proof}.\n'
        'Both standalone saved-proof modes pass before documentation changes.\n'
        'The nine additive document updates preserve all previous text and the first repair index.\n'
        'The next source-only route retains populated caches and explicit old request admission.\n'
        'Final preservation, sealing, local publication and root push are subsequent steps.\n'
        'The whole formalization goal remains ACTIVE. No new Haskell repair is required.\n')
with (root / 'lean/notes-current-original-row-reconstruction.md').open('a') as stream:
    stream.write('\n## Next composition requirement\n\n'
        'Existing grown-inventory producers admit listed closed resident roots.\n'
        'The fixed arbitrary model used here does not supply their concrete Inventory.At.\n'
        'Preserve native request coverage and wrapper captured-child admission at actual publications.\n'
        'Then transport the same populated wrapper under finite input agreement.\n'
        'Read the checkpoint NEXT-TARGET.md and the two reviewed admission packages.\n')
print(json.dumps(dict(status='PASS', proof=proof, next_target=str(target), whole_goal_complete=False)))
