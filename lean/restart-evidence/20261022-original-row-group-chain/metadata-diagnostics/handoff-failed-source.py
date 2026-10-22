import datetime
import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = ROOT / 'lean/restart-evidence/20261022-original-row-group-chain'
for name in ['next-inventory','next-audit']:
    path = Path('/tmp/mcfta-original-row-group-chain-' + name)
    for pin in json.loads((path / 'pins.json').read_text()):
        data = (path / pin['path']).read_bytes()
        assert len(data) == pin['bytes'] and hashlib.sha256(data).hexdigest() == pin['sha256']
    subprocess.run(['/usr/bin/python3',str(HERE / 'archive-extra.py'),str(path),name],check=True)

inventory = HERE / 'next-inventory'
audit = HERE / 'next-audit'
index = json.loads((inventory / 'source-index.json').read_text())
supplement = json.loads((audit / 'reviewed-source-scope.json').read_text())['supplemental_definitions']
identities = set()
counts = []
for base, sources in [(inventory,index['sources']),(audit,supplement)]:
    cuts = 0
    for source in sources:
        path = Path(source['path'])
        path = path if path.is_absolute() else ROOT / path
        data = path.read_bytes()
        assert data == (base / source['snapshot']).read_bytes()
        assert len(data) == source['bytes'] and len(data.splitlines()) == source['lines']
        assert hashlib.sha256(data).hexdigest() == source['sha256']
        identities.add(str(path))
        for cut in source['cuts']:
            excerpt = b''.join(data.splitlines(keepends=True)[cut['start']-1:cut['end']])
            assert excerpt == (base / cut['snapshot']).read_bytes()
            assert len(excerpt) == cut['bytes'] and hashlib.sha256(excerpt).hexdigest() == cut['sha256']
            cuts += 1
    counts.append(cuts)
assert counts == [28,12] and len(identities) == 26
review = dict(status='ROOT_SOURCE_ONLY_NEXT_TARGET_REVIEW_CLEAR',observed_at=datetime.datetime.now().astimezone().isoformat(),
    original_inventory_sources=20,original_inventory_cuts=28,supplemental_cuts=12,total_distinct_live_sources=26,
    root_read_all_40_cuts=True,root_whole_note_and_plain_contract_read=True,
    independent_review='next-audit/review.md',whole_dependency_manual_read_claimed=False,
    proposed_target='Reconstruct an ordinary original parent after the actual group chain',
    execution_boundary='Existing raw natural-index native work lifted through checked demand',
    fresh_width_generated_admission_or_new_source_room_claimed=False,
    declaration_body_or_compiler_authorized=False,whole_goal_complete=False)
(HERE / 'root-next-target-review.json').write_text(json.dumps(review,indent=2)+'\n')
proof = (HERE / 'proof-commit.txt').read_text().strip()
assert len(proof) == 40 and subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip() == proof
next_text = f'''# Next target: ordinary result reconstruction

H22 proves the finite original-parent symbol-group chain at {proof}.
The257-line source has SHA45ee19aba69aec9339203917841052791a389fe46f511ab9574105c8f3d254bb.
Strict1, sole FULL1 and Audit1 pass. Audit has3639 jobs and75499 dependencies.
The complete1156-line public TYPE and actual standard-three axioms are reviewed.
The one metadata installer failure and its exact schema repair remain retained.

Read next-inventory/note.md and proposed-contract.txt, then next-audit/review.md.
Read the twelve supplemental cuts in next-audit/reviewed-source-scope.json.
They complete Good.fields and Stable.canonical and retain public supporting APIs.
Root and independent review cover26 distinct identities and40 bounded cuts.
These are source-only plans. No next declaration, body or compiler is authorized.
Start a fresh baseline and propose exact context, public/private/local declarations
and a total source budget. Obtain root and independent declaration review first.

Restrict the parent to an actual original, available, admitted, closed ordinary node.
Run H22 once and use its actual last Wrapper and flattened selected rows.
Use existing makeNode raw work, native advance and the two-step checked-demand lift.
Derive result availability, Ordinary, closedness and all-ambient parent-language iff.
Use public source child provenance and node_free. Do not use the private childData proof.
Prove the small Stable transport across the literal heap-only update.
Retain both native memo tables, operation caches and the exact pair memo.
Compose the full packet, physical growth, issued history, effects and global Trace.
The result can be empty. No unchanged identity or literal unnormalized row list is claimed.

This is the existing raw natural-index work path. It adds no allocated-width check.
Keep the old initial-source Room separate from new-source capacity and fresh key safety.
Generated-root OriginalInput/admission, model/rank rebase, child traversal, Mu/union view
alignment, a common-fuel outer interpreter, Haskell refinement and convergence remain open.
H6 constructed_node_calls remains strongest combined. The whole goal stays active.
No Haskell repair is added. Keep FINDINGS repair index FIRST and all old evidence.

The older12, later exact8 and H21 two commits are pushed and remote-verified.
The user explicitly authorizes continued pushes to formalize. Publish the completed
H22 checkpoint after seal and local verification. The local publisher has no network command.
Do not post to the board. Retain the optimized interned core and all marked drafts.
'''
(HERE / 'NEXT-TARGET.md').write_text(next_text)
focused = ROOT / 'lean/notes-current-original-row-group-chain.md'
with focused.open('a') as out:
    out.write('\nOne root metadata installer failed on a manifest schema before any tool installation.\nThe failed input, corrected input and exact repair remain in metadata-diagnostics.\nThe auxiliary Audit warning count is corrected from0 to1; source warnings remain0.\nAll three Lean/Lake results remain unchanged.\n\n')
    out.write('Next target: read lean/restart-evidence/20261022-original-row-group-chain/NEXT-TARGET.md.\nThe next ordinary reconstruction contract remains source-only.\nFresh exact declaration review must precede any new body.\n')
publication = json.loads((HERE / 'bound-preparation/publication-gate.template.json').read_text())
assert publication['proof_commit'] == '__H22_PROOF_COMMIT__'
publication['proof_commit'] = proof
publication['status'] = 'ROOT_ACCEPTED'
assert publication['network_publication'] == 'AUTHORIZED_PENDING_ROOT_PUSH'
assert hashlib.sha256((HERE / 'final-publication.py').read_bytes()).hexdigest() == publication['publisher_sha256']
assert not (HERE / 'publication-gate.json').exists()
(HERE / 'publication-gate.json').write_text(json.dumps(publication,indent=2)+'\n')
with (HERE / 'current-progress.md').open('a') as out:
    out.write('\n## Proof commit and restart route\n\n')
    out.write(f'Proof commit {proof} contains only the new module and Audit import.\n')
    out.write('Both standalone saved-proof modes pass before all nine document prefixes are written.\n')
    out.write('All old document text remains by exact inverses. FINDINGS retains its repair index FIRST.\n')
    out.write('The next source-only inventory and independent supplements have26 distinct sources/40 cuts.\n')
    out.write('Ordinary result reconstruction is the next target. Fresh declarations remain unapproved.\n')
    out.write('Current goal turn: PROGRESS. The whole formalization stays active.\n')
    out.write('Final preservation, support capture, seal, local publication and authorized push remain pending.\n')
print(json.dumps({'status':'PASS','proof_commit':proof,'next_target_sources':26,'next_target_cuts':40,'future_body_authorized':False}))
