import datetime
import hashlib
import json
import sys
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
here = root / 'lean/restart-evidence/20261022-prepend-grouping'
sha = lambda raw: hashlib.sha256(raw).hexdigest()
review_sha = sys.argv[1]
assert sha((here / 'next-traversal-audit/review.md').read_bytes()) == review_sha
assert sha((here / 'final-document-review/review.md').read_bytes()) == '47b931f8fe471963500db5ed4b02a1cf014d21310d80f9023a234a265a78faa0'
assert json.loads((here / 'verification.json').read_text())['status'] == 'PASS'
sources, cuts = set(), 0
for name in ['next-traversal-inventory','next-traversal-inventory-scope-erratum']:
    component = here / name
    for pin in json.loads((component / 'pins.json').read_text()):
        raw = (component / pin['path']).read_bytes()
        assert len(raw) == pin['bytes'] and sha(raw) == pin['sha256']
    for source in json.loads((component / 'source-index.json').read_text())['sources']:
        raw = Path(source['path']).read_bytes()
        assert sha(raw) == source['sha256'] and len(raw) == source['bytes']
        lines = raw.splitlines(True)
        assert len(lines) == source['lines']
        sources.add(source['path'])
        if 'snapshot' in source:
            assert (component / source['snapshot']).read_bytes() == raw
        for span in source['reviewed_ranges']:
            assert 1 <= span['start'] <= span['end'] <= len(lines)
            data = b''.join(lines[span['start']-1:span['end']])
            assert data == (component / span['excerpt']).read_bytes()
            assert len(data) == span['bytes'] and sha(data) == span['sha256']
            cuts += 1
assert len(sources) == 15 and cuts == 27
gate = dict(status='ROOT_SOURCE_ONLY_NEXT_PLAN_CLEAR',review_sha256=review_sha,
    primary_sources=len(sources),selected_ranges=cuts,root_read_all_indexed_cuts=True,
    current_bytes_and_ranges_verified=True,per_group_concrete_fuels_and_same_evolving_wrapper=True,
    same_initial_room_and_global_trace=True,literal_nodeEdges_view_only=True,
    haskell_mu_and_union_view_correspondence_open=True,generated_parent_admission_open=True,
    new_headers_bodies_or_compiler_authorized=False,whole_goal_complete=False)
(here / 'root-next-traversal-review.json').write_text(json.dumps(gate,indent=2) + '\n')
next_text = '''# Next target: actual original-parent symbol-group chain

H21 proves the pure singleton-prepend, final reversal and iterator bridge.
The selected89-line source has SHA3d293c27b502aa308c8cc05f21796264b18f873221b3343910e77d6bcb6b53ba.
Clean strict3, sole FULL1 and Audit1 pass. The five-job history retains two failed stricts.
The metadata reader failure and its whitespace repair remain separate.

Read next-traversal-inventory/note.md and proposed-contract.txt.
Also read next-traversal-inventory-scope-erratum/note.md and next-traversal-audit/review.md.
These are source-only plans. No next Lean declaration, body or check is approved.
Start a fresh baseline and propose exact context, public/private/local statements
and a total line budget. Obtain root and independent declaration review first.

Use symbol alone and the supplied finite iterator order. H21 plus the existing
lookup laws identify each reversed bucket with its exact original symbol filter.
Produce a finite chain of actual H16 group runs from H20, with one concrete fuel
per group and the SAME evolving complete Wrapper. Keep source, model, ranks,
width and initialDomains fixed. Retain every global Trace and current invariant.
Reuse the genuine initial Room tuple. Do not assume future capacity or completion.
Derive cumulative extension and all-ambient physical union iff for flattened output.
Do not assert equal final heaps across iterator orders or a common-fuel outer program.

The row view is H20's literal modeled nodeEdges. Its Mu case is empty and vacuous.
Haskell nodeEdges unfolds Mu and collects union alternatives. That correspondence is open.
The public pass first rebuilds children. Its generated parents need new admission/rebase.
Actual outer traversal refinement, reconstruction, generated parents, Mu/full pass,
practical width, solver contracts, Haskell refinement and convergence remain open.
H6 constructed_node_calls remains the strongest combined semantic theorem.
The whole goal stays active. No Haskell source change or repair is added.
The approved older12 commits were pushed through562120d456.
Newer commits require the separately requested exact-payload approval.
'''
assert not (here / 'NEXT-TARGET.md').exists()
(here / 'NEXT-TARGET.md').write_text(next_text)
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
proof = (here / 'proof-commit.txt').read_text().strip()
progress = f'''
## Later update: checked proof and restart handoff

Updated: {now}. Proof commit: {proof}.

The official89-line module is installed with the sole new Audit import.
Clean strict3 and sole FULL1 pass. Root and independent review read all nine complete TYPEs.
All nine pairs agree under four-character ASCII whitespace normalization.
Seven pairs also agree byte-for-byte. Both raw TYPEs and the actual flags remain.
Reader2 passes on the unchanged FULL. Reader1's six failed metadata artifacts remain.
The saved verifier V2 stale-reader-path defect was found before execution.
The original CLEAR, additive HOLD erratum and exact V3 dual-reader repair remain.

Audit1 passes at3638 jobs/75494 dependencies. Actual proof jobs total5:
four source checks and one Audit, two failures, zero warned source passes and zero rejected TYPEs.
All four math drafts, actual inputs, raw errors and three exact repairs remain.
Root and independent review read all805 bound tool lines and retain all270 assertions.
Normal and live saved-proof checks passed before document writes.
The nine exact document inverses and baseline preservation pass.
Preservation covers93582 files/modes,3636 older Lean sources,298 Haskell files,
207 active package files and305 frozen registries/1399 entries with five inherited overrides.
FINDINGS keeps its Haskell repair index FIRST. No Haskell change or repair is added.

Read NEXT-TARGET.md for the reviewed source-only finite group-chain plan.
Its literal row view does not prove Haskell Mu/union unfolding or generated-parent admission.
No next header, body or compiler command is approved. H6 remains strongest combined.
The older approved12-commit push is complete at562120d456; newer exact8 approval is pending.
The seal and local publisher run after this dated cut. This entry predicts no outcome.
The whole goal stays active.
'''
with (here / 'current-progress.md').open('a') as stream:
    stream.write(progress)
publication = json.loads((here / 'checkpoint-preparation-v2/publication-gate.template.json').read_text())
assert publication['proof_commit'] == '__H21_PROOF_COMMIT__'
assert sha((here / 'final-publication.py').read_bytes()) == publication['publisher_sha256']
publication.update(status='ROOT_ACCEPTED',proof_commit=proof,
    root_document_review_sha256='47b931f8fe471963500db5ed4b02a1cf014d21310d80f9023a234a265a78faa0',
    root_review='Reviewed all nine additions and their exact inverses, focused note, source/TYPE scope, retained histories and local-only publication guards.')
assert not (here / 'publication-gate.json').exists()
(here / 'publication-gate.json').write_text(json.dumps(publication,indent=2) + '\n')
print(json.dumps(dict(status='PASS',next_plan_source_only=True,primary_sources=len(sources),selected_ranges=cuts,proof=proof,publication_scope='LOCAL_ONLY',seal_and_local_publication='PENDING')))
