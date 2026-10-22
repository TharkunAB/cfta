import ast
import datetime
import hashlib
import json
from pathlib import Path

here = Path('/home/tritlo/Code/mcfta/lean/restart-evidence/20261022-original-row-cluster-completion')
def sha(data):
    return hashlib.sha256(data).hexdigest()
components = ['checkpoint-preparation', 'checkpoint-preparation-audit', 'full-preparation', 'full-reader-audit']
for component in components:
    package = here / component
    manifest = json.loads((package / 'pins.json').read_text())
    pins = manifest['files'] if 'files' in manifest else manifest
    for name, pin in pins.items():
        data = (package / name).read_bytes()
        assert sha(data) == pin['sha256'], (component, name)
        if 'bytes' in pin:
            assert len(data) == pin['bytes'], (component, name)
scripts = ['verify-preservation.py', 'verify-checkpoint.py', 'commit-proofs.py',
    'archive-support.py', 'seal-checkpoint.py', 'verify-seal.py', 'final-publication.py', 'update-documents.py']
lengths = [len((here / 'checkpoint-preparation' / name).read_bytes().splitlines()) for name in scripts]
assert lengths == [127, 44, 55, 16, 26, 16, 47, 199] and sum(lengths) == 530
for name in scripts:
    ast.parse((here / 'checkpoint-preparation' / name).read_text())
for name in ['check-full-public.py', 'prepare-selected-full.py']:
    ast.parse((here / 'full-preparation' / name).read_text())
reviews = {'checkpoint-preparation-audit/review.md': '4e9424bf861174a2495f9ae488c6207ea2cc2a859b1c6598b27f70dc80e55c01',
    'full-reader-audit/review.md': 'eade742d4fe2531f49ef352af1f678536ec541dd04354ad87df60c55a64c8efa'}
assert all(sha((here / name).read_bytes()) == expected for name, expected in reviews.items())
report = dict(status='ROOT_SOURCE_CLEAR_PENDING_ACTUAL_PROOF_AND_BINDINGS',
    observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    root_read_whole_eight_checkpoint_scripts=True, checkpoint_script_lines=530,
    root_read_whole_full_reader_materializer_and_tail=True,
    full_tool_lines=[105, 47, 14], independent_reviews=reviews,
    actual_source_strict_full_type_audit_ledger_and_bound_tool_review_pending=True,
    prepared_tool_activation_authorized=False, compiler_authorized=False,
    source_cap_lines=350, default_limits_required=True, network_publication_authorized=False)
output = here / 'root-tool-template-review.json'
assert not output.exists()
output.write_text(json.dumps(report, indent=2) + '\n')
progress = here / 'current-progress.md'
archive = here / 'initial-current-progress.md'
assert not archive.exists()
archive.write_bytes(progress.read_bytes())
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
progress.write_text('# Genuine original-row cluster completion\n\nUpdated: ' + now + '.\n\n'
    'The fresh upstream pull and88001-file baseline passed. H16 remains sealed.\n'
    'Root and independent review cleared the exact17/51/7/62 declarations.\n'
    'root-signature-review.json authorizes one external complete source draft.\n'
    'The draft must retain actual cluster completion and all current invariants.\n'
    'The SAME fixed source/models, populated state, initial domain cache and Trace remain.\n'
    'Only two private helpers are allowed. The source hard stop is350 lines.\n'
    'The full local generalized induction statement counts toward that limit.\n'
    'The pending checkpoint and FULL templates passed whole source review.\n'
    'No H17 Lean command has run. Compiler and prepared-tool activation remain pending.\n'
    'No Haskell source or repair changes. FINDINGS keeps the repair index first.\n'
    'Physical pruning, grouping, generated parents, Mu and the public pass remain open.\n'
    'H6 remains the strongest combined semantic theorem. The whole goal stays active.\n'
    'Remote publication still needs the pending fresh direct user approval.\n')
print(json.dumps({'status': 'PASS', 'template_review_sha256': sha(output.read_bytes())}))
