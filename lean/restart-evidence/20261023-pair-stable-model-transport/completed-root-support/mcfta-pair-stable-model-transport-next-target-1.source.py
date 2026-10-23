import datetime
import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = ROOT / 'lean/restart-evidence/20261023-pair-stable-model-transport'
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

packages = [
    ('next-admission-inventory', 'a9ccd96257d1b552f9519db871794782ce91dd836c9960303948d2f3d7264f0b', 30),
    ('next-admission-audit', '369b958b66353bf4f5ede38d9ab42fa1bcbe3d7a4d0f4ec141f53bb0618b235b', 39),
]
for name, expected, count in packages:
    package = Path('/tmp/mcfta-pair-stable-model-transport-' + name)
    assert sha(package / 'pins.json') == expected and (package / 'FROZEN.json').exists()
    pins = json.loads((package / 'pins.json').read_text())
    if isinstance(pins, dict):
        pins = [dict(path=path, **pin) for path, pin in pins.items()]
    assert len(pins) == count
    for pin in pins:
        path = package / pin['path']
        assert path.stat().st_size == pin['bytes'] and sha(path) == pin['sha256'], path
    subprocess.run(['/usr/bin/python3', str(HERE / 'archive-extra.py'), str(package), name], check=True)
inventory = HERE / 'next-admission-inventory'
sources = json.loads((inventory / 'source-index.json').read_text())['sources']
cuts = 0
for entry in sources:
    path = ROOT / entry['path']
    data = path.read_bytes()
    assert sha(path) == entry['sha256'] and data == (inventory / entry['snapshot']).read_bytes()
    for cut in entry['cuts']:
        actual = b''.join(data.splitlines(True)[cut['start'] - 1:cut['end']])
        assert actual == (inventory / cut['snapshot']).read_bytes()
        cuts += 1
assert len(sources) == 10 and cuts == 15
review = dict(status='ROOT_NEXT_ADMISSION_SOURCE_INVENTORY_CLEAR',
    observed_at=datetime.datetime.now().astimezone().isoformat(), root_whole_note_plain_contract_and_all_cuts_read=True,
    root_whole_generic_Requests_source_read=True, source_identities=10, source_cuts=15,
    supplemental_complete_demand_and_type_headers_read=True, independent_review='next-admission-audit/review.json',
    independent_review_sha256=sha(HERE / 'next-admission-audit/review.json'),
    proposed_route='Existing generic Requests plus actual-control fuel induction. Pair admission only in call/order; actual capture readback at demand.',
    private_call_image_copy_required=False, native_coverage_conflated=False,
    new_declaration_authorized=False, body_authorized=False, compiler_authorized=False, whole_goal_complete=False)
(HERE / 'root-next-admission-review.json').write_text(json.dumps(review, indent=2) + '\n')
(HERE / 'NEXT-TARGET.md').write_text('''# Next proof boundary

H24 transports both Stable edge laws and exact finite ranks at one literal populated Wrapper.
It requires genuine old admission of every actual returned captured canonical request.
The first strict, sole FULL and sole Audit pass. The source has41 lines.
The whole formalization goal remains active. H6 remains strongest combined.

Derive request admission from actual comparison execution next.
Use the existing generic AdmissionCache.Requests on the separate Wrapper memo.
It must cover every stored cell in every phase, including cells with no table entry.
Preserve a genuine initial certificate and admission of the new requested full pair.
An actual completed H7 call must retain the all-cell certificate.
Use lookup, demand and finish preservation and demand_evaluate for the actual capture.
Generalize the observed-run induction over control and full state.
Require pair admission in call and order phases only. Swap its two conjuncts at reversal.
Native steps leave the pair memo unchanged. Return steps need no result-language law.
Do not copy the private call_image proof or introduce a phase framework.

At a stable boundary, returned status and genuine canonical returned admission
derive the initial all-phase certificate. The conditional result law cannot do so.
For literal original rows, row_inputs_meaning needs explicit parent model admission.
H15 does not supply it. H20 carries it for the same actual comparisons.
Reuse the already derived run. Do not assume future completion or final admission.
The source-only inventory and independent review retain10 live identities and15 cuts,
with complete demand and generic type-header supplements.
The90 to150-line estimate and180-line hard stop are proposals only.
Refresh the baseline and review exact declarations before implementation.

Then lift the certificate through group execution and reconstruction.
Native all-phase Covered and its actual reached-control checks remain separate.
Generated-root composition still needs concrete inventory admission and model/rank agreement.
New-source Trace, Room, native word ranges and fresh key safety remain open.
Mu traversal, the full public pass, Haskell refinement and convergence remain open.
No new Haskell repair is required. FINDINGS keeps the external repair index first.

Two root metadata commands failed: the initial SSH fetch and the first manifest archive.
The HTTPS fetch and corrected list-manifest archive passed. All attempts remain.
These commands and the retained inline preparation diagnostics are not proof jobs.
No proof repair or rejected FULL exists in H24. Seal and push are later root actions.
''')
print(json.dumps(review))
