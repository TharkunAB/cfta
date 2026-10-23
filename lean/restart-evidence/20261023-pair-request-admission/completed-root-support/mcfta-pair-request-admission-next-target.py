import datetime
import runpy
globals().update(runpy.run_path('/tmp/mcfta-pair-request-admission-root-common.py'))

source = Path('/tmp/mcfta-pair-request-admission-next-inventory')
audit = Path('/tmp/mcfta-pair-request-admission-next-inventory-audit')
checked_package(source, 'eb1bf15055c9ec0917f5f408f1cfdc42fcdfd7b70c13ccacdfeb36f7edfa03a3',
    'a28d7c3192328f0161a77e8e25cbd676613bd970caf1818fd7b65b2e35a6b9f4')
checked_package(audit, '1c3437edf77d928977f88163a6d9477f8b833619bb5c6aae13838d677dc584c2',
    '6633ec2a54ce69c92fc055051452c0403db740c4a33f76a63135bf1d2e1f0633')
assert load(audit / 'review.json')['status'] == 'CLEAR'
assert sha(audit / 'review.json') == '6526dcfbe22dcebc38eb49bbf7b293710f2cf7ffa5231b726d626898efd632a7'
index = load(source / 'source-index.json')
assert len(index['sources']) == 10
count = lines = 0
for item in index['sources']:
    path = ROOT / item['path']
    data = path.read_bytes()
    assert data == (source / item['snapshot']).read_bytes()
    assert sha(path) == item['sha256'] and len(data) == item['bytes']
    assert len(data.splitlines()) == item['lines']
    for cut in item['cuts']:
        retained = source / cut['snapshot']
        assert retained.read_bytes() == b''.join(data.splitlines(True)[cut['start']-1:cut['end']])
        assert sha(retained) == cut['sha256'] and retained.stat().st_size == cut['bytes']
        count += 1
        lines += cut['end'] - cut['start'] + 1
assert count == 13
archive(source, 'next-admission-inventory')
archive(audit, 'next-admission-audit')
save('root-next-admission-review.json', dict(status='SOURCE_ONLY_ROUTE_CLEAR',
    observed_at=datetime.datetime.now().astimezone().isoformat(), root_read_whole_note_and_plain_contract=True,
    root_read_all_selected_cuts=True, source_identities=10, source_cuts=13, cut_lines=lines,
    independent_review='CLEAR', next_component='Native Covered-only augmentation of the SAME H13 BOTH-miss result',
    actual_scope_ready_empty_domain_API_pins_still_required=True, exact_declaration_gate_required=True,
    source_estimate=[140,180], estimate_is_not_authority=True, new_header_authorized=False,
    body_authorized=False, compiler_authorized=False, whole_goal_complete=False))
target = HERE / 'NEXT-TARGET.md'
assert not target.exists()
target.write_text('''# Current proof and next target

The whole formalization goal remains ACTIVE. This component makes PROGRESS.
H25 completed_admitted is checked at the same observed H7 result and full state.
Incoming Stable, genuine old returned canonical admission and current pair
admission derive final all-cell Requests and actual returned canonical admission.
The local induction follows actual lookup, demand, order, native and return.
The strict log is empty. The sole FULL and Audit pass. The public TYPE has441
logical lines and32076 bytes. Root and independent reviews read every TYPE line.
The two raw TYPE views match. The BODY remains programmatic evidence only.
Actual axioms are Classical.choice, Quot.sound and propext.
Audit has3642 jobs and75503 dependencies. Only the old inputs warning remains.
There are three actual Lean/Lake jobs and no failed or warned source job.
The uncompiled156-line draft, selected157-line source and exact annotation patch remain.
Four failed root metadata attempts and four successful retries remain separate.
No Haskell source changed. FINDINGS keeps its external repair index first.
H6 constructed_node_calls remains the strongest combined semantic theorem.

Next derive native Covered for the SAME H13 BOTH-miss comparison.
Read next-admission-inventory and next-admission-audit. Both are source-only.
Reuse public AdmissionTrace.Trace.covered and the derived CoveredQuery.branches.
Use H18 with genuine parent model admission for actual row-child admission.
Derive the literal edgeBody certificate and current fields. Retain the exact
H13 result, full after state, native Receipt, Stable, Idle and memo tuple.
Do not replace that witness with another execution or an assumed final certificate.
The next exact declaration gate must pin public residency, growth and empty-domain
scope/readiness/seen facts. The prospective140–180 lines do not authorize a body.
Start with native Covered only. Add same-run H25 pair admission in a later
component unless its complete exact contract fits the separately reviewed cap.
Ready hits have no native Receipt. Keep their actual checked-state equality.

H20/H22 hide internal pair-run witnesses. H16 comparison_lift is forward only.
Do not project hidden H7 runs from those final results or import H25's local IH.
A cluster/all-group certificate lift needs its own operational construction.
Keep the fixed source/model/ranks and admitted-parent requirements.
Keep H15's arbitrary initial domains, SAME global Trace and genuine initial Room.
Generated-root admission, source/model/rank agreement, new Room/WordRanges,
literal Mu/full pass, practical width, solver and Haskell correspondence,
and convergence remain open. No whole-implementation claim is supported.

The user authorizes pushes to origin/formalize. The local publisher has no
network command. Root push follows seal and local checkpoint verification.
Keep all older proofs, counterexamples, drafts, repairs and optimized code.
Do not post to the board, send messages, update memory or create an ADR.
''')
print(json.dumps(dict(status='PASS', sources=10, cuts=count, cut_lines=lines, whole_goal_complete=False)))
