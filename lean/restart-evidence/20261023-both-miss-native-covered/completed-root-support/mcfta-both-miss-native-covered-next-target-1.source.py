import datetime
import runpy
import sys
globals().update(runpy.run_path('/tmp/mcfta-both-miss-native-covered-root-common.py'))

source = Path('/tmp/mcfta-both-miss-native-covered-next-inventory')
audit = Path('/tmp/mcfta-both-miss-native-covered-next-inventory-audit')
checked_package(source, '7c26f01b2f5d8d9d96dddc726c265d324ba977a9d993a83641ff9c8f745de451',
    'a3ec5609bdc1936b03cfb815c17a6a82c45b3bb94d7160038cf697d8500f8818')
checked_package(audit, sys.argv[1], sys.argv[2])
assert sha(audit / 'review.json') == sys.argv[3]
assert load(audit / 'review.json')['status'] == 'CLEAR'
index = load(source / 'source-index.json')
assert len(index['sources']) == 28
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
assert count == 38 and lines == 1058
assert load(HERE / 'root-audit-review.json')['status'] == 'PASS'
archive(source, 'next-comparison-inventory')
archive(audit, 'next-comparison-audit')
save('root-next-comparison-review.json', dict(status='SOURCE_ONLY_ROUTE_CLEAR',
    observed_at=datetime.datetime.now().astimezone().isoformat(), root_read_whole_note_and_plain_contract=True,
    root_read_all_selected_cuts=True, source_identities=28, source_cuts=38, cut_lines=lines,
    independent_review='CLEAR', next_component='Checked-state equality for the SAME supplied completed-hit H7 run',
    source_estimate=[110,160], proposed_hard_stop=180, estimate_is_not_authority=True,
    exact_declaration_gate_required=True, new_header_authorized=False,
    body_authorized=False, compiler_authorized=False, whole_goal_complete=False,
    historical_inventory_audit_pending_superseded_by='root-audit-review.json',
    actual_audit_build_jobs=3643, actual_audit_dependencies=75504))
target = HERE / 'NEXT-TARGET.md'
assert not target.exists()
proof = (HERE / 'proof-commit.txt').read_text().strip()
assert git('rev-parse', 'HEAD').strip() == proof
target.write_text('''# Current proof and next target

The whole formalization goal remains ACTIVE. This component makes PROGRESS.
H26 both_miss_complete augments the SAME H13 BOTH-miss result with native Covered.
Its source, finite model, ranks, holds and full returned state remain fixed.
Genuine parent admission and initial native Covered remain premises.
All H13 outputs remain. Its SAME native Receipt.trace supplies the coverage proof.
Strict1 has an empty log. The sole FULL1 and Audit1 pass with default limits.
The public TYPE has1294 logical lines and138240 bytes. Both reviewers read it all.
Checked and printed TYPE bytes match. BODY evidence remains programmatic only.
Actual axioms are Classical.choice, Quot.sound and propext.
Audit has3643 jobs and75504 dependencies. Only the old inputs warning remains.
There are three actual Lean/Lake jobs and no failed or warned source job.
The sole152-line ordinary source variant needs no repair. No Haskell source changed.
FINDINGS keeps its external Haskell repair index first.
H6 constructed_node_calls remains the strongest combined semantic theorem.

Next prove completed-hit checked-state equality for the SAME supplied H7 done.
Read next-comparison-inventory and next-comparison-audit. These are source-only.
Their historical Audit-pending cut is superseded by root-audit-review.json.
Use initial Stable, a published original or reverse key and the actual done equation.
Derive after.checked = before.checked for every actual completed fuel.
Keep the exact result and full after. A reverse hit may change the pair memo.
Derive the reverse-only descending order from Stable.canonical and original absence.
Public lookup/demand returned-cell retention avoids payload identification.
A small local yielded-prefix inversion and ret-control induction remain necessary.
The existing private H7 helpers are source guides and cannot be imported.
Do not choose a second completion or assume cross-fuel uniqueness or state equality.
The110–160-line estimate and proposed180-line stop require a fresh declaration gate.
No new Lean header, proof body or compiler is authorized by this inventory.

Then augment H15 once, keeping every output and its SAME actual full after.
Hit readback transports initial native Covered. BOTH misses use public miss_readback
on that SAME done to obtain raw native Steps. Genuine Resources/Current and public
prefix admission derive the physical Trace. Trace.covered then supplies coverage.
Retain arbitrary initialDomains, its Valid proof, the SAME global allocation Trace
and the genuine initial Room reservation. Never infer a hidden contextual receipt.
The later wrapper needs its own exact contract and total-source budget review.
Direct H10/H26 recomposition remains an alternative proposed190–230/hard250 route.
H25 can later add captured-pair Requests and canonical returned-cell admission
to that SAME result, with genuine old returned-cell admission retained as a premise.

H20/H22 hide internal pair runs. Do not project those runs or import a local IH.
Generated-root admission, source/model/rank agreement, new Room/WordRanges,
literal Mu/full pass, practical width, solver and Haskell correspondence,
and convergence remain open. No whole-implementation claim is supported.

The user authorizes pushes to origin/formalize. The local publisher has no
network command. Root push follows seal and local checkpoint verification.
Keep all older proofs, counterexamples, drafts, repairs and optimized code.
Do not post to the board, send messages, update memory or create an ADR.
''')
print(json.dumps(dict(status='PASS', sources=28, cuts=count, cut_lines=lines,
    proof=proof, whole_goal_complete=False)))
