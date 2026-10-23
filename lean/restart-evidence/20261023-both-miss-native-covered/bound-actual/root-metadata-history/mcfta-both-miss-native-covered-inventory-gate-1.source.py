import datetime
import runpy
import sys
globals().update(runpy.run_path('/tmp/mcfta-both-miss-native-covered-root-common.py'))

source = Path('/tmp/mcfta-both-miss-native-covered-inventory')
audit = Path('/tmp/mcfta-both-miss-native-covered-inventory-audit')
pins = checked_package(source,
    '2a02406ddee5faced488a94f6aee5175e4ea580185f075e2755a4493e58fb22c',
    '2fdd6f0d690e994fe0adf806995745ea1a4302595a4f7d5e627a276873a2dd37')
assert len(pins) == 66
assert sha(source / 'source-index.json') == '17b4b25c4e14032bebb2abcb9f0a03d05cedcd6e82bf1952fd94cb5869ac5a6d'
assert sha(source / 'plain-contract.txt') == '5252df3c1c01b7d73f850322f75de9729d76026bf02231169f7468b5318562f0'
index = load(source / 'source-index.json')
assert len(index['sources']) == 21
cuts = lines = 0
for item in index['sources']:
    live = ROOT / item['path']
    data = live.read_bytes()
    assert data == (source / item['snapshot']).read_bytes()
    assert sha(live) == item['sha256'] and len(data) == item['bytes']
    assert len(data.splitlines()) == item['lines']
    for cut in item['cuts']:
        snapshot = source / cut['snapshot']
        assert snapshot.read_bytes() == b''.join(data.splitlines(True)[cut['start']-1:cut['end']])
        assert sha(snapshot) == cut['sha256'] and snapshot.stat().st_size == cut['bytes']
        cuts += 1
        lines += cut['end'] - cut['start'] + 1
assert (cuts, lines) == (25, 465)
for reference in index['baseline_reference'].values():
    path = Path(reference['path'])
    assert path.stat().st_size == reference['bytes'] and sha(path) == reference['sha256']
assert git('rev-parse', 'HEAD').strip() == START
assert (ROOT / 'lean/MicroCFTA/Audit.lean').read_bytes() == (HERE / 'original-sources/Audit.original.lean.txt').read_bytes()
checked_package(audit, sys.argv[1], sys.argv[2])
independent = load(audit / 'review.json')
assert independent['status'] == 'CLEAR' and sha(audit / 'review.json') == sys.argv[3]
archive(source, 'native-covered-inventory')
archive(audit, 'native-covered-inventory-audit')
report = dict(status='ROOT_SOURCE_ONLY_ROUTE_CLEAR', observed_at=datetime.datetime.now().astimezone().isoformat(),
    root_whole_public_cuts_read=True, sources=21, cuts=cuts, cut_lines=lines,
    all_H13_outputs_retained=True, same_finite_model_and_ranked=True,
    genuine_parent_admission_and_initial_Covered=True, same_receipt_trace_required=True,
    public_APIs_only=True, new_induction=False, native_Covered_only=True,
    source_target=[140, 170], source_hard_stop=180,
    independent_review_sha256=sha(audit / 'review.json'),
    exact_header_proposal_authorized=True, body_proposal_authorized=False,
    compiler_authorized=False, prepared_tool_execution_authorized=False, whole_goal_complete=False)
save('root-inventory-review.json', report)
with (HERE / 'current-progress.md').open('a') as output:
    output.write('\n## Public API route gate\n\nRoot and independent reviews accept all21 source identities and25 public cuts.\nH18 child admission and public row residency derive the literal source certificate.\nThe same H13 native Receipt.trace can derive final native Covered.\nThe exact signature proposal is authorized with a180-line source hard stop.\nNo proof body, compiler or prepared tool is authorized by this route gate.\n')
print(json.dumps(report))
