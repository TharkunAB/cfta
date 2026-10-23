import datetime
import re
import runpy
import sys
globals().update(runpy.run_path('/tmp/mcfta-completed-hit-readback-root-common.py'))

source = Path('/tmp/mcfta-completed-hit-readback-source')
audit = Path('/tmp/mcfta-completed-hit-readback-body-audit')
checked_package(source, sys.argv[1], sys.argv[2])
checked_package(audit, sys.argv[3], sys.argv[4])
assert sha(audit / 'review.md') == sys.argv[5]
assert load(audit / 'review.json')['status'] == 'SOURCE_ONLY_COMPLETE_BODY_CLEAR'
assert load(HERE / 'root-full-tools-review.json')['independent_source_review'] == 'CLEAR'
declaration = load(HERE / 'root-declaration-review.json')
assert declaration['status'] == 'ROOT_DECLARATION_REVIEW_CLEAR'
assert declaration['local_induction']['helper'] == 'ret_checked'
assert declaration['private_names'] == ['yielded_done', 'ret_checked']
path = source / (NAME + '.lean')
data = path.read_bytes()
assert sha(path) == sys.argv[6] and len(data.splitlines()) == int(sys.argv[7]) <= 180
contracts = load(HERE / 'signature-plan/contracts.json')
fragments = load(HERE / 'signature-plan/insertion-map.json')['compiled_fragments']
assert len(contracts) == len(fragments) == 10
positions = []
for item in fragments:
    fragment = HERE / 'signature-plan' / item['file']
    assert contracts[item['file']] == item['sha256'] == sha(fragment)
    raw = fragment.read_bytes()
    assert len(raw.splitlines()) == item['lines']
    attached = raw.rstrip(b'\n') + b' := by\n' if 'future_body_attachment' in item else raw
    assert data.count(attached) == 1, item['file']
    positions.append(data.index(attached))
assert positions == sorted(positions) and positions[0] == 0
header = (HERE / 'signature-plan/public-header.lean.txt').read_bytes().rstrip(b'\n') + b' := by\n'
public_body = data[data.index(header) + len(header):data.rindex(('end MicroCFTA.' + NAME).encode())]
assert re.findall(rb'(?m)^ *have[ \t]+([^ \t:\n]+)', data) == [name.encode() for name in declaration['local_names']]
assert re.findall(rb'(?m)^ *let[ \t]+([^ \t:\n]+)', data) == [name.encode() for name in declaration['local_let_names']]
assert re.findall(rb'(?m)^private theorem (\w+)', data) == [b'yielded_done', b'ret_checked']
assert re.findall(rb'(?m)^theorem (\w+)', data) == [b'completed_hit_checked']
assert re.findall(rb'(?m)^ *induction[^\n]*', data) == [b'  induction pending generalizing fuel before with']
assert not re.search(rb'\b(induction|show)\b', public_body)
assert not re.search(rb'(?m)^\s*set_option|\bsorry\b|\baxiom\b', data)
assert not re.search(rb'(?m)^ *obtain[^\n]* : ', data)
assert public_body.count(b'yielded_done ') == 7
assert public_body.count(b'ret_checked ') == 2
assert b'FlatMemoThunk.lookup_returned' in public_body and b'FlatMemoThunk.demand_returned' in public_body
assert data.rstrip().endswith(('end MicroCFTA.' + NAME).encode())
assert git('rev-parse', 'HEAD').strip() == START
assert not (ROOT / 'lean/MicroCFTA' / (NAME + '.lean')).exists()
archive(source, 'source')
archive(audit, 'body-audit')
report = dict(status='ROOT_ACCEPTED_FOR_FIRST_STRICT', observed_at=datetime.datetime.now().astimezone().isoformat(),
    source='source/' + NAME + '.lean', source_sha256=sha(path), source_lines=int(sys.argv[7]), hard_stop=180,
    root_read_complete_source=True, independent_complete_source_review='CLEAR',
    independent_review_sha256=sha(audit / 'review.md'), exact_context_and_ten_contracts=True,
    only_reviewed_local_types=True, exact_two_private_helpers=True,
    exact_ret_checked_induction=True, generated_IH_fixed_value_result_after=True,
    same_arbitrary_supplied_done_result_and_full_after=True,
    arbitrary_captured_payload_and_public_returned_cell_retention=True,
    only_checked_state_equality=True, no_second_execution=True,
    first_strict_authorized=True, official_install_authorized=False,
    new_proof_jobs=0, whole_goal_complete=False)
save('root-source-compile-gate.json', report)
with (HERE / 'current-progress.md').open('a') as output:
    output.write('\n## Complete source accepted\n\nRoot and independent reviews accept the complete body and all10 exact fragments.\nThe first strict command is authorized at default limits with all linters.\nThe source follows the same observed done equation through direct and reversed hits.\nThe captured pair stays arbitrary. Only the checked native state is equal.\nMetadata attempts remain separate from proof commands. No proof command ran before this gate.\nOfficial installation and actual evidence binding remain pending. The whole goal stays ACTIVE.\n')
print(json.dumps(report))
