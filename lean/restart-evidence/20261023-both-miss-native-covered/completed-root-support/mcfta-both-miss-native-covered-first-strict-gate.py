import datetime
import re
import runpy
import sys
globals().update(runpy.run_path('/tmp/mcfta-both-miss-native-covered-root-common.py'))

source = Path('/tmp/mcfta-both-miss-native-covered-source')
audit = Path('/tmp/mcfta-both-miss-native-covered-body-audit')
checked_package(source, sys.argv[1], sys.argv[2])
checked_package(audit, sys.argv[3], sys.argv[4])
assert sha(audit / 'review.md') == sys.argv[5]
assert load(HERE / 'root-full-tools-review.json')['independent_source_review'] == 'CLEAR'
declaration = load(HERE / 'root-declaration-review.json')
assert declaration['status'] == 'ROOT_DECLARATION_REVIEW_CLEAR'
assert declaration['local_induction'] is None
path = source / (NAME + '.lean')
data = path.read_bytes()
assert sha(path) == sys.argv[6] and len(data.splitlines()) == int(sys.argv[7]) <= 180
contracts = load(HERE / 'signature-plan/contracts.json')
assert len(contracts) == 10
assert data.startswith((HERE / 'signature-plan/context.lean.txt').read_bytes())
header = (HERE / 'signature-plan/public-header.lean.txt').read_bytes().rstrip(b'\n') + b' := by\n'
assert data.count(header) == 1
public_body = data[data.index(header) + len(header):data.rindex(('end MicroCFTA.' + NAME).encode())]
bindings = (HERE / 'signature-plan/local-bindings.lean.txt').read_bytes()
assert public_body.count(bindings) == 1
positions = [public_body.index(bindings)]
fragments = ['local-raw-scope.lean.txt', 'local-raw-covered.lean.txt', 'local-ordered-inputs.lean.txt',
    'local-ready.lean.txt', 'local-fields.lean.txt', 'local-certificate.lean.txt', 'local-final-covered.lean.txt']
for filename in fragments:
    fragment = (HERE / 'signature-plan' / filename).read_bytes().rstrip(b'\n') + b' := by\n'
    assert public_body.count(fragment) == 1
    positions.append(public_body.index(fragment))
assert positions == sorted(positions)
assert re.findall(rb'(?m)^ *have[ \t]+([^ \t:\n]+)', public_body) == [name.encode() for name in declaration['local_names']]
assert re.findall(rb'(?m)^ *let[ \t]+([^ \t:\n]+)', public_body) == [b'ordered', b'request']
assert re.findall(rb'(?m)^theorem (\w+)', data) == [b'both_miss_complete']
assert not re.search(rb'\b(induction|show)\b', public_body)
assert not re.search(rb'(?m)^\s*set_option|\bsorry\b|\baxiom\b|\bprivate\b', data)
call = b'SourceCurrentSameSymbolEdgeOriginalRows.both_miss_complete'
assert public_body.count(call) == 1 and public_body.count(b'receipt.trace') == 1
assert positions[-2] < public_body.index(call) < positions[-1]
assert data.rstrip().endswith(('end MicroCFTA.' + NAME).encode())
assert git('rev-parse', 'HEAD').strip() == START
assert not (ROOT / 'lean/MicroCFTA' / (NAME + '.lean')).exists()
archive(source, 'source')
archive(audit, 'body-audit')
report = dict(status='ROOT_ACCEPTED_FOR_FIRST_STRICT', observed_at=datetime.datetime.now().astimezone().isoformat(),
    source='source/' + NAME + '.lean', source_sha256=sha(path), source_lines=int(sys.argv[7]), hard_stop=180,
    root_read_complete_source=True, independent_complete_source_review='CLEAR',
    independent_review_sha256=sha(audit / 'review.md'), exact_context_and_ten_contracts=True,
    only_reviewed_local_types=True, no_induction_or_typed_show=True, no_private_helpers=True,
    same_H13_call_and_native_receipt_trace=True, only_native_covered_appended=True,
    first_strict_authorized=True, official_install_authorized=False,
    new_proof_jobs=0, whole_goal_complete=False)
save('root-source-compile-gate.json', report)
with (HERE / 'current-progress.md').open('a') as output:
    output.write('\n## Complete source accepted\n\nRoot and independent reviews accept the complete body and all10 exact fragments.\nThe first strict command is authorized at default limits with all linters.\nThe source invokes H13 once and uses that SAME native Receipt.trace for Covered.\nMetadata attempts remain separate from proof commands. No proof command ran before this gate.\nOfficial installation and actual evidence binding remain pending. The whole goal stays ACTIVE.\n')
print(json.dumps(report))
