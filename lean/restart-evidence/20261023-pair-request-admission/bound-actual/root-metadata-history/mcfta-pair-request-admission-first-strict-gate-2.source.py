import datetime
import re
import runpy
import sys
globals().update(runpy.run_path('/tmp/mcfta-pair-request-admission-root-common.py'))

source = Path('/tmp/mcfta-pair-request-admission-source')
audit = Path('/tmp/mcfta-pair-request-admission-body-audit')
checked_package(source, sys.argv[1], sys.argv[2])
checked_package(audit, sys.argv[3], sys.argv[4])
assert sha(audit / 'review.md') == sys.argv[5]
assert load(HERE / 'root-full-tools-review.json')['independent_source_review'] == 'CLEAR'
path = source / (NAME + '.lean')
data = path.read_bytes()
assert sha(path) == sys.argv[6] and len(data.splitlines()) == int(sys.argv[7]) <= 180
contracts = load(HERE / 'signature-plan/contracts.json')
assert data.startswith((HERE / 'signature-plan/context.lean.txt').read_bytes())
header = (HERE / 'signature-plan/public-header.lean.txt').read_bytes().rstrip(b'\n') + b' := by\n'
assert data.count(header) == 1
public_body = data[data.index(header) + len(header):data.rindex(('end MicroCFTA.' + NAME).encode())]
positions = []
for local in ['property', 'swapped', 'initial', 'preserved', 'final']:
    fragment = (HERE / ('signature-plan/local-' + local + '.lean.txt')).read_bytes().rstrip(b'\n')
    fragment += b'\n' if local == 'property' else b' := by\n'
    assert data.count(fragment) == 1
    positions.append(data.index(fragment))
assert positions == sorted(positions)
assert re.findall(rb'(?m)^ *have[ \t]+([^ \t:\n]+)', public_body) == [b'swapped', b'initial', b'preserved', b'final']
assert re.findall(rb'(?m)^ *let[ \t]+([^ \t:\n]+)[ \t]*:', public_body) == [b'property']
assert re.findall(rb'(?m)^theorem (\w+)', data) == [b'completed_admitted']
assert len(re.findall(rb'\binduction\b', data)) == 1
assert not re.search(rb'(?m)^\s*set_option|\bsorry\b|\baxiom\b|\bprivate\b', data)
assert data.rstrip().endswith(('end MicroCFTA.' + NAME).encode())
assert git('rev-parse', 'HEAD').strip() == START
assert not (ROOT / 'lean/MicroCFTA' / (NAME + '.lean')).exists()
archive(source, 'source')
archive(audit, 'body-audit')
report = dict(status='ROOT_ACCEPTED_FOR_FIRST_STRICT', observed_at=datetime.datetime.now().astimezone().isoformat(),
    source='source/' + NAME + '.lean', source_sha256=sha(path), source_lines=int(sys.argv[7]), hard_stop=180,
    root_read_complete_source=True, independent_complete_source_review='CLEAR',
    independent_review_sha256=sha(audit / 'review.md'), exact_context_and_seven_contracts=True,
    only_reviewed_local_types_and_one_induction=True, no_private_helpers=True,
    first_strict_authorized=True, official_install_authorized=False,
    new_proof_jobs=0, whole_goal_complete=False)
save('root-source-compile-gate.json', report)
with (HERE / 'current-progress.md').open('a') as output:
    output.write('\n## Complete source accepted\n\nRoot and independent reviewers accept the complete body and exact seven fragments.\nThe first strict command is authorized. Default limits and all linters remain.\nThe first sandboxed metadata gate failed before its script ran because the user bus was unavailable.\nThe elevated retry passed. A preparation archive path error also stopped before mutation; its retry passed.\nThe first early-tool gate copied the reviewed files, then failed on the diagnostic-tail path.\nIts retry checked every retained partial file before it finished. No proof tool ran in those attempts.\nThe first strict gate counted public statement lets as proof locals and stopped before mutation.\nIts corrected retry restricts that check to the public body, as the reviewed verifier does.\nAll four failed metadata attempts remain separate from proof commands.\nOfficial installation and actual evidence binding remain pending. The whole goal stays ACTIVE.\n')
print(json.dumps(report))
