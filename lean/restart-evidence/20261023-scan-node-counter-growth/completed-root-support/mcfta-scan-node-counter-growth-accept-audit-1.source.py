exec(compile(open('/home/tritlo/Code/mcfta/lean/restart-evidence/20261023-scan-node-counter-growth/root-common.py').read(), 'root-common.py', 'exec'))
import datetime
import re

stem = 'root-scan-node-counter-growth-audit-1'
receipt = load(HERE / (stem + '.json'))
assert receipt['exit_code'] == 0 and receipt['observed_at']
assert receipt['command'][-2:] == ['build','MicroCFTA.Audit']
raw = (HERE / receipt['log']).read_bytes()
log = raw.decode()
build = re.search(r'Build completed successfully \((\d+) jobs\)',log)
dependencies = re.search(r'Checked axiom dependencies of (\d+) MicroCFTA theorems',log)
assert build and dependencies
assert not re.search(r'(?m)^error:',log)
warnings = re.findall(r'(?m)^warning: .+$',log)
assert len(warnings) == 1 and 'InternedFreshOrdinaryClosedCompletion.lean:24:5:' in warnings[0]
assert load(HERE / receipt['limits']) == {'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
source = ROOT / 'lean/MicroCFTA' / (NAME + '.lean')
assert sha(source) == load(HERE / 'selected-source-gate.json')['source_sha256']
original = (HERE / 'original-sources/Audit.original.lean.txt').read_bytes()
assert (ROOT / 'lean/MicroCFTA/Audit.lean').read_bytes() == ('import MicroCFTA.' + NAME + '\n').encode() + original
save('root-cohort-audit-gate.json',dict(status='ACCEPTED_ACTUAL_AGGREGATE_AUDIT',
    module=NAME, stem=stem, exit_code=0, observed_at=receipt['observed_at'],
    source_sha256=sha(source), receipt_sha256=sha(HERE / (stem + '.json')),
    log_sha256=sha(HERE / receipt['log']), log_bytes=len(raw), build_jobs=int(build.group(1)),
    dependencies=int(dependencies.group(1)), warnings=warnings, new_source_warnings=0,
    original_Audit_inverse_checked=True, goal_status='ACTIVE_INCOMPLETE'))
with (HERE / 'current-progress.md').open('a') as out:
    out.write('\n## Actual proof and Audit checkpoint\n\nUpdated: ' + datetime.datetime.now(datetime.timezone.utc).isoformat() + '.\n\n')
    out.write('The unchanged80-line Scan source passed its first strict check with an empty log and all linters.\n')
    out.write('The sole FULL check passed. Root and an independent reviewer read all three complete checked public TYPEs.\n')
    out.write('All twelve raw slices reconstruct the complete656026-byte output. BODY retention was checked programmatically.\n')
    out.write('Actual raw TYPE identity is false for outcomeState and execute_mono, and true for step_mono. All lexical identities are true.\n')
    out.write('The accessor has no axioms. Both theorems use only the three allowed standard axioms.\n')
    out.write('The aggregate Audit passed with ' + build.group(1) + ' build jobs and ' + dependencies.group(1) + ' dependency checks.\n')
    out.write('It replayed one older unused-input warning. The new source has no warning.\n')
    out.write('The official source, sole Audit import and unchanged variant are installed. No H38 proof or evidence commit exists yet.\n')
    out.write('Actual history, final saved-verifier data, both saved modes, document refresh, seal and push remain pending.\n')
    out.write('H23 counter composition, fixed-source initial counter order and original global history transport remain separate targets.\n')
    out.write('Upper bounds, full-pipeline Room/WordRanges/resources, generated execution, Mu/full pass, practical width, Haskell/solver correspondence and convergence remain open.\n')
    out.write('H6 constructed_node_calls remains strongest combined. The complete goal is ACTIVE and incomplete.\n')
    out.write('No Haskell source changed. Keep the external Haskell repair index FIRST in FINDINGS.\n')
print('PASS: actual Audit counts recorded; the complete formalization remains incomplete.')
