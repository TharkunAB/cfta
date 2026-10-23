exec(compile(open('/tmp/mcfta-pair-node-counter-growth-root-common.py').read(), '/tmp/mcfta-pair-node-counter-growth-root-common.py', 'exec'))
import datetime
import re

stem = 'root-pair-node-counter-growth-audit-1'
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
progress = HERE / 'current-progress.md'
stamp = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
with progress.open('a') as out:
    out.write('\n## Actual proof and Audit checkpoint\n\nUpdated: ' + stamp + '.\n\n')
    out.write('The unchanged 96-line pair source passed its first all-linter strict check with an empty log.\n')
    out.write('The sole FULL check passed. Root and an independent reviewer read all three complete checked public TYPEs.\n')
    out.write('All twelve raw slices reconstruct the complete 1048134-byte output. BODY retention was checked programmatically.\n')
    out.write('Actual raw TYPE identity is false for outcomeState and true for both theorems. All three lexical identities are true.\n')
    out.write('The accessor has no axioms. Both theorems use only the three allowed standard axioms.\n')
    out.write('The aggregate Audit passed with ' + build.group(1) + ' build jobs and ' + dependencies.group(1) + ' dependency checks.\n')
    out.write('It replayed one older unused-input warning. The new source has no warning.\n')
    out.write('The official source and sole Audit import are installed. No H37 proof or evidence commit exists yet.\n')
    out.write('Saved-verifier source/data, complete actual history, both saved modes, document refresh, seal and push remain pending.\n')
    out.write('The pending verifier author is Arity. Guard will review it. Required completed public TYPE and pending closing-tool reviews.\n')
    out.write('The source proves only the input-to-actual-outcome node-counter lower bound through pair comparison.\n')
    out.write('Scan/H23 composition, fixed-source initial counter order, domain history, upper bounds, Room/WordRanges, full resources, Mu/full pass, Haskell/solver correspondence and convergence remain open.\n')
    out.write('H6 constructed_node_calls remains the strongest combined result. The complete goal is ACTIVE and incomplete.\n')
    out.write('No Haskell source changed. Keep the external Haskell repair index FIRST in FINDINGS.\n')
print('Recorded actual Audit counts and the exact unfinished publication state.')
