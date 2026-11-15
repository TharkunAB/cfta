from pathlib import Path
import datetime
import hashlib
import json
import subprocess

work = Path(__file__).parent
base = '0e8d6e24714bca42cd96c93fa4cb33020e065006'
packet = '20261115-actual-source-task-scan-checkpoint'
old_packet = '20261115-native-cm-producer-and-auxiliary-assembly-checkpoint'
old_work = Path('lean/restart-evidence/' + old_packet + '-work')
public = Path('lean/restart-evidence/20261115-actual-source-task-scan-publication')
result = json.loads((public / 'checked.json').read_text())
assert len(result['checks']) == 5 and all(item['exit'] == 0 and not item['nonstandard_axioms'] for item in result['checks'])
code = subprocess.check_output(['git','rev-parse','HEAD']).decode().strip()
assert code == 'bb2151075d8e039f49516d87dd19e976d4326c71'
config = dict(result, checked_code=code, prior_checkpoint=base, public_run=str(public.resolve()),
    public_gates=5, explicit_reports=408, source_files=6119, direct_audit_imports=5119,
    board_prefix='current-board-public-', original_prepared_scan_header='bab8fc35f029b67ca6a65a366d48379b6a4e84f5136fdd15a8a353295534551e',
    new_private_resource_probes=6, old_owner_bytes_preserved_as_exact_prefix=True,
    other_source_files_byte_exact=6118, native_CM_memo_history_all_actual_prefixes_proved=True,
    native_query_scope='One literal initial node query, both complete memo families initially empty; qualified C/M results.',
    full_scope='One finite accepted completion of same original emitted partial root under one compatible assignment, with actual domains, paths, UF aliases, residuals, readback, parked recompletion and removed historical obligations on that output branch; all original fuels, budgets and emissions before later stops.')
(work/'checkpoint-config.json').write_text(json.dumps(config,indent=2)+'\n')
roots=[]
prefixes=('20261115-current-actual-source-','20261115-current-actual-prepared-scan-','20261115-current-any-budget-identity-','20261115-native-actual-source-')
excluded={'20261115-native-actual-source-opaque-and-control-anybudget-check'}
for path in sorted(Path('lean/restart-evidence').iterdir()):
    if path.is_dir() and path.name.startswith(prefixes) and path.name not in excluded:
        roots.append(str(path))
roots += [str(work),str(public),'lean/restart-evidence/20261115-after-identity-real-worker-frontier-note']
assert len(roots)==len(set(roots)) and all(Path(p).is_dir() for p in roots)
(work/'archive-roots.json').write_text(json.dumps(roots,indent=2)+'\n')
(work/'skipped-published-roots.json').write_text(json.dumps({'live_checker_excluded':sorted(excluded),'live_checker_session':93536,'frozen_opaque255_and_control408_raw_inputs_included':True},indent=2)+'\n')
(work/'selection-review.json').write_text(json.dumps({'selected_roots':len(roots),'all_promoted_components_and_repair_parents_included':True,'prior_immutable_checkpoints_preserved':True,'live_derived_outputs_excluded':True,'compiled_objects_excluded':True},indent=2)+'\n')
for name in ['assemble.py','finalize.py']:
    text=(old_work/name).read_text().replace(old_packet,packet).replace("BASE = '299db36637ea5997b592488aad1c8e16134764c0'", "BASE = '"+base+"'").replace('# Mixed native producer cases checkpoint','# Actual source task and prepared-scan resource checkpoint')
    if name=='assemble.py':
        start=text.index('EXTRA = ');end=text.index('\nSKIP_DIRS',start);text=text[:start]+'EXTRA = []'+text[end:]
    (work/name).write_text(text)
text=Path('lean/restart-evidence/20261115-native-general-cm-history-checkpoint/verify.py').read_text().replace('20261115-native-general-cm-history-checkpoint',packet)
(work/'verify.py').write_text(text)
text='''# Actual source task and prepared-scan resource checkpoint

Checked at {{TIME}}. Checked code: `{{CODE}}`.
Prior checkpoint: `0e8d6e24714bca42cd96c93fa4cb33020e065006`.
Source digest: `{{TREE}}`. Main remains
`e53852064d3ef5a2eafec47d754c27504b11de5f`; fresh fetch22999 passed.
No Haskell, Cabal, LiquidHaskell or tests changed. No Haskell fix is claimed.

Six committed proofs establish actual tuple-nil resources, row scans, fallback
dispatch, strong induction over every actual source task, captured-row current
initialization, and the ORIGINAL prepared-scan target at EVERY supplied budget.
The prepared header remains byte-exact, SHA256
`bab8fc35f029b67ca6a65a366d48379b6a4e84f5136fdd15a8a353295534551e`.
It retains original root, workFuel, prepared seed, forecast, exact row prefixes,
staged child order, restored captured cache and outputs before a later stop.
The task proof uses genuine smaller-task IHs. Recursive callbacks still require
the genuine smaller-depth identity-worker IH; this checkpoint does not close
that whole-worker depth induction.

All five publication gates passed in2586. Strict owner checks retain all66 old
resource probes plus six new reports:72 standard. Independent normal imports
check three existing results, including the original16-conjunct observed API.
Audit checks97,752 dependencies and408 reports:405 standard and three without
axioms. Only propext, Classical.choice and Quot.sound occur. The tree retains
6,119 sources and5,119 direct Audit imports. The owner adds1,279 lines and keeps
ALL old bytes as an exact prefix. All other6,118 Lean sources stay byte-exact.

Original failed candidates and statement-exact repairs are retained. Repairs
fix only proof names, constructor syntax, typed aliases and local reduction.
Local opacity of recursive reservations and actual controls removes expensive
whole-worker normalization. Actual sources use the original runtime budgets.
One redundant opacity attribute was removed because its target was already
opaque. No linter was disabled. All heavy checks were serial with8GiB caps and
zero swap. Compiled private objects are disposable; source and logs reproduce
the results. This turn removed159,593,144 terminal object bytes before this
checkpoint. Keep public .lake, live jobs and five protected unknown tmp entries.

The native C/M history theorem from the prior checkpoint remains proved for
one literal initial native node query with both complete memo families empty.
It preserves qualified structural Profile at every actual prefix of that same
history with original P, heights, fuel and plans. Profile permits Empty.

Next exact target: finish original identity-worker arbitrary-budget declaration
c831 in the full-source-coupled-integration-audit packet. Source now contains
all six checked task/scan fragments. Append ONLY the repaired opaque helper and
consumer, not another copy of those six. Frozen opaque255 f929b276 and control408
8d254829 are checking in93536; no whole-worker proof credit yet. The consumer
also needs the ordinary public SelectedPreparationObservedResources import.
All66 original probes and all16 observed API clauses remain protected.

Next REAL worker obligations: prove continuing SelectedStep.runPrefix resources
at the SAME supplied workFuel with actual OuterNarrow, then genuine real smaller-
depth callbacks. Existing sufficient-bound runs do not prove this. Separately,
derive actual worker query occurrence qualification, original InputsThrough and
FieldsThrough from numeric reservations, and inherited native memo laws across
requests. advancePhysical retains both native tables and the domain cache.
Do not restart later queries with fresh tables or add a future resource/model
supplier. The archived after-identity frontier note gives exact composition APIs.

The FULL goal remains ONE finite accepted completion of the SAME original
emitted partial root under ONE compatible assignment satisfying actual native
domains, retained paths, UF aliases, residuals, readback, parked recompletion and
EVERY removed historical obligation on THAT output branch. Preserve original
source/root/noStop, fuels, budgets, ALL outcomes and emissions before later stops.
Typing/depth adequacy and completeness, BOTH preprocessing/LPO language directions,
stream order/multiplicity/lazy demand, exact node-count/count/weight/training,
BOTH rank inverses, host bounds and compiled Haskell correspondence remain open.
Task resources and structural closure do not establish the joint finite witness.

Goal ACTIVE. origin/formalize pushes remain explicitly authorized; the wrong-chat
fork push remains canceled. Root owns Source/compiler/Git/board/tmp. Primary usage
was29percent at22:07 CET. Pause and ping Matti if it exceeds80percent.
All earlier document bytes follow unchanged as historical records.

'''
(work/'checkpoint-note.md').write_text(text)
d=json.loads((work/'WIP.json').read_text());d.update(at=datetime.datetime.now().astimezone().isoformat(),source_mutated=True,all_source_still_base=False,source_code=code,public_gates_passed=True,public_check_session=2586,active_checker={'session':93536,'run':'20261115-native-actual-source-opaque-and-control-anybudget-check'},original_prepared_scan_proved=True,original_prepared_scan_all66_checked=True,whole_identity_worker_at_any_budget_proved=False,goal_active=True,previous_goal_turn='progress: actual task induction verified and original prepared-scan diagnostics obtained; current turn adds six verified source proofs');(work/'WIP.json').write_text(json.dumps(d,indent=2)+'\n')
print(json.dumps({'selected_roots':len(roots),'checked_code':code,'public_gates':5}))
