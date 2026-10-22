import datetime
import hashlib
import json
import re
from pathlib import Path

here = Path('/home/tritlo/Code/mcfta/lean/restart-evidence/20261022-original-row-cluster-completion')
receipt = json.loads((here / 'original-row-cluster-completion-strict-1.json').read_text())
raw = (here / receipt['log']).read_bytes()
assert receipt['exit_code'] == 1 and hashlib.sha256(raw).hexdigest() == '6def86a8b3726593c81c9ed715d7853a288bb4bd8356e8af8059b70a01c4bc67'
assert len(re.findall(rb'^.+?:\d+:\d+: error(?:\([^)]*\))?:', raw, re.M)) == 13
assert not re.search(rb'^.+?:\d+:\d+: warning(?:\([^)]*\))?:', raw, re.M)
progress = here / 'current-progress.md'
archive = here / 'body-proposal-current-progress.md'
assert not archive.exists()
archive.write_bytes(progress.read_bytes())
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
progress.write_text('# Genuine original-row cluster completion\n\nUpdated: ' + now + '.\n\n'
    'The upstream pull and88001-file baseline passed. H16 remains sealed.\n'
    'The first complete344-line draft passed whole source review but failed strict1.\n'
    'The actual check ended at' + receipt['observed_at'] + '.\n'
    'Its complete6884-byte log has13 error heads and no warning heads.\n'
    'The primary defects are the missing nodeEdges namespace and reserved local prefix names.\n'
    'The failed source, full raw log, receipt, effective caps and usage remain.\n'
    'source-repair-v2 retains a344-line candidate467e909e and the exact inverse.\n'
    'Its context17 has new hashb33ff6c3. All three header texts remain unchanged.\n'
    'The only changes are the namespace open and six local identifier occurrences.\n'
    'Root read all344 repaired lines. Independent repair review and strict2 remain pending.\n'
    'The FULL materializer repair selects the new context explicitly. No FULL ran.\n'
    'The source hard stop remains350 lines. Default proof limits and linters remain.\n'
    'No official module or Audit import has been installed. No Haskell change is added.\n'
    'Physical language preservation, grouping, generated parents, Mu and the public pass remain open.\n'
    'H6 remains the strongest combined semantic theorem. The whole goal stays active.\n'
    'Remote publication still needs the pending fresh direct user approval.\n')
repairs = here / 'metadata-repairs.md'
assert not repairs.exists()
repairs.write_text('# Metadata and coordination corrections\n\n'
    'The root tool-review length vector initially placed archive-support and seal-checkpoint in reverse order.\n'
    'The root corrected the16/26 order before execution. The total remained530.\n'
    'The exact inverse is retained in the root support preparation patch. No failed metadata job is claimed.\n\n'
    'The root sent V2 review messages to a completed task. Those messages did not start a turn.\n'
    'A live-agent query confirmed the completed status. followup_task then started the actual review.\n'
    'No V2 review result or compiler job was invented. No owned worker was restarted.\n')
print(json.dumps({'status': 'PASS', 'actual_proof_jobs': 1, 'strict1_failed': True}))
