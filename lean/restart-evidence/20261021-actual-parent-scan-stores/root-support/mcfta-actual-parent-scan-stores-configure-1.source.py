import json
import sys
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
here = root / 'lean/restart-evidence/20261021-actual-parent-scan-stores'
source_sha, jobs, dependencies, commands, failures = sys.argv[1:]
module = 'SourceCurrentActualParentScanNativeStores'

path = here / 'prepare-checkpoint.py'
text = path.read_text()
text = text.replace("{'pair', 'independent-review', 'scan-plan'}", "{'parent-scan', 'independent-review', 'admission-plan', 'owner-geometry-plan'}")
text = text.replace("('pair', 'positive-owner', 'SourceCurrentPositiveOwnerPair',", "('parent-scan', 'parent-scan-stores', '" + module + "',")
text = text.replace('0bcad2715a1170cac3c7bf99423b716916c068a3a859e092d70258c368b40f39', source_sha)
text = text.replace('mcfta-required-positive-chronology', 'mcfta-scan-native-stores')
path.write_text(text)

path = here / 'verify-checkpoint.py'
text = path.read_text().replace("[('pair','SourceCurrentPositiveOwnerPair')]", "[('parent-scan','" + module + "')]")
text = text.replace('3586', jobs).replace('74877', dependencies)
text = text.replace("== 5 and account['nonzero_lean_jobs'] == 1", "== " + commands + " and account['nonzero_lean_jobs'] == " + failures)
text = text.replace('proof-commit-pair.txt', 'proof-commit-parent-scan.txt')
path.write_text(text)

path = here / 'verify-preservation.py'
text = path.read_text().replace('SourceCurrentPositiveOwnerPair', module)
text = text.replace('20261021-required-positive-chronology/frozen-modules.json', '20261021-scan-native-stores/frozen-modules.json')
path.write_text(text)

(here / 'attempt-expectations.json').write_text(json.dumps({
    'audit_jobs': int(jobs), 'audit_dependencies': int(dependencies),
    'actual_lean_lake_jobs': int(commands), 'nonzero_lean_jobs': int(failures)
}, indent=2) + '\n')

print(json.dumps({'status': 'PASS', 'source_sha256': source_sha, 'audit_jobs': int(jobs),
    'audit_dependencies': int(dependencies), 'actual_lean_lake_jobs': int(commands),
    'nonzero_lean_jobs': int(failures)}))
