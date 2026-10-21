import json
import shutil
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
results = []
packages = [
    ('/tmp/mcfta-outer-rank-adequacy-next-plan', 'future-adequacy-plan', 'verify.py'),
    ('/tmp/mcfta-outer-rank-adequacy-plan-review', 'future-adequacy-plan-review', 'review-verify.py'),
]
for source, name, verifier in packages:
    target = HERE / name
    assert not target.exists()
    shutil.copytree(source, target)
    for live in [False, True]:
        command = ['/usr/bin/python3', str(target / verifier), '--root', str(ROOT)]
        if live:
            command.append('--live')
        result = subprocess.run(command, cwd='/', check=True, text=True, capture_output=True)
        results.append({'package': name, **json.loads(result.stdout)})
review = {
    'root_whole_plan_header_context_index_report_verifier_read': True,
    'root_all_24_sources_and_32_ranges_read_and_hash_verified': True,
    'independent_whole_plan_and_all_sources_clear': True,
    'ordinary_and_mandatory_live_results': results,
    'implementation_authorized': False,
    'compiler_authorized': False,
    'approved_future_source_hard_stop': 650,
    'scope': 'Future node-only adequacy plan. No implementation or checked adequacy result.',
}
(HERE / 'future-adequacy-plan-root-review.json').write_text(json.dumps(review, indent=2) + '\n')
print(json.dumps(review))
