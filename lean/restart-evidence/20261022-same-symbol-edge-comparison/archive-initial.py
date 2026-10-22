import hashlib
import json
import runpy
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
PREVIOUS = HERE.parent / '20261022-same-symbol-edge-original-rows'
components = [
    ('/tmp/mcfta-same-symbol-edge-comparison-previous-local-checkpoint', 'previous-local-checkpoint'),
    (str(PREVIOUS / 'next-comparison-inventory'), 'comparison-plan'),
    (str(PREVIOUS / 'next-comparison-plan-audit'), 'comparison-plan-audit'),
    ('/tmp/mcfta-same-symbol-edge-comparison-source', 'source-proposal'),
    ('/tmp/mcfta-same-symbol-edge-comparison-checkpoint-preparation', 'checkpoint-preparation'),
]
for source, name in components:
    sys.argv = [str(HERE / 'archive-extra.py'), source, name]
    runpy.run_path(str(HERE / 'archive-extra.py'), run_name='__main__')
erratum = PREVIOUS / 'next-comparison-authorship-erratum.md'
(HERE / erratum.name).write_bytes(erratum.read_bytes())
source = HERE / 'source-proposal/SourceCurrentSameSymbolEdgeComparison.lean'
assert len(source.read_bytes().splitlines()) == 112
assert hashlib.sha256(source.read_bytes()).hexdigest() == '02d01576ce9e7188342835138452a5163b150e28c264c01782137848e1a1c560'
context = (HERE / 'comparison-plan/context.lean.txt').read_bytes()
header = (HERE / 'comparison-plan/proposed-signature.lean.txt').read_bytes().rstrip(b'\n') + b' := by\n'
assert len(context.splitlines()) == 16 and len(header.splitlines()) == 48
assert source.read_bytes().startswith(context) and source.read_bytes().count(header) == 1
(HERE / 'root-source-authorization.json').write_text(json.dumps({
    'status': 'ROOT_SOURCE_REVIEWED', 'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
    'root_read_complete_source': True, 'exact_context_lines': 16, 'exact_header_lines': 48,
    'source_lines': 112, 'source_limit': 180, 'proof_jobs_at_cut': 0,
    'scope': 'Original-row comparison completion for all actual memo lookup branches',
    'current_packet_and_room_explicit': True, 'no_success_or_post_room_oracle': True,
    'no_native_receipt_on_cache_hits': True, 'no_full_pass_claim': True,
}, indent=2) + '\n')
