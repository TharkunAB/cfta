import runpy
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
PREVIOUS = HERE.parent / '20261022-same-symbol-edge-comparison'
components = [
    ('/tmp/mcfta-same-symbol-edge-comparison-domains-previous-local-checkpoint', 'previous-local-checkpoint'),
    (str(PREVIOUS / 'next-scan-inventory'), 'domain-history-plan'),
    (str(PREVIOUS / 'next-scan-plan-audit'), 'domain-history-plan-audit'),
]
for source, name in components:
    sys.argv = [str(HERE / 'archive-extra.py'), source, name]
    runpy.run_path(str(HERE / 'archive-extra.py'), run_name='__main__')
for name in ['next-scan-root-contract-review.json', 'next-scan-authorship-erratum.md']:
    assert not (HERE / name).exists()
    (HERE / name).write_bytes((PREVIOUS / name).read_bytes())
