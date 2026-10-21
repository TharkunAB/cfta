import runpy
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
components = [
    ('mcfta-count-mass-bound-full-preparation', 'count-full-preparation'),
    ('mcfta-finite-round-forecast-full-preparation', 'finite-full-preparation'),
    ('mcfta-count-mass-bound-full-preparation-audit', 'count-full-preparation-review'),
    ('mcfta-finite-round-forecast-full-preparation-audit', 'finite-full-preparation-review'),
    ('mcfta-count-mass-bound-accepted-audit', 'count-accepted-review'),
    ('mcfta-finite-round-forecast-accepted-audit', 'finite-accepted-review'),
    ('mcfta-finite-round-reader-line-repair', 'finite-reader-line-repair'),
    ('mcfta-warm-rank-grid-preservation-preparation', 'preservation-preparation'),
    ('mcfta-warm-rank-grid-preservation-audit', 'preservation-initial-review'),
    ('mcfta-warm-rank-grid-preservation-repair-1', 'preservation-repair-1'),
    ('mcfta-warm-rank-grid-preservation-repair-1-audit', 'preservation-repair-1-review'),
    ('mcfta-warm-rank-grid-proof-verifier-preparation', 'proof-verifier-preparation'),
    ('mcfta-warm-rank-grid-proof-verifier-repair-1', 'proof-verifier-repair-1'),
    ('mcfta-warm-rank-grid-proof-verifier-repair-1-audit', 'proof-verifier-repair-1-review'),
    ('mcfta-warm-next-packet-plan', 'next-warm-plan'),
    ('mcfta-warm-next-packet-plan-audit', 'next-warm-plan-review'),
    ('mcfta-warm-rank-grid-checkpoint-preparation', 'checkpoint-preparation'),
    ('mcfta-warm-rank-grid-publication-preparation', 'publication-preparation'),
]
for source, name in components:
    assert (Path('/tmp') / source).is_dir() and not (HERE / name).exists()
for source, name in components:
    sys.argv = [str(HERE / 'archive-extra.py'), str(Path('/tmp') / source), name]
    runpy.run_path(str(HERE / 'archive-extra.py'), run_name='__main__')
