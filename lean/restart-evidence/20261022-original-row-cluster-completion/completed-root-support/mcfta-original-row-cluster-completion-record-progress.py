import datetime
import difflib
import json
from pathlib import Path

here = Path('/home/tritlo/Code/mcfta/lean/restart-evidence/20261022-original-row-cluster-completion')
before = Path('/tmp/mcfta-original-row-cluster-completion-install-1.source.py').read_text()
after = Path('/tmp/mcfta-original-row-cluster-completion-install.py').read_text()
(here / 'install-baseline-archive-repair.patch').write_text(''.join(difflib.unified_diff(
    before.splitlines(True), after.splitlines(True), fromfile='install-1.source.py', tofile='install-2.source.py')))
receipt = json.loads(Path('/tmp/mcfta-original-row-cluster-completion-install-1.json').read_text())
assert receipt['exit_code'] == 1
note = '\nThe first root installation metadata job failed before any repository write.\n'
note += 'It tried to read an Audit archive that had not been created. The second job first\n'
note += 'reads the exact baseline Audit from Git, verifies its live bytes, hash and3122 lines,\n'
note += 'then creates the archive and index before installation. The exact helper patch\n'
note += 'and complete failed receipt/raw/source remain. There is one failed root metadata job.\n'
note += 'The public-TYPE reviewer also retained two local metadata diagnostics and their fixes.\n'
note += 'Those did not execute prepared tools and did not create root or proof failures.\n'
path = here / 'metadata-repairs.md'
assert 'first root installation metadata' not in path.read_text()
path.write_text(path.read_text() + note)
prior = here / 'strict1-current-progress.md'
assert not prior.exists()
prior.write_bytes((here / 'current-progress.md').read_bytes())
timestamp = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
(here / 'current-progress.md').write_text(f'''# Genuine original-row cluster completion

Updated: {timestamp}.

The prior goal turn made progress: strict1/strict2 diagnostics led to exact retained repairs.
The current turn produced a clean strict3, accepted sole FULL and successful aggregate Audit.
The selected source has345 lines, SHA c6e8e0f7. Public and helper statements remain unchanged.
The checked TYPE has618 logical lines,617 LF, no final LF and57667 bytes, SHA89d3dbda.
Root and an independent reviewer read the complete checked TYPE. Printed bytes match.
Actual axioms are Classical.choice, Quot.sound and propext. The body is checked programmatically.
All five actual Lean/Lake jobs remain: two failed strict, clean strict3, FULL1 and Audit1.
Audit passes3634 jobs and75451 theorem dependencies. No source exit-zero warning or TYPE rejection.
The official module and one Audit import are installed. The original Audit archive is exact.
One root metadata installation failure and its archive-step repair remain documented.
The actual nine bound metadata tools need complete independent review before execution.
Proof commit, documentary checkpoint and final seal/publication remain pending at this cut.
Physical language preservation, grouping, generated parents, Mu and public pass remain open.
H6 remains the strongest combined semantic theorem. No Haskell source change is added.
Upstream refresh reports Already up to date. H16 remains sealed; all old work is retained.
Remote publication still needs the pending fresh direct user approval. The whole goal stays active.
''')
print(json.dumps(dict(status='PASS', proof_jobs=5, failed_proof_jobs=2, failed_root_metadata_jobs=1)))
