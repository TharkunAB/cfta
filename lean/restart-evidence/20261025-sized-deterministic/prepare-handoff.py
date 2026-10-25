import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-sized-deterministic-20261025')
evidence = root / 'lean/restart-evidence/20261025-sized-deterministic'
block = '''## Deterministic Sized gate from main

Main `153e1a211b56dd78bd22f6b427fb78e673041d55` is integrated.
Gate proof: `cb59a931b06e54bf217fca7cd86f4d8a2cacb998`.
Dispatcher and rank integration: `01882288bb037712665f5d134b3005d2cc717da3`.
The goal stays ACTIVE.

The executable global key-cardinality check derives state and run uniqueness.
Public and raw finite-map dispatch now check it before the product gate.
Both routes return exactly the reference query record and residual errors.
This is extensional API equality. Physical set correctness, branch identity
and cost are outside this proof. Original guard and validation limits remain.

All five strict Lean checks, installed readback and Audit pass.
The audit checks 76607 theorem dependencies. Native Sized: 11 examples pass,
including four properties with 300 cases each. Formatting checks pass.
The Haskell documentation correction is recorded first in root FINDINGS.
H6 remains the strongest end-to-end result. Next: admitted ordered child
traversal, then the residual and captured-slot final write.
Details: `lean/notes-current-sized-deterministic.md`.

'''
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
             'lean/SYSTEM.md', 'lean/COVERAGE.md', 'lean/API-COVERAGE.md',
             'lean/notes-current-system-claim.md', 'lean/notes-proof-status-20261017.md']
for relative in documents:
    path = root / relative
    content = path.read_text()
    assert '## Deterministic Sized gate from main' not in content
    marker = '## Ordered native child traversal'
    assert marker in content
    path.write_text(content.replace(marker, block + marker, 1))

runs = ['sized-native-1', 'gate-strict-1', 'gate-strict-2', 'installed-gate',
        'dispatcher-strict-1', 'dispatcher-strict-2', 'installed-dispatcher',
        'preprocessing-strict-1', 'preprocessing-strict-2', 'installed-raw-dependencies',
        'raw-api-strict-1', 'raw-api-strict-2', 'installed-raw-api',
        'rank-strict-1', 'rank-strict-2', 'installed-rank', 'aggregate-audit',
        'installed-public', 'haskell-format']
evidence.mkdir()
for name in runs:
    shutil.copytree(area / name, evidence / name)
shutil.copytree(area / 'upstream', evidence / 'upstream')
for name in ['check.py', 'prepare-handoff.py', 'heavy-peaks']:
    shutil.copyfile(area / name, evidence / name)

sources = ['lean/MicroCFTA/' + module + '.lean' for module in [
    'SourceSizedDeterministic', 'SourceSizedDispatcher', 'SourceSizedPreprocessing',
    'SourceSizedFiniteKeysDispatchApi', 'SourceSizedFiniteKeysRankEvaluation',
    'SourceCurrentColdFiniteWarmCalls']]
sources += ['cfta-generator/src/Data/CFTA/Sized.hs', 'cfta-generator/CHANGELOG.md',
            'cfta-generator/test/Data/CFTA/SizedSpec.hs']
for relative in sources:
    destination = evidence / 'sources' / relative
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(root / relative, destination)

sha = lambda data: hashlib.sha256(data).hexdigest()
checks = {name: json.loads((evidence / name / 'report.json').read_text()) for name in runs}
expected_failures = {name for name in runs if name.endswith('strict-1')}
assert {name for name, check in checks.items() if check['exit_code']} == expected_failures
for name, check in checks.items():
    raw = (evidence / name / 'raw.log').read_bytes()
    assert len(raw) == check['bytes'] and sha(raw) == check['sha256']
    if 'strict-' in name:
        source = next((evidence / name / 'MicroCFTA').glob('*.lean'))
        assert sha(source.read_bytes()) == check['source_sha256']
        if name.endswith('strict-2'):
            assert source.read_bytes() == (root / 'lean/MicroCFTA' / source.name).read_bytes()
            assert not raw
native = (evidence / 'sized-native-1/raw.log').read_text()
assert native.count('+++ OK, passed 300 tests.') == 4
assert '11 examples, 0 failures' in native
assert '[45 of 45] Compiling Data.CFTA.Sized' in native
audit = (evidence / 'aggregate-audit/raw.log').read_text()
assert 'Checked axiom dependencies of 76607 MicroCFTA theorems.' in audit
public = (evidence / 'installed-public/raw.log').read_text()
assert public.count("depends on axioms:") == 14
assert public.count('does not depend on any axioms') == 1
assert '⋯' not in public and '...' not in public
unchanged = root / 'lean/MicroCFTA/SourceCurrentColdFiniteWarmCalls.lean'
old = subprocess.check_output(['git', 'show', 'a195d3bbb0efe52210933877771be816766765ee:' + str(unchanged.relative_to(root))], cwd=root)
assert old == unchanged.read_bytes()
summary = dict(checks=len(runs), rejected_strict_attempts=5, final_strict_passes=5,
               native_examples=11, property_cases=[300] * 4, audit_dependencies=76607,
               public_declarations=15, public_bytes=len(public.encode()),
               public_sha256=sha(public.encode()), h6_unchanged=True,
               source_sha256={relative: sha((root / relative).read_bytes()) for relative in sources})
(evidence / 'verification.json').write_text(json.dumps(summary, indent=2) + '\n')
manifest = {str(path.relative_to(evidence)): dict(bytes=path.stat().st_size, sha256=sha(path.read_bytes()))
            for path in sorted(evidence.rglob('*')) if path.is_file()}
(evidence / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps(dict(payloads=len(manifest), bytes=sum(item['bytes'] for item in manifest.values()),
                      manifest_sha256=sha((evidence / 'manifest.json').read_bytes()), verification=summary), indent=2))
