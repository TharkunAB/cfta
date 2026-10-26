import hashlib
import json
import re
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-native-uniform-prefix-20261026')
evidence = root / 'lean/restart-evidence/20261026-native-uniform-prefix'
base = (area / 'base.txt').read_text().strip()
sha = lambda data: hashlib.sha256(data).hexdigest()
git = lambda *args: subprocess.check_output(['git', *args], cwd=root)
old = lambda rel: git('show', base + ':' + rel)
checks = {p.parent.name: json.loads(p.read_text()) for p in sorted(area.glob('*/report.json'))}
finals = json.loads((area / 'final-strict.json').read_text())
source_paths = ['lean/MicroCFTA/' + module + '.lean' for module in finals]
for module, name in finals.items():
    rel = 'lean/MicroCFTA/' + module + '.lean'
    data = (root / rel).read_bytes()
    assert checks[name]['exit_code'] == 0 and checks[name]['source_sha256'] == sha(data), module
    assert (area / name / 'MicroCFTA' / (module + '.lean')).read_bytes() == data, module
    assert git('show', 'HEAD:' + rel) == data, rel
    if module != 'Audit':
        assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b', data.decode()), module
for name, report in checks.items():
    raw = (area / name / 'raw.log').read_bytes()
    assert len(raw) == report['bytes'] and sha(raw) == report['sha256'], name
    if name.startswith(('helper-build-', 'aggregate-audit-', 'public-')):
        assert report['exit_code'] == 0, name
declarations = json.loads((area / 'public-declarations.json').read_text())
public_bytes = (area / 'public-final-1/raw.log').read_bytes()
public = public_bytes.decode()
assert len(re.findall(r'depends on axioms:|does not depend on any axioms', public)) == len(declarations) == 19
assert '⋯' not in public and '...' not in public
for axioms in re.findall(r'depends on axioms:\s*\[([^]]*)\]', public):
    assert set(re.findall(r'[A-Za-z_.]+', axioms)) <= {'propext', 'Classical.choice', 'Quot.sound'}
assert len(public.splitlines()) == 1573 and len(public_bytes) == 129307
assert sha(public_bytes) == '6a4a374c6baf69290b4bbcc40c6f7a2e58c5f304e8967a56b4f70d9d5e221122'
for name in ['strict-audit-1', 'aggregate-audit-1']:
    assert 'Checked axiom dependencies of 77073 MicroCFTA theorems.' in (area / name / 'raw.log').read_text()
expected_audit = old('lean/MicroCFTA/Audit.lean').decode().replace(
    'import MicroCFTA.SourcePruningEnumerationRecursiveEquations\n',
    'import MicroCFTA.SourcePruningEnumerationRecursiveEquations\n'
    'import MicroCFTA.SourcePruningEnumerationPrefixPacket\n'
    'import MicroCFTA.SourcePruningEnumerationNativeCacheGrowth\n', 1)
assert (root / 'lean/MicroCFTA/Audit.lean').read_text() == expected_audit
assert set(git('diff', '--name-only', base, 'HEAD', '--', 'lean/MicroCFTA').decode().splitlines()) == set(source_paths)
assert not git('diff', '--name-only', base, '--', 'cfta', 'cfta-generator', 'specftacular', '*.cabal')
main = git('rev-parse', 'origin/main').decode().strip()
assert main == '153e1a211b56dd78bd22f6b427fb78e673041d55'
subprocess.run(['git', 'merge-base', '--is-ancestor', main, 'HEAD'], cwd=root, check=True)
unchanged = ['lean/MicroCFTA/' + module + '.lean' for module in [
    'SourcePruningEnumerationSelectedStep', 'SourcePruningEnumerationSelectedStepCompletion',
    'SourcePruningEnumerationSelectedOrdinary', 'SourcePruningEnumerationNativeOrdinary',
    'SourcePruningEnumerationNativeContinuations', 'SourcePruningEnumerationNativeOrdinaryContinuations',
    'SourcePruningEnumerationNativeBranchCompletion', 'SourcePruningEnumerationRecursive',
    'SourcePruningEnumerationRecursiveEquations', 'SourcePruningEnumerationCapturedEdge',
    'SourcePruningCallbackCompletion', 'SourcePruningRecordTypes',
    'SourcePruningEnumerationNativeIndex', 'SourcePruningEnumerationRestart',
    'EnumerationCompressionFrame', 'EnumerationPendingOrder', 'EnumerationOrder',
    'SourceCurrentColdFiniteWarmCalls']]
unchanged += ['cfta/src/Data/CFTA/' + name for name in [
    'Enumeration.hs', 'Interned/Type.hs', 'Interned/Cache.hs', 'Interned/Memo.hs', 'Interned/Operations.hs']]
for rel in unchanged:
    assert old(rel) == (root / rel).read_bytes(), rel
boundaries = dict(
    existing_lean_change_is_exactly_two_audit_imports=True,
    older_valid_and_all_completion_interfaces_unchanged=True,
    runtime_workers_unchanged=True,
    strongest_end_to_end_theorem_unchanged=True,
    haskell_unchanged=True,
    common_prefix_fuel_derived_from_initial_inputs=True,
    whole_result_equality_across_fuels_claimed=False,
    full_conditional_ordinary_capability_retained=True,
    captured_cache_transport_keeps_same_cached_value=True,
    recursive_packet_preservation_proved=False,
    initial_only_recursive_capacity_proved=False,
    whole_driver_language_proved=False)
(area / 'source-boundaries.json').write_text(json.dumps(boundaries, indent=2) + '\n')
verification = dict(
    base=base, source_head=git('rev-parse', 'HEAD').decode().strip(), recorded_main=main,
    checks=checks, final_strict_modules=finals,
    failed_checks={name: report['exit_code'] for name, report in checks.items() if report['exit_code']},
    public_declarations=len(declarations), full_definitions=['PrefixValid', 'Valid'],
    public_lines=len(public.splitlines()), public_bytes=len(public_bytes), public_sha256=sha(public_bytes),
    audit_dependencies=77073,
    final_source_sha256={rel: sha((root / rel).read_bytes()) for rel in source_paths},
    unchanged_source_sha256={rel: sha((root / rel).read_bytes()) for rel in unchanged},
    boundaries=boundaries, goal_status='active')
(area / 'verification.json').write_text(json.dumps(verification, indent=2) + '\n')
(area / 'proof-change.patch').write_bytes(git('diff', base, 'HEAD', '--', *source_paths))
for rel in source_paths:
    target = area / 'sources' / rel
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes((root / rel).read_bytes())
target = area / 'original-sources/lean/MicroCFTA/Audit.lean'
target.parent.mkdir(parents=True, exist_ok=True)
target.write_bytes(old('lean/MicroCFTA/Audit.lean'))
(area / 'verification-review.txt').write_text(
    'Initial Context, Safe, PendingReferences, CacheValid and actual restart expansion derive common prefix fuel.\n'
    'The entire old Valid and its conditional ordinary capability remain present.\n'
    'Larger representative fuel retains exact execution on the actual checked core, not global action equality.\n'
    'Prefix projections use the same actual native and enumeration observations.\n'
    'Native Post transports validity of the same captured enumeration cache.\n'
    'No safety theorem follows from Frame alone.\n'
    'Legacy ordinary Ranges does not certify hook-aware sibling endpoints.\n'
    'Recursive completion, initial-only capacity and whole-driver language remain open.\n'
    'H6 and all earlier executable sources stay unchanged.\n')
assert not evidence.exists()
shutil.copytree(area, evidence)
manifest = {str(p.relative_to(evidence)): dict(bytes=p.stat().st_size, sha256=sha(p.read_bytes()))
            for p in sorted(evidence.rglob('*')) if p.is_file()}
(evidence / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps(dict(
    checks=len(checks), strict=sum(name.startswith('strict-') for name in checks),
    failures=len(verification['failed_checks']), strict_final_modules=len(finals),
    public_declarations=len(declarations), audit_dependencies=77073,
    payloads=len(manifest), bytes=sum(info['bytes'] for info in manifest.values()),
    manifest_sha256=sha((evidence / 'manifest.json').read_bytes())), indent=2))
