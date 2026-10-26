import hashlib
import json
import re
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-native-observed-words-20261026')
evidence = root / 'lean/restart-evidence/20261026-native-observed-words'
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
        code = re.sub(r'/-[\s\S]*?-/', '', data.decode())
        code = re.sub(r'--[^\n]*', '', code)
        assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b', code), module
for name, report in checks.items():
    raw = (area / name / 'raw.log').read_bytes()
    assert len(raw) == report['bytes'] and sha(raw) == report['sha256'], name
    if name.startswith(('helper-build-', 'aggregate-audit-', 'public-')):
        assert report['exit_code'] == 0, name
declarations = json.loads((area / 'public-declarations.json').read_text())
public_bytes = (area / 'public-final-1/raw.log').read_bytes()
public = public_bytes.decode()
assert len(re.findall(r'depends on axioms:|does not depend on any axioms', public)) == len(declarations) == 20
assert '⋯' not in public and '...' not in public
for axioms in re.findall(r'depends on axioms:\s*\[([^]]*)\]', public):
    assert set(re.findall(r'[A-Za-z_.]+', axioms)) <= {'propext', 'Classical.choice', 'Quot.sound'}
assert len(public.splitlines()) == 688 and len(public_bytes) == 48890
assert sha(public_bytes) == '624c44345ecc4d639131c823487ed768298f7c9924a8f50d0a4051724dffa883'
for name in ['strict-audit-1', 'aggregate-audit-1']:
    assert 'Checked axiom dependencies of 77138 MicroCFTA theorems.' in (area / name / 'raw.log').read_text()
expected_audit = old('lean/MicroCFTA/Audit.lean').decode().replace(
    'import MicroCFTA.SourcePruningEnumerationReceiptCallbackFuel\n',
    'import MicroCFTA.SourcePruningEnumerationReceiptCallbackFuel\n'
    'import MicroCFTA.SourceCurrentAllocatedTargetCallerObserved\n'
    'import MicroCFTA.SourceCurrentAllocatedNativeWordBoundary\n', 1)
assert (root / 'lean/MicroCFTA/Audit.lean').read_text() == expected_audit
assert set(git('diff', '--name-only', base, 'HEAD', '--', 'lean/MicroCFTA').decode().splitlines()) == set(source_paths)
assert not git('diff', '--name-only', base, '--', 'cfta', 'cfta-generator', 'specftacular', '*.cabal')
main = git('rev-parse', 'origin/main').decode().strip()
assert main == '153e1a211b56dd78bd22f6b427fb78e673041d55'
subprocess.run(['git', 'merge-base', '--is-ancestor', main, 'HEAD'], cwd=root, check=True)
unchanged = ['lean/MicroCFTA/' + module + '.lean' for module in [
    'SourcePruningEnumerationSelectedStep', 'SourcePruningEnumerationSelectedStepCompletion',
    'SourceCurrentAllocatedTargetQuery', 'SourceCurrentAllocatedTargetWorkerNative',
    'SourceCurrentAllocatedNativePhysicalTraceCompletion', 'SourceCurrentAllocatedNativePhysicalExecution',
    'SourceCurrentAllocatedNativeRequestBounds', 'SourceCurrentAllocatedRecursiveWarmInitialRanges',
    'SourceCurrentAllocatedNativeInventoryState', 'SourceCurrentAllocatedPartialInvariant',
    'SourcePruningEnumerationRecursivePacket', 'SourcePruningEnumerationRecursivePrefix',
    'SourcePruningEnumerationRecursiveCallback', 'SourcePruningEnumerationReceiptCallbackFuel',
    'SourcePruningEnumerationPrefixCompletion', 'SourcePruningEnumerationPrefixPacket',
    'SourcePruningEnumerationPreparedFuel', 'SourcePruningEnumerationPrefixHistory',
    'SourcePruningEnumerationNativeCacheGrowth', 'SourcePruningEnumerationReceiptCallback',
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
    older_completion_and_step_receipt_interfaces_unchanged=True,
    runtime_workers_unchanged=True,
    strongest_end_to_end_theorem_unchanged=True,
    haskell_unchanged=True,
    rich_trace_derives_its_actual_numeric_prefix_checks=True,
    certified_step_needs_no_separate_word_ranges=True,
    finite_target_receipt_derived_from_current_numeric_room=True,
    supplied_raw_return_matched_at_exact_value_and_checked_state=True,
    full_outer_caller_post_and_original_receipt_retained=True,
    positive_width_raw_done_without_checked_trace_proved=True,
    counterexample_has_ready_at_good_or_context_claim=False,
    generic_raw_success_to_checked_trace_proved=False,
    initial_only_recursive_capacity_proved=False,
    whole_subtree_preservation_proved=False,
    whole_driver_language_proved=False)
(area / 'source-boundaries.json').write_text(json.dumps(boundaries, indent=2) + '\n')
verification = dict(
    base=base, source_head=git('rev-parse', 'HEAD').decode().strip(), recorded_main=main,
    checks=checks, final_strict_modules=finals,
    failed_checks={name: report['exit_code'] for name, report in checks.items() if report['exit_code']},
    public_declarations=len(declarations), full_definitions=['Step', 'Trace'],
    public_lines=len(public.splitlines()), public_bytes=len(public_bytes), public_sha256=sha(public_bytes),
    audit_dependencies=77138,
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
    'A rich completed Trace records its own physical instruction inputs and therefore WordRanges.\n'
    'Step.verified_observed removes a redundant ranges argument from that rich Step, not raw success.\n'
    'Current numeric node/edge/domain room derives a complete target Receipt without future range admissions.\n'
    'Completed-run uniqueness identifies the supplied raw return at its exact value and complete checked state.\n'
    'The original full Receipt and all Context fields, effects, merge/fourth history and probes remain present.\n'
    'Width2 witness has actual raw done, closed available operand and valid physical tables, but no checked Trace.\n'
    'The witness makes no semantic Ready, At, full Good or caller Context claim and establishes no Haskell output defect.\n'
    'Future recursive capacity cannot be inferred from raw done or additional workFuel.\n'
    'Whole-subtree preservation and full recursive language remain open.\n'
    'H6 and all earlier executable sources stay unchanged.\n')
assert not evidence.exists()
shutil.copytree(area, evidence)
manifest = {str(p.relative_to(evidence)): dict(bytes=p.stat().st_size, sha256=sha(p.read_bytes()))
            for p in sorted(evidence.rglob('*')) if p.is_file()}
(evidence / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps(dict(
    checks=len(checks), strict=sum(name.startswith('strict-') for name in checks),
    failures=len(verification['failed_checks']), strict_final_modules=len(finals),
    public_declarations=len(declarations), audit_dependencies=77138,
    payloads=len(manifest), bytes=sum(info['bytes'] for info in manifest.values()),
    manifest_sha256=sha((evidence / 'manifest.json').read_bytes())), indent=2))
