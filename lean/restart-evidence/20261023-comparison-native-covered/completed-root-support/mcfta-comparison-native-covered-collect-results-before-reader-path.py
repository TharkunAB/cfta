import re
import runpy
import shutil
globals().update(runpy.run_path('/tmp/mcfta-comparison-native-covered-root-common.py'))

assert load(HERE / 'root-full-review.json')['complete_public_type_root_review'] == 'CLEAR'
jobs = {}
for path in sorted(HERE.glob('comparison-native-covered-*.json')):
    receipt = load(path)
    if not isinstance(receipt, dict) or 'wrapper' not in receipt or 'exit_code' not in receipt:
        continue
    assert Path(receipt['command'][0]).name in {'lean', 'lake'}
    raw = (HERE / receipt['log']).read_bytes()
    text = raw.decode()
    jobs[path.stem] = [receipt['exit_code'], receipt.get('sha256'), sha(HERE / receipt['log']),
        len(re.findall(r'^.+?:\d+:\d+: error(?:\([^)]*\))?:', text, re.M)),
        len(re.findall(r'^.+?:\d+:\d+: warning(?:\([^)]*\))?:', text, re.M))]
assert set(jobs) == {'comparison-native-covered-strict-1', 'comparison-native-covered-public-1', 'comparison-native-covered-audit-1'}
assert all(row[0] == 0 and row[3:] == [0, 0] for row in jobs.values())
audit = (HERE / 'comparison-native-covered-audit-1.log').read_text()
build = int(re.search(r'Build completed successfully \((\d+) jobs\)\.', audit).group(1))
dependencies = int(re.search(r'Checked axiom dependencies of (\d+) MicroCFTA theorems', audit).group(1))
assert build == 3645 and dependencies == 75508
metadata = {}
target = HERE / 'root-metadata-history'
target.mkdir()
for path in sorted(Path('/tmp').glob('mcfta-comparison-native-covered-*.json')):
    if not path.with_suffix('.limits.json').exists():
        continue
    receipt = load(path)
    assert 'wrapper' in receipt and Path(receipt['command'][0]).name not in {'lean', 'lake'}
    metadata['root-metadata-history/' + path.name] = receipt['exit_code']
    for suffix in ['.json', '.log', '.limits.json', '.usage.json', '.source.py', '.peaks.txt']:
        item = path.with_name(path.stem + suffix)
        assert item.is_file(), item
        shutil.copyfile(item, target / item.name)
assert len(metadata) == 14 and sum(code != 0 for code in metadata.values()) == 2
assert metadata['root-metadata-history/mcfta-comparison-native-covered-declaration-gate-1.json'] == 1
assert metadata['root-metadata-history/mcfta-comparison-native-covered-declaration-gate-2.json'] == 1
variant = 'source/' + NAME + '.lean'
artifacts = set()
for stem, row in jobs.items():
    artifacts.update(stem + suffix for suffix in ['.json', '.log', '.limits.json', '.usage.json'])
    if row[1]:
        artifacts.add(stem + '.source.lean')
for prefix in ['root-metadata-history', 'public-readback', 'signature-plan', 'source']:
    artifacts.update(str(path.relative_to(HERE)) for path in (HERE / prefix).rglob('*') if path.is_file())
artifacts.update(['selected-source-gate.json', 'root-full-review.json', 'root-declaration-review.json',
    'selected-sources.json', 'check-full-public.py', 'full-preparation/check-full-public.py',
    'public-audit/review.json', 'body-audit/review.json'])
artifacts.remove(variant)
history = dict(status='ROOT_ACCEPTED', selected_source_sha256=sha(HERE / variant),
    variants=[dict(path=variant, sha256=sha(HERE / variant), lines=204,
        reason='The original root-authored mathematical source. Strict, FULL and Audit pass unchanged on the first attempt.')],
    artifacts=[dict(path=path, bytes=(HERE / path).stat().st_size, sha256=sha(HERE / path)) for path in sorted(artifacts)],
    patches=[], rejected_public_types=[])
save('source-history-gate.json', history)
save('actual-result-data.json', dict(status='ROOT_RECORDED_ACTUAL_RESULTS', jobs=jobs, metadata_jobs=metadata,
    audit_build_jobs=build, audit_dependencies=dependencies, audit_log_sha256=sha(HERE / 'comparison-native-covered-audit-1.log'),
    mathematical_variants=1, lean_lake_failures=0, root_metadata_failures=2,
    root_metadata_cut='Fourteen completed capped root jobs through accept-full-1. Collection and later root jobs are outside this immutable cut.',
    history_artifacts=len(artifacts), new_haskell_repairs=0, whole_goal_complete=False))
print(json.dumps(dict(status='PASS', jobs=jobs, metadata_jobs=len(metadata), metadata_failures=2,
    variants=1, history_artifacts=len(artifacts), build=build, dependencies=dependencies)))
