exec(compile(open('/tmp/mcfta-rebuild-admission-root-common.py').read(), '/tmp/mcfta-rebuild-admission-root-common.py', 'exec'))
import datetime
import re
import shutil
metadata = HERE / 'root-metadata-history'
assert not metadata.exists()
metadata.mkdir()
metadata_jobs = {}
for path in sorted(Path('/tmp').glob('mcfta-rebuild-admission-*.json')):
    item = load(path)
    if not isinstance(item, dict) or 'wrapper' not in item or 'exit_code' not in item:
        continue
    assert Path(item['command'][0]).name not in {'lean', 'lake'}
    for suffix in ['.json', '.log', '.limits.json', '.usage.json', '.source.py', '.peaks.txt']:
        original = path.with_name(path.stem + suffix)
        assert original.is_file(), original
        shutil.copy2(original, metadata / original.name)
        assert sha(original) == sha(metadata / original.name)
    metadata_jobs['root-metadata-history/' + path.name] = item['exit_code']
assert metadata_jobs and not any(metadata_jobs.values())
save('root-metadata-history-cut.json', dict(status='COMPLETE_TERMINAL_METADATA_CUT_BEFORE_CLOSING_TOOLS',
    observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(), jobs=metadata_jobs, failed_jobs=0,
    later_receipts='The final one-time completed-root-support collection retains closing receipts after this cut.'))
specs = {'strict1':('strict', NAME), 'FULL1':('full', NAME), 'audit1':('audit', None)}
actual = {}
for path in HERE.glob('*.json'):
    item = load(path)
    if isinstance(item, dict) and 'wrapper' in item and 'exit_code' in item and Path(item['command'][0]).name in {'lean', 'lake'}:
        actual[path.stem] = item
assert set(actual) == set(specs)
jobs = {}
for stem, (kind, module) in specs.items():
    receipt = actual[stem]
    raw = (HERE / receipt['log']).read_text()
    assert receipt['exit_code'] == 0
    jobs[stem] = dict(kind=kind, module=module, exit_code=receipt['exit_code'], source_sha256=receipt.get('sha256'),
        log_sha256=sha(HERE / receipt['log']),
        errors=len(re.findall(r'^.+?:\d+:\d+: error(?:\([^)]*\))?:', raw, re.M)),
        source_warnings=len(re.findall(r'^.+?:\d+:\d+: warning(?:\([^)]*\))?:', raw, re.M)))
    assert load(HERE / receipt['limits']) == {'memory.max':'4294967296', 'memory.high':'4294967296', 'memory.swap.max':'0'}
    usage = load(HERE / (stem + '.usage.json'))
    assert 0 <= usage['age_seconds'] <= 600 and usage['remaining_percent'] > 1
assert (HERE / 'strict1.log').read_bytes() == b''
save('job-history.json', jobs)
variant_path = 'source-v1/' + NAME + '.lean'
variant = HERE / variant_path
assert sha(variant) == sha(HERE / (NAME + '.lean')) == '355224ff767c10856684db24c0d6393e61c63a6754ae6044bb64ba29b0ca61e7'
assert len(variant.read_bytes().splitlines()) == 90
variants = [dict(module=NAME, path=variant_path, sha256=sha(variant), lines=90,
    reason='Original independently reviewed literal rebuild certificate body. The first strict and sole FULL checks passed without source changes.')]
excluded = {'source-history-gate.json', 'archived-components.json', 'current-progress.md', variant_path}
artifacts = []
for path in sorted(HERE.rglob('*')):
    if not path.is_file():
        continue
    relative = str(path.relative_to(HERE))
    if relative not in excluded:
        artifacts.append(dict(path=relative, bytes=path.stat().st_size, sha256=sha(path)))
assert not {item['path'] for item in variants} & {item['path'] for item in artifacts}
selection = load(HERE / 'selected-sources.json')
save('source-history-gate.json', dict(status='ROOT_ACCEPTED',
    selected_sources={path:record['sha256'] for path, record in selection.items()},
    variants=variants, artifacts=artifacts, patches=[], rejected_public_types=[]))
audit_raw = (HERE / 'audit1.log').read_text()
build = re.search(r'Build completed successfully \((\d+) jobs\)\.', audit_raw)
dependencies = re.search(r'Checked axiom dependencies of (\d+) MicroCFTA theorems', audit_raw)
assert build and dependencies and (int(build.group(1)), int(dependencies.group(1))) == (3650, 75527)
warnings = re.findall(r'(?m)^warning: .+$', audit_raw)
assert len(warnings) == 1 and 'InternedFreshOrdinaryClosedCompletion.lean:24:5:' in warnings[0]
metrics = dict(actual_jobs=len(jobs), source_jobs=sum(item['kind'] in {'strict', 'full'} for item in jobs.values()),
    focused_build_jobs=0, audit_jobs=1, failed_jobs=sum(item['exit_code'] != 0 for item in jobs.values()),
    warned_source_exit_zero_jobs=sum(item['exit_code'] == 0 and item['kind'] in {'strict', 'full'} and item['source_warnings'] > 0 for item in jobs.values()),
    rejected_public_type_jobs=0)
save('actual-proof-cut.json', dict(status='ACTUAL_AUDIT_AND_HISTORY_BOUND', metrics=metrics,
    audit=dict(stem='audit1', build_jobs=int(build.group(1)), dependencies=int(dependencies.group(1)),
        log_sha256=sha(HERE / 'audit1.log'), warnings=warnings),
    metadata_jobs=len(metadata_jobs), failed_metadata_jobs=0, variants=1, patches=0, artifacts=len(artifacts),
    source_history_sha256=sha(HERE / 'source-history-gate.json'),
    original_Audit_sha256=sha(HERE / 'original-sources/Audit.original.lean.txt')))
print(json.dumps(load(HERE / 'actual-proof-cut.json')))
