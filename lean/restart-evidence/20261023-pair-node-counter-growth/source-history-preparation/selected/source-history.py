exec(compile(open('/tmp/mcfta-pair-node-counter-growth-root-common.py').read(), '/tmp/mcfta-pair-node-counter-growth-root-common.py', 'exec'))
import datetime
import re
import shutil

metadata = HERE / 'root-metadata-history'
metadata.mkdir()
metadata_jobs = {}
for path in sorted(Path('/tmp').glob('mcfta-pair-node-counter-growth-*.json')):
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
failures = [path for path, code in metadata_jobs.items() if code != 0]
save('root-metadata-history-cut.json', dict(status='COMPLETE_TERMINAL_METADATA_CUT_BEFORE_CLOSING_TOOLS',
    observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(), jobs=metadata_jobs, failed_jobs=len(failures),
    later_receipts='The one-time completed-root-support collection retains all closing receipts after this cut.'))
specs = {'root-pair-node-counter-growth-strict-1': ('strict', NAME), 'root-pair-node-counter-growth-full-1': ('full', NAME), 'root-pair-node-counter-growth-audit-1': ('audit', None)}
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
    jobs[stem] = dict(kind=kind, module=module, exit_code=receipt['exit_code'], source_sha256=receipt.get('sha256'),
        log_sha256=sha(HERE / receipt['log']),
        errors=len(re.findall(r'^.+?:\d+:\d+: error(?:\([^)]*\))?:', raw, re.M)),
        source_warnings=len(re.findall(r'^.+?:\d+:\d+: warning(?:\([^)]*\))?:', raw, re.M)))
    assert load(HERE / receipt['limits']) == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
    usage = load(HERE / (stem + '.usage.json'))
    assert 0 <= usage['age_seconds'] <= 600 and usage['remaining_percent'] > 1
assert (HERE / 'root-pair-node-counter-growth-strict-1.log').read_bytes() == b''
assert all(job['exit_code'] == job['errors'] == job['source_warnings'] == 0 for job in jobs.values())
save('job-history.json', jobs)
variant_path = 'variants/v1/' + NAME + '.lean'
source = HERE / variant_path
lines = len(source.read_bytes().splitlines())
assert lines == 96 and lines <= 160
variants = [dict(module=NAME, path=variant_path, sha256=sha(source), lines=lines,
    reason='The single reviewed body passed its first strict check and sole complete public-output check unchanged.')]
assert sha(source) == sha(HERE / (NAME + '.lean')) == load(HERE / 'selected-source-gate.json')['source_sha256']
assert load(HERE / 'selected-source-gate.json')['canonical_copy_deferred_to_reviewed_materializer']
excluded = {'source-history-gate.json', 'actual-proof-cut.json', 'archived-components.json', 'current-progress.md', variant_path}
artifacts = []
for path in sorted(HERE.rglob('*')):
    if path.is_file() and str(path.relative_to(HERE)) not in excluded:
        artifacts.append(dict(path=str(path.relative_to(HERE)), bytes=path.stat().st_size, sha256=sha(path)))
assert not {row['path'] for row in variants} & {row['path'] for row in artifacts}
selection = load(HERE / 'selected-sources.json')
save('source-history-gate.json', dict(status='ROOT_ACCEPTED', selected_sources={path: pin['sha256'] for path, pin in selection.items()},
    variants=variants, artifacts=artifacts, patches=[], rejected_public_types=[]))
raw = (HERE / 'root-pair-node-counter-growth-audit-1.log').read_text()
build = re.search(r'Build completed successfully \((\d+) jobs\)\.', raw)
dependencies = re.search(r'Checked axiom dependencies of (\d+) MicroCFTA theorems', raw)
assert build and dependencies
warnings = re.findall(r'(?m)^warning: .+$', raw)
assert len(warnings) == 1 and 'InternedFreshOrdinaryClosedCompletion.lean:24:5:' in warnings[0]
metrics = dict(actual_jobs=len(jobs), source_jobs=sum(job['kind'] in {'strict', 'full'} for job in jobs.values()),
    focused_build_jobs=sum(job['kind'] == 'focused_build' for job in jobs.values()), audit_jobs=sum(job['kind'] == 'audit' for job in jobs.values()),
    failed_jobs=sum(job['exit_code'] != 0 for job in jobs.values()),
    warned_source_exit_zero_jobs=sum(job['kind'] in {'strict', 'full'} and job['exit_code'] == 0 and job['source_warnings'] > 0 for job in jobs.values()),
    rejected_public_type_jobs=0)
save('actual-proof-cut.json', dict(status='ACTUAL_AUDIT_AND_HISTORY_BOUND', metrics=metrics,
    audit=dict(stem='root-pair-node-counter-growth-audit-1', build_jobs=int(build.group(1)), dependencies=int(dependencies.group(1)), log_sha256=sha(HERE / 'root-pair-node-counter-growth-audit-1.log'), warnings=warnings),
    metadata_jobs=len(metadata_jobs), failed_metadata_jobs=len(failures), metadata_failure_paths=failures,
    variants=len(variants), patches=0, artifacts=len(artifacts), source_history_sha256=sha(HERE / 'source-history-gate.json'),
    original_Audit_sha256=sha(HERE / 'original-sources/Audit.original.lean.txt')))
print(json.dumps(load(HERE / 'actual-proof-cut.json')))
